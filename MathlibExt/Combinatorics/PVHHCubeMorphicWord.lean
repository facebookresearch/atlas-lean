/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# An additive-cube-free morphic word

The Cassaigne–Currie–Schaeffer–Shallit substitution generates an infinite word with no
additive cubes (`conjecture_holds`). The proof uses Parikh-vector differences and the
substitution graph from Sections 2–4 of the cited paper, with exact integer bounds.
-/

namespace MathlibExt.Combinatorics.PVHHCubeMorphicWordWanted

@[expose] public section

/-- **The alphabet $\{0, 1, 3, 4\}$.** The alphabet with four distinct letters, written $0$, $1$,
$3$ and $4$. -/
inductive Letter where
  | zero
  | one
  | three
  | four
  deriving DecidableEq

/-- **The substitution $0 \mapsto 03$, $1 \mapsto 43$, $3 \mapsto 1$, $4 \mapsto 01$.** The map
sending each letter of the alphabet $\{0, 1, 3, 4\}$ to a word: $0$ to $03$, $1$ to $43$, $3$ to
$1$ and $4$ to $01$. -/
def substitution : Letter → List Letter
  | .zero => [.zero, .three]
  | .one => [.four, .three]
  | .three => [.one]
  | .four => [.zero, .one]

/-- **Iterates of the substitution on $0$.** For $k \ge 0$, the word $\sigma^k(0)$ obtained from
the one-letter word $0$ by applying the substitution $\sigma$ ($0 \mapsto 03$, $1 \mapsto 43$,
$3 \mapsto 1$, $4 \mapsto 01$) $k$ times, where $\sigma$ acts on a word by replacing each letter
with its image: $\sigma^0(0) = 0$ and $\sigma^{k+1}(0) = \sigma(\sigma^k(0))$. -/
def substitutionIterate : ℕ → List Letter
  | 0 => [.zero]
  | k + 1 => (substitutionIterate k).flatMap substitution

/-- **The fixed point generated from $0$.** Let $\sigma$ be the substitution $0 \mapsto 03$,
$1 \mapsto 43$, $3 \mapsto 1$, $4 \mapsto 01$ on the alphabet $\{0, 1, 3, 4\}$, extended to words
by replacing each letter with its image. An infinite word $w = w_0 w_1 w_2 \cdots$ over
$\{0, 1, 3, 4\}$ is the fixed point generated from $0$ if the word $\sigma^k(0)$ is a prefix of $w$
for every $k \ge 0$. -/
def IsGeneratedFixedPoint (w : ℕ → Letter) : Prop :=
  ∀ k i (hi : i < (substitutionIterate k).length),
    w i = (substitutionIterate k).get ⟨i, hi⟩

/-- **Value of a letter.** Each letter of the alphabet $\{0, 1, 3, 4\}$ has as its value the
integer it names: the letters $0$, $1$, $3$ and $4$ have values $0$, $1$, $3$ and $4$. -/
def letterValue : Letter → ℤ
  | .zero => 0
  | .one => 1
  | .three => 3
  | .four => 4

/-- **Sum of a factor.** For an infinite word $w = w_0 w_1 w_2 \cdots$ over the alphabet
$\{0, 1, 3, 4\}$ and natural numbers $s$ and $\ell$, the sum of the factor of length $\ell$
starting at position $s$ is the integer $\sum_{i=0}^{\ell-1} w_{s+i}$, where each letter counts
as its value. -/
def factorSum (w : ℕ → Letter) (start length : ℕ) : ℤ :=
  (Finset.range length).sum fun i ↦ letterValue (w (start + i))

/-- **Avoiding additive cubes.** An infinite word $w = w_0 w_1 w_2 \cdots$ over the alphabet
$\{0, 1, 3, 4\}$ avoids PVHH-cubes (additive cubes) if there are no natural numbers $s$ and
$\ell \ge 1$ such that the three consecutive factors $w_s \cdots w_{s+\ell-1}$,
$w_{s+\ell} \cdots w_{s+2\ell-1}$ and $w_{s+2\ell} \cdots w_{s+3\ell-1}$ of length $\ell$ all have
the same sum of letter values. -/
def AvoidsPVHHCubes (w : ℕ → Letter) : Prop :=
  ∀ start length, 0 < length →
    ¬(factorSum w start length = factorSum w (start + length) length ∧
      factorSum w (start + length) length = factorSum w (start + 2 * length) length)

/-- **Additive-cube-free fixed point conjecture.** Let $\sigma$ be the substitution
$0 \mapsto 03$, $1 \mapsto 43$, $3 \mapsto 1$, $4 \mapsto 01$ on the alphabet $\{0, 1, 3, 4\}$,
extended to words by replacing each letter with its image. The proposition that there is an
infinite word $w$ over $\{0, 1, 3, 4\}$ such that $\sigma^k(0)$ is a prefix of $w$ for every
$k \ge 0$ and $w$ avoids PVHH-cubes (additive cubes): no three consecutive nonempty factors of $w$
of equal length have equal sums of letter values. -/
def conjecture : Prop :=
  ∃ w : ℕ → Letter, IsGeneratedFixedPoint w ∧ AvoidsPVHHCubes w

end

/-! ## Difference vectors and transitions -/

private structure Vec where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq

private def zero : Vec := ⟨0, 0, 0, 0⟩

private def plus (x y : Vec) : Vec :=
  ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩

private def minus (x y : Vec) : Vec :=
  ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩

-- An adjacent-block difference uses the middle boundary twice.
private def difference (a b c d : Vec) : Vec := plus (minus a b) (minus d c)

private def dot (r x : Vec) : ℤ := r.a * x.a + r.b * x.b + r.c * x.c + r.d * x.d

private def incidence (x : Vec) : Vec := ⟨x.a + x.d, x.c + x.d, x.a + x.b, x.b⟩

private def inverse (x : Vec) : Vec :=
  ⟨x.c - x.d, x.d, x.b - x.a + x.c - x.d, x.a - x.c + x.d⟩

private def pull (r : Vec) : Vec := ⟨r.a + r.c, r.c + r.d, r.b, r.a + r.b⟩

private theorem dot_incidence (r x : Vec) : dot r (incidence x) = dot (pull r) x := by
  simp only [dot, incidence, pull]
  ring

private theorem dot_difference (r a b c d : Vec) :
    dot r (difference a b c d) = dot r a - dot r b - dot r c + dot r d := by
  simp only [dot, difference, plus, minus]
  ring

private theorem dot_plus (r x y : Vec) : dot r (plus x y) = dot r x + dot r y := by
  simp only [dot, plus]
  ring

private def unit : Letter → Vec
  | .zero => ⟨1, 0, 0, 0⟩
  | .one => ⟨0, 1, 0, 0⟩
  | .three => ⟨0, 0, 1, 0⟩
  | .four => ⟨0, 0, 0, 1⟩

private def lengthRow : Vec := ⟨1, 1, 1, 1⟩

private def sumRow : Vec := ⟨0, 1, 3, 4⟩

private def lattice (x : Vec) : Prop := dot lengthRow x = 0 ∧ dot sumRow x = 0

private def digit (d : Vec) : Prop := d = zero ∨ d = unit .zero ∨ d = unit .four

private def predecessors : Letter → List (Letter × Vec)
  | .zero => [(.zero, zero), (.four, zero)]
  | .one => [(.three, zero), (.four, unit .zero)]
  | .three => [(.zero, unit .zero), (.one, unit .four)]
  | .four => [(.one, zero)]

private theorem predecessor_digit {a b : Letter} {d : Vec}
    (h : (a, d) ∈ predecessors b) : digit d := by
  cases b <;> simp_all [predecessors, digit, Prod.mk.injEq] <;> grind

private structure Boundary where
  a : Letter
  b : Letter
  c : Letter
  d : Letter
  deriving DecidableEq

private structure State where
  letters : Boundary
  u : Vec
  v : Vec
  deriving DecidableEq

private def root : State := ⟨⟨.zero, .zero, .zero, .zero⟩, zero, zero⟩

private def diagonal (s : State) : Prop :=
  s.letters.a = s.letters.b ∧ s.letters.b = s.letters.c ∧ s.letters.c = s.letters.d ∧
    s.u = zero ∧ s.v = zero
  deriving Decidable

private def Step (p q : State) : Prop :=
  ∃ a b c d : Vec,
    (p.letters.a, a) ∈ predecessors q.letters.a ∧
    (p.letters.b, b) ∈ predecessors q.letters.b ∧
    (p.letters.c, c) ∈ predecessors q.letters.c ∧
    (p.letters.d, d) ∈ predecessors q.letters.d ∧
    q.u = plus (incidence p.u) (difference a b b c) ∧
    q.v = plus (incidence p.v) (difference b c c d)

private theorem step_root : Step root root := by
  exact ⟨zero, zero, zero, zero, by simp [root, predecessors], by simp [root, predecessors],
    by simp [root, predecessors], by simp [root, predecessors], rfl, rfl⟩

private theorem step_add {p q : State} {a b c d : Vec}
    (hu : q.u = plus (incidence p.u) (difference a b b c))
    (hv : q.v = plus (incidence p.v) (difference b c c d)) :
    plus q.u q.v = plus (incidence (plus p.u p.v)) (difference a b c d) := by
  rw [hu, hv]
  simp only [plus, difference, minus, incidence, Vec.mk.injEq]
  exact ⟨by ring, by ring, by ring, by ring⟩

private def previous (s : State) : List State := do
  let (a, x) ← predecessors s.letters.a
  let (b, y) ← predecessors s.letters.b
  let (c, z) ← predecessors s.letters.c
  let (d, w) ← predecessors s.letters.d
  return ⟨⟨a, b, c, d⟩,
    inverse (minus s.u (difference x y y z)), inverse (minus s.v (difference y z z w))⟩

private theorem inverse_add (x y : Vec) : inverse (minus (plus (incidence x) y) y) = x := by
  cases x with
  | mk a b c d =>
    simp only [inverse, minus, plus, incidence, Vec.mk.injEq]
    exact ⟨by ring, by ring, by ring, by ring⟩

private theorem mem_previous {p q : State} (h : Step p q) : p ∈ previous q := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hu, hv⟩ := h
  simp only [previous, List.bind_eq_flatMap, List.mem_flatMap, List.pure_def, List.mem_singleton]
  refine ⟨_, ha, _, hb, _, hc, _, hd, ?_⟩
  dsimp
  rw [hu, hv, inverse_add, inverse_add]

/-! ## Integer bounds on ancestral differences -/

-- These rows are integer approximations, scaled by 10^6, to the real and complex projections
-- in Section 2.1 of the paper. The checked integer inequalities below suffice for the argument.
private def pRow : Vec := ⟨512400, 597857, 353702, 656846⟩
private def qRow : Vec := ⟨180600, 680916, -452415, -572410⟩
private def rRow : Vec := ⟨578800, -321935, -69024, -166151⟩
private def sRow : Vec := ⟨-574900, 218273, 616526, -681027⟩

private def controlled (H : ℤ) (x : Vec) : Prop :=
  -H ≤ dot pRow x ∧ dot pRow x ≤ H ∧ -H ≤ dot qRow x ∧ dot qRow x ≤ H ∧
  -H ≤ 2 * dot rRow x ∧ 2 * dot rRow x ≤ H ∧ -H ≤ 2 * dot sRow x ∧ 2 * dot sRow x ≤ H

private def coordsBound (H : ℤ) (x : Vec) : Prop :=
  -H ≤ x.a ∧ x.a ≤ H ∧ -H ≤ x.b ∧ x.b ≤ H ∧
  -H ≤ x.c ∧ x.c ≤ H ∧ -H ≤ x.d ∧ x.d ≤ H

private theorem controlled_coords {H : ℤ} {x : Vec} (h : controlled H x) :
    coordsBound (3 * H / 1000000) x := by
  obtain ⟨hp₁, hp₂, hq₁, hq₂, hr₁, hr₂, hs₁, hs₂⟩ := h
  simp only [dot, pRow, qRow, rRow, sRow] at *
  simp only [coordsBound]
  have hab : -3 * H ≤ 1000000 * x.a ∧ 1000000 * x.a ≤ 3 * H := by
    constructor <;> linarith
  have hbb : -3 * H ≤ 1000000 * x.b ∧ 1000000 * x.b ≤ 3 * H := by
    constructor <;> linarith
  have hcb : -3 * H ≤ 1000000 * x.c ∧ 1000000 * x.c ≤ 3 * H := by
    constructor <;> linarith
  have hdb : -3 * H ≤ 1000000 * x.d ∧ 1000000 * x.d ≤ 3 * H := by
    constructor <;> linarith
  omega

private theorem lattice_controls_real {H : ℤ} {x : Vec}
    (hl : lattice x) (h : controlled H x) (hH : 1 ≤ H) :
    -(H - 1) ≤ dot pRow x ∧ dot pRow x ≤ H - 1 ∧
    -(H - 1) ≤ dot qRow x ∧ dot qRow x ≤ H - 1 := by
  obtain ⟨hl, hs⟩ := hl
  obtain ⟨_, _, _, _, hr₁, hr₂, hs₁, hs₂⟩ := h
  simp only [dot, lengthRow, sumRow, rRow, sRow] at hl hs hr₁ hr₂ hs₁ hs₂
  have hpLower : -3 * H ≤ 4 * dot pRow x := by
    simp only [dot, pRow]
    linarith
  have hpUpper : 4 * dot pRow x ≤ 3 * H := by
    simp only [dot, pRow]
    linarith
  have hqLower : -3 * H ≤ 4 * dot qRow x := by
    simp only [dot, qRow]
    linarith
  have hqUpper : 4 * dot qRow x ≤ 3 * H := by
    simp only [dot, qRow]
    linarith
  exact ⟨by omega, by omega, by omega, by omega⟩

private def Perturbation (x : Vec) : Prop :=
  ∃ a b c d, digit a ∧ digit b ∧ digit c ∧ digit d ∧ x = difference a b c d

private theorem digit_range {r d : Vec} {lo hi : ℤ} (hd : digit d)
    (hlo : lo ≤ 0 ∧ lo ≤ r.a ∧ lo ≤ r.d) (hhi : 0 ≤ hi ∧ r.a ≤ hi ∧ r.d ≤ hi) :
    lo ≤ dot r d ∧ dot r d ≤ hi := by
  rcases hd with rfl | rfl | rfl
  · simpa [dot, zero] using And.intro hlo.1 hhi.1
  · simpa [dot, unit] using And.intro hlo.2.1 hhi.2.1
  · simpa [dot, unit] using And.intro hlo.2.2 hhi.2.2

private theorem perturbation_range {r x : Vec} {lo hi : ℤ} (hx : Perturbation x)
    (hlo : lo ≤ 0 ∧ lo ≤ r.a ∧ lo ≤ r.d) (hhi : 0 ≤ hi ∧ r.a ≤ hi ∧ r.d ≤ hi) :
    -2 * (hi - lo) ≤ dot r x ∧ dot r x ≤ 2 * (hi - lo) := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := hx
  rw [dot_difference]
  obtain ⟨ha₁, ha₂⟩ := digit_range ha hlo hhi
  obtain ⟨hb₁, hb₂⟩ := digit_range hb hlo hhi
  obtain ⟨hc₁, hc₂⟩ := digit_range hc hlo hhi
  obtain ⟨hd₁, hd₂⟩ := digit_range hd hlo hhi
  omega

-- The two expanding rows contract when we traverse a step toward the root.
private theorem expanding_bound {H : ℤ} {x y d : Vec} (hx : controlled H x)
    (hy : controlled H y) (hd : Perturbation d) (hstep : y = plus (incidence x) d)
    (hH : 10000000 < H) :
    -(H - 1) ≤ dot pRow x ∧ dot pRow x ≤ H - 1 ∧
    -(H - 1) ≤ dot qRow x ∧ dot qRow x ≤ H - 1 := by
  obtain ⟨ha₁, ha₂, hb₁, hb₂, hc₁, hc₂, hd₁, hd₂⟩ := controlled_coords hx
  obtain ⟨hp₁, hp₂, hq₁, hq₂, _⟩ := hy
  obtain ⟨dp₁, dp₂⟩ := perturbation_range (r := pRow) (lo := 0) (hi := 656846)
    hd (by decide) (by decide)
  obtain ⟨dq₁, dq₂⟩ := perturbation_range (r := qRow) (lo := -572410) (hi := 180600)
    hd (by decide) (by decide)
  rw [hstep, dot_plus, dot_incidence] at hp₁ hp₂ hq₁ hq₂
  let C := 3 * H / 1000000
  have hC : 1000000 * C ≤ 3 * H := by dsimp [C]; omega
  change -C ≤ x.a at ha₁
  change x.a ≤ C at ha₂
  change -C ≤ x.b at hb₁
  change x.b ≤ C at hb₂
  change -C ≤ x.c at hc₁
  change x.c ≤ C at hc₂
  change -C ≤ x.d at hd₁
  change x.d ≤ C at hd₂
  have hp :
      -610000 * C ≤ 1000 * dot (pull pRow) x - 1690 * dot pRow x ∧
      1000 * dot (pull pRow) x - 1690 * dot pRow x ≤ 610000 * C := by
    simp only [dot, pull, pRow]
    constructor <;> linarith only [ha₁, ha₂, hb₁, hb₂, hc₁, hc₂, hd₁, hd₂]
  have hq :
      -610000 * C ≤ 1000 * dot (pull qRow) x + 1505 * dot qRow x ∧
      1000 * dot (pull qRow) x + 1505 * dot qRow x ≤ 610000 * C := by
    simp only [dot, pull, qRow]
    constructor <;> linarith only [ha₁, ha₂, hb₁, hb₂, hc₁, hc₂, hd₁, hd₂]
  obtain ⟨hp₃, hp₄⟩ := hp
  obtain ⟨hq₃, hq₄⟩ := hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith only [hH, hC, dp₂, hp₁, hp₄]
  · linarith only [hH, hC, dp₁, hp₂, hp₃]
  · linarith only [hH, hC, dq₁, hq₂, hq₃]
  · linarith only [hH, hC, dq₂, hq₁, hq₄]

-- The remaining two rows contract jointly after two steps from the root.
private theorem contracting_bound {H : ℤ} {x y z d e : Vec} (hx : controlled H x)
    (hd : Perturbation d) (he : Perturbation e)
    (hy : y = plus (incidence x) d) (hz : z = plus (incidence y) e)
    (hH : 10000000 < H) :
    -(H - 1) ≤ 2 * dot rRow z ∧ 2 * dot rRow z ≤ H - 1 ∧
    -(H - 1) ≤ 2 * dot sRow z ∧ 2 * dot sRow z ≤ H - 1 := by
  obtain ⟨ha₁, ha₂, hb₁, hb₂, hc₁, hc₂, hd₁, hd₂⟩ := controlled_coords hx
  obtain ⟨_, _, _, _, hr₁, hr₂, hs₁, hs₂⟩ := hx
  obtain ⟨er₁, er₂⟩ := perturbation_range (r := rRow) (lo := -166151) (hi := 578800)
    he (by decide) (by decide)
  obtain ⟨es₁, es₂⟩ := perturbation_range (r := sRow) (lo := -681027) (hi := 0)
    he (by decide) (by decide)
  obtain ⟨dr₁, dr₂⟩ := perturbation_range (r := pull rRow) (lo := 0) (hi := 509776)
    hd (by decide) (by decide)
  obtain ⟨ds₁, ds₂⟩ := perturbation_range (r := pull sRow) (lo := -356627) (hi := 41626)
    hd (by decide) (by decide)
  let C := 3 * H / 1000000
  have hC : 1000000 * C ≤ 3 * H := by dsimp [C]; omega
  change -C ≤ x.a at ha₁
  change x.a ≤ C at ha₂
  change -C ≤ x.b at hb₁
  change x.b ≤ C at hb₂
  change -C ≤ x.c at hc₁
  change x.c ≤ C at hc₂
  change -C ≤ x.d at hd₁
  change x.d ≤ C at hd₂
  have hr :
      -550000 * C ≤ 1000 * dot (pull (pull rRow)) x + 61 * dot rRow x + 388 * dot sRow x ∧
      1000 * dot (pull (pull rRow)) x + 61 * dot rRow x + 388 * dot sRow x ≤ 550000 * C := by
    simp only [dot, pull, rRow, sRow]
    constructor <;> linarith only [ha₁, ha₂, hb₁, hb₂, hc₁, hc₂, hd₁, hd₂]
  have hs :
      -550000 * C ≤ 1000 * dot (pull (pull sRow)) x - 388 * dot rRow x + 61 * dot sRow x ∧
      1000 * dot (pull (pull sRow)) x - 388 * dot rRow x + 61 * dot sRow x ≤ 550000 * C := by
    simp only [dot, pull, rRow, sRow]
    constructor <;> linarith only [ha₁, ha₂, hb₁, hb₂, hc₁, hc₂, hd₁, hd₂]
  obtain ⟨hr₃, hr₄⟩ := hr
  obtain ⟨hs₃, hs₄⟩ := hs
  simp only [hz, hy, dot_plus, dot_incidence]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith only [hH, hC, hr₃, hr₂, hs₂, dr₁, er₁]
  · linarith only [hH, hC, hr₄, hr₁, hs₁, dr₂, er₂]
  · linarith only [hH, hC, hs₃, hr₁, hs₂, ds₁, es₁]
  · linarith only [hH, hC, hs₄, hr₂, hs₁, ds₂, es₂]

private def Admissible (x : ℕ → Vec) : Prop :=
  (∃ n, ∀ i, n ≤ i → x i = zero) ∧ lattice (x 0) ∧
    ∀ i, ∃ d, Perturbation d ∧ x i = plus (incidence (x (i + 1))) d

-- For the least common bound on the padded sequence, a bound above 10^7 could be lowered:
-- use the expanding inequalities toward the cube and the contracting ones toward the root.
private theorem bounded_of_admissible {x : ℕ → Vec} (hx : Admissible x) (i : ℕ) :
    controlled 10000000 (x i) := by
  classical
  obtain ⟨⟨n, hn⟩, hl, hstep⟩ := hx
  have mono {a b : ℤ} {x : Vec} (hab : a ≤ b) (h : controlled a x) :
      controlled b x := by
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := h
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hfinite : ∀ k, ∃ H : ℕ, ∀ j ≤ k, controlled (H : ℤ) (x j) := by
    have pointwise (j : ℕ) : ∃ H : ℕ, controlled (H : ℤ) (x j) := by
      refine ⟨(dot pRow (x j)).natAbs + (dot qRow (x j)).natAbs +
        (2 * dot rRow (x j)).natAbs + (2 * dot sRow (x j)).natAbs, ?_⟩
      unfold controlled
      omega
    intro k
    induction k with
    | zero =>
      obtain ⟨H, hH⟩ := pointwise 0
      exact ⟨H, fun j hj => (show j = 0 by omega) ▸ hH⟩
    | succ k ih =>
      obtain ⟨H, hH⟩ := ih
      obtain ⟨J, hJ⟩ := pointwise (k + 1)
      refine ⟨H + J, fun j hj => ?_⟩
      by_cases hj₀ : j ≤ k
      · exact mono (by omega) (hH j hj₀)
      · rw [show j = k + 1 by omega]
        exact mono (by omega) hJ
  have hex : ∃ H : ℕ, ∀ j, controlled (H : ℤ) (x j) := by
    obtain ⟨H, hH⟩ := hfinite n
    refine ⟨H, fun j => ?_⟩
    by_cases hj : j ≤ n
    · exact hH j hj
    · rw [hn j (by omega)]
      simp [controlled, dot, zero]
  let H := Nat.find hex
  have hH : ∀ j, controlled (H : ℤ) (x j) := Nat.find_spec hex
  have hbound : H ≤ 10000000 := by
    by_contra! hlarge
    have hlt : (10000000 : ℤ) < H := by omega
    have himproved (j : ℕ) : controlled ((H : ℤ) - 1) (x j) := by
      have he :
          -((H : ℤ) - 1) ≤ dot pRow (x j) ∧ dot pRow (x j) ≤ (H : ℤ) - 1 ∧
          -((H : ℤ) - 1) ≤ dot qRow (x j) ∧ dot qRow (x j) ≤ (H : ℤ) - 1 := by
        cases j with
        | zero => exact lattice_controls_real hl (hH 0) (by omega)
        | succ j =>
          obtain ⟨d, hd, h⟩ := hstep j
          exact expanding_bound (hH (j + 1)) (hH j) hd h hlt
      obtain ⟨d, hd, h⟩ := hstep j
      obtain ⟨e, he', h'⟩ := hstep (j + 1)
      obtain ⟨hr₁, hr₂, hs₁, hs₂⟩ :=
        contracting_bound (hH (j + 1 + 1)) he' hd h' h hlt
      exact ⟨he.1, he.2.1, he.2.2.1, he.2.2.2, hr₁, hr₂, hs₁, hs₂⟩
    have hsmaller : ∀ j, controlled ((H - 1 : ℕ) : ℤ) (x j) := fun j =>
      mono (by omega) (himproved j)
    have hmin : H ≤ H - 1 := Nat.find_min' hex hsmaller
    omega
  exact mono (by omega) (hH i)

/-! ## Bounds from the last twelve edges -/

private inductive Axis
  | real
  | imag
  | add
  | sub

private def axes : List Axis := [.real, .imag, .add, .sub]

private def axisRow : Axis → Vec
  | .real => rRow
  | .imag => sRow
  | .add => plus rRow sRow
  | .sub => minus rRow sRow

private def pullIterate : ℕ → Vec → Vec
  | 0, r => r
  | n + 1, r => pullIterate n (pull r)

-- The accumulated error from the earlier part of a path is uniformly small.
private theorem earlier_bound (ax : Axis) {x : Vec} (hx : controlled 10000000 x) :
    -60000 ≤ dot (pullIterate 12 (axisRow ax)) x ∧
      dot (pullIterate 12 (axisRow ax)) x ≤ 60000 := by
  obtain ⟨ha₁, ha₂, hb₁, hb₂, hc₁, hc₂, hd₁, hd₂⟩ := controlled_coords hx
  obtain ⟨_, _, _, _, hr₁, hr₂, hs₁, hs₂⟩ := hx
  simp only [dot, rRow, sRow] at hr₁ hr₂ hs₁ hs₂
  norm_num at ha₁ ha₂ hb₁ hb₂ hc₁ hc₂ hd₁ hd₂
  cases ax <;> simp only [axisRow, pullIterate, pull, dot, rRow, sRow, plus, minus] <;>
    constructor <;> linarith only [ha₁, ha₂, hb₁, hb₂, hc₁, hc₂, hd₁, hd₂, hr₁, hr₂, hs₁, hs₂]

private def suffixWeights : ℕ → Vec → Letter → List ℤ
  | 0, _, _ => [0]
  | n + 1, r, b => (predecessors b).flatMap fun (a, d) =>
    (suffixWeights n (pull r) a).map fun t => dot r d + t

-- Each row of this table bounds the weights of all length-twelve paths ending at a letter.
private def suffixBounds : Axis → Letter → ℤ × ℤ
  | .real, .zero => (-121350, 150072)
  | .real, .one => (200585, 728872)
  | .real, .three => (-44973, 604338)
  | .real, .four => (121178, 495888)
  | .imag, .zero => (-53511, 301119)
  | .imag, .one => (-484018, 82846)
  | .imag, .three => (-670037, -389230)
  | .imag, .four => (10990, 270817)
  | .add, .zero => (-111778, 430636)
  | .add, .one => (-8116, 575190)
  | .add, .three => (-653448, 116988)
  | .add, .four => (193730, 664490)
  | .sub, .zero => (-271130, 50910)
  | .sub, .one => (311544, 1131326)
  | .sub, .three => (414420, 1204610)
  | .sub, .four => (-100456, 386422)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
-- Checking the length-twelve paths for each axis and letter requires additional reduction.
private theorem suffixBounds_valid (ax : Axis) (b : Letter) :
    (suffixWeights 12 (axisRow ax) b).all
      (fun t => decide ((suffixBounds ax b).1 ≤ t ∧ t ≤ (suffixBounds ax b).2)) = true := by
  cases ax <;> cases b <;> decide +kernel

private def within (ax : Axis) (a b c d : Letter) (x : Vec) : Prop :=
  let (aLo, aHi) := suffixBounds ax a
  let (bLo, bHi) := suffixBounds ax b
  let (cLo, cHi) := suffixBounds ax c
  let (dLo, dHi) := suffixBounds ax d
  aLo - bHi - cHi + dLo - 60000 ≤ dot (axisRow ax) x ∧
    dot (axisRow ax) x ≤ aHi - bLo - cLo + dHi + 60000
  deriving Decidable

private def fine (s : State) : Bool :=
  axes.all fun ax =>
    let ⟨a, b, c, d⟩ := s.letters
    decide (within ax a b b c s.u ∧ within ax b c c d s.v ∧
      within ax a b c d (plus s.u s.v))

private def latticeVector (m n : ℤ) : Vec := ⟨m + n, -2 * m - n, 2 * m - n, -m + n⟩

private def latticeCandidates : List Vec :=
  ([-1, 0, 1] : List ℤ).flatMap fun m =>
    ([-1, 0, 1] : List ℤ).map fun n => latticeVector m n

/-! ## The finite search -/

private def letterIndex : Letter → ℕ
  | .zero => 0
  | .one => 1
  | .three => 2
  | .four => 3

-- A certificate obtained by repeatedly adding the admissible predecessors of the terminal states.
-- Each bucket fixes the four boundary letters. Its numbers encode the eight coordinates of the
-- two difference vectors as base-five digits, with 2 representing the coordinate zero.
private def certificate : Letter → Letter → Array (List ℕ)
  | .zero, .zero => #[[195312], [195312, 192812], [257812, 195312], [179687, 195312],
      [], [195312, 197808], [195312], [],
      [132912, 132812], [132912], [132912, 195312], [132912, 132812],
      [195312], [195312], [273412, 273312, 257812], [179687, 195312]]
  | .zero, .one => #[[], [], [177191], [114691],
      [], [195316, 195312], [257191, 195312], [117816],
      [132812], [146040, 195312, 207792, 145917, 130317], [195312], [130316, 132812],
      [257192], [285921], [177191, 273312], []]
  | .zero, .three => #[[257712, 195212], [177112], [], [180336],
      [195212], [195212], [], [185332, 195212],
      [132812, 195212], [272712, 195212], [195312, 195212], [],
      [], [192836], [], []]
  | .zero, .four => #[[195312], [], [], [195312],
      [198536], [195411, 195312], [198536, 121061, 195312], [136036, 195312],
      [], [210412, 132912], [], [],
      [195312], [195312], [273412], [195312]]
  | .one, .zero => #[[195312, 195308], [], [195308], [179687, 195308],
      [], [], [259683], [],
      [148408], [132809], [132912], [132783, 148408],
      [], [], [273412, 273308], [195308, 179583]]
  | .one, .one => #[[192816, 195312], [], [192816], [192816, 179687, 114687, 176567, 130317],
      [197812, 195312], [195312], [257187, 260312, 195312],
      [194687, 197812, 179687, 195312, 182812, 117812],
      [132812], [130416, 195312, 130312, 130317, 207793],
      [195411, 195311, 130416, 195312, 130317],
      [132911, 130416, 194687, 132812, 130312, 130317],
      [257187, 195312], [195312], [192816, 273412, 257187],
      [192816, 179687, 195312, 208417, 176567, 176468]]
  | .one, .three => #[[257712], [193337], [], [180336],
      [182832, 195312, 198333, 259608, 182733], [183457, 195312, 260208, 195208, 198333],
      [183457, 195312, 247728],
      [185332, 182832, 120957, 195312, 195208, 182708, 198333, 182733],
      [132936, 132812], [130436, 195312, 130312, 272708, 195208],
      [195311, 195436, 195312, 195208], [],
      [257836, 257712], [257836, 257207, 192832, 257708, 273333, 257108], [], [273333]]
  | .one, .four => #[[195312], [], [196036], [195312],
      [185457], [195312], [195312], [195312, 120433],
      [210308], [207911, 146036, 210412, 130412, 130437, 207808], [211011],
      [148511, 132911, 132783, 148408],
      [195312], [195312], [273412], [195312, 195308]]
  | .three, .zero => #[[195412, 195312], [192812], [], [],
      [197783], [197808], [182912], [120412],
      [], [], [], [],
      [], [257188], [], []]
  | .three, .one => #[[195312], [192915], [257792], [],
      [197911, 195312], [195411, 195416, 195312], [183436, 195312, 194668],
      [120936, 117916, 195312, 182812],
      [], [142896, 195312, 207793], [195312], [142896],
      [195312, 257192, 272693], [195312], [], [195312, 208417]]
  | .three, .three => #[[195312, 257712], [257712], [], [],
      [195312], [257187, 194687, 195312, 260208, 198333], [195312], [195312, 182708, 198333],
      [195312, 132812], [194687, 272812, 195312, 130312], [195312], [],
      [], [241587], [], []]
  | .three, .four => #[[195412, 179812, 117312], [179812, 114812], [], [],
      [117312, 197783], [195411, 179812, 197808], [], [120433],
      [], [], [], [],
      [179812], [179812], [], []]
  | .four, .zero => #[[195287, 195312], [195287, 192812], [], [195312],
      [197683], [198407, 195287, 195183, 197808, 198333], [], [120308, 198333, 117188],
      [210288], [210288], [], [],
      [195312], [195312], [], [195312]]
  | .four, .one => #[[], [], [257692], [195812, 192692, 130317],
      [197688], [195311, 195316, 195287, 195312, 195292, 195188],
      [195312, 195292, 260188, 194568], [182811, 117816, 195312, 194667, 197688],
      [207796, 132812], [207796, 195312, 130312, 207792, 130292, 145917, 130317, 207693],
      [195312, 130292, 130317], [207796, 132812, 145917, 130317, 207693],
      [195312, 257092], [195312, 270817], [270817], [195312]]
  | .four, .three => #[[257712, 195212], [177087, 177112], [], [],
      [195212, 197708], [195311, 257087, 195212, 260208, 195208, 198333], [247728],
      [185332, 120957, 195212, 198333, 182733],
      [], [], [], [],
      [], [257087, 177087, 241487, 177112], [], []]
  | .four, .four => #[[195287, 195312], [130287, 192812], [], [195312],
      [], [198407, 136532, 195287, 195312, 197808, 182833], [195312, 182833], [195312],
      [], [130437], [], [],
      [195312], [195312, 192812], [], [195312]]

private def bucket (l : Boundary) : List ℕ :=
  (certificate l.a l.b)[4 * letterIndex l.c + letterIndex l.d]?.getD []

private def baseFiveCoord (n : ℕ) : ℤ := (n % 5 : ℕ) - (2 : ℤ)

private def decodeVector (n : ℕ) : Vec :=
  ⟨baseFiveCoord n, baseFiveCoord (n / 5), baseFiveCoord (n / 25), baseFiveCoord (n / 125)⟩

private def decodeState (l : Boundary) (n : ℕ) : State :=
  ⟨l, decodeVector n, decodeVector (n / 625)⟩

private def listed (s : State) : Bool :=
  (bucket s.letters).any fun n => decide (decodeState s.letters n = s)

private def candidates (a b c : Letter) : List Vec :=
  latticeCandidates.filter fun v => axes.all fun ax => decide (within ax a b b c v)

private def terminalStates (l : Boundary) : List State := do
  let u ← candidates l.a l.b l.c
  let v ← candidates l.b l.c l.d
  let s := ⟨l, u, v⟩
  if fine s then [s] else []

private def checkIncoming (s : State) : Bool :=
  (previous s).all fun p =>
    (!fine p || listed p) && (!decide (diagonal p) || decide (diagonal s))

-- Check terminal coverage and closure under eligible predecessors. A transition out of a
-- diagonal state into a listed state must also end on the diagonal.
private def checkBucket (l : Boundary) : Bool :=
  (terminalStates l).all listed && (bucket l).all fun n => checkIncoming (decodeState l n)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6000000 in
-- The kernel checks terminal coverage and incoming transitions for all 256 letter tuples.
private theorem certificate_valid (l : Boundary) : checkBucket l = true := by
  obtain ⟨a, b, c, d⟩ := l
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem incoming_of_listed {s : State} (h : listed s = true) :
    checkIncoming s = true := by
  obtain ⟨n, hn, he⟩ := List.any_eq_true.mp h
  have hs : decodeState s.letters n = s := of_decide_eq_true he
  rw [← hs]
  exact List.all_eq_true.mp (Bool.and_eq_true_iff.mp (certificate_valid s.letters)).2 n hn

private def tailWeight : ℕ → (ℕ → Vec) → Vec → ℕ → ℤ
  | 0, _, _, _ => 0
  | n + 1, d, r, i => dot r (d i) + tailWeight n d (pull r) (i + 1)

private theorem tailWeight_mem {b : ℕ → Letter} {d : ℕ → Vec}
    (h : ∀ i, (b (i + 1), d i) ∈ predecessors (b i)) (n : ℕ) (r : Vec) (i : ℕ) :
    tailWeight n d r i ∈ suffixWeights n r (b i) := by
  induction n generalizing r i with
  | zero => simp [tailWeight, suffixWeights]
  | succ n ih =>
    exact List.mem_flatMap.mpr
      ⟨_, h i, List.mem_map.mpr ⟨_, ih (pull r) (i + 1), rfl⟩⟩

private theorem tailWeight_bound {b : ℕ → Letter} {d : ℕ → Vec}
    (h : ∀ i, (b (i + 1), d i) ∈ predecessors (b i)) (ax : Axis) (i : ℕ) :
    (suffixBounds ax (b i)).1 ≤ tailWeight 12 d (axisRow ax) i ∧
      tailWeight 12 d (axisRow ax) i ≤ (suffixBounds ax (b i)).2 := by
  exact of_decide_eq_true
    (List.all_eq_true.mp (suffixBounds_valid ax (b i)) _ (tailWeight_mem h 12 (axisRow ax) i))

private theorem dot_eq_tail {x a b c d : ℕ → Vec}
    (h : ∀ i, x i = plus (incidence (x (i + 1))) (difference (a i) (b i) (c i) (d i)))
    (n : ℕ) (r : Vec) (i : ℕ) :
    dot r (x i) = dot (pullIterate n r) (x (i + n)) + tailWeight n a r i -
      tailWeight n b r i - tailWeight n c r i + tailWeight n d r i := by
  induction n generalizing r i with
  | zero => simp [tailWeight, pullIterate]
  | succ n ih =>
    conv_lhs => rw [h i, dot_plus, dot_incidence, dot_difference, ih (pull r) (i + 1)]
    simp only [tailWeight, pullIterate, show i + (n + 1) = i + 1 + n by omega]
    ring

private theorem within_of_path {x a b c d : ℕ → Vec} {la lb lc ld : ℕ → Letter}
    (h : ∀ i, x i = plus (incidence (x (i + 1))) (difference (a i) (b i) (c i) (d i)))
    (ha : ∀ i, (la (i + 1), a i) ∈ predecessors (la i))
    (hb : ∀ i, (lb (i + 1), b i) ∈ predecessors (lb i))
    (hc : ∀ i, (lc (i + 1), c i) ∈ predecessors (lc i))
    (hd : ∀ i, (ld (i + 1), d i) ∈ predecessors (ld i))
    (hx : ∀ i, controlled 10000000 (x i)) (ax : Axis) (i : ℕ) :
    within ax (la i) (lb i) (lc i) (ld i) (x i) := by
  obtain ⟨h₁, h₂⟩ := earlier_bound ax (hx (i + 12))
  obtain ⟨ha₁, ha₂⟩ := tailWeight_bound ha ax i
  obtain ⟨hb₁, hb₂⟩ := tailWeight_bound hb ax i
  obtain ⟨hc₁, hc₂⟩ := tailWeight_bound hc ax i
  obtain ⟨hd₁, hd₂⟩ := tailWeight_bound hd ax i
  unfold within
  dsimp only
  rw [dot_eq_tail h 12]
  omega

-- Index zero represents the alleged cube. Larger indices follow its substitution ancestors,
-- with self-loops padding the walk after it reaches the root.
private def Walk (s : ℕ → State) : Prop :=
  (∃ n, ∀ i, n ≤ i → s i = root) ∧ ∀ i, Step (s (i + 1)) (s i)

private theorem lattice_add {x y : Vec} (hx : lattice x) (hy : lattice y) :
    lattice (plus x y) := by
  obtain ⟨hx₁, hx₂⟩ := hx
  obtain ⟨hy₁, hy₂⟩ := hy
  simp [lattice, dot_plus, hx₁, hy₁, hx₂, hy₂]

private theorem fine_of_walk {s : ℕ → State} (h : Walk s)
    (hu₀ : lattice (s 0).u) (hv₀ : lattice (s 0).v) (i : ℕ) : fine (s i) = true := by
  classical
  obtain ⟨⟨n, hn⟩, hstep⟩ := h
  unfold Step at hstep
  choose a b c d ha hb hc hd hu hv using hstep
  have huv (j : ℕ) := step_add (hu j) (hv j)
  have hdigit (j : ℕ) : digit (a j) ∧ digit (b j) ∧ digit (c j) ∧ digit (d j) :=
    ⟨predecessor_digit (ha j), predecessor_digit (hb j),
      predecessor_digit (hc j), predecessor_digit (hd j)⟩
  have controlU : ∀ j, controlled 10000000 (s j).u :=
    bounded_of_admissible ⟨⟨n, fun j hj => congrArg State.u (hn j hj)⟩, hu₀, fun j =>
      ⟨_, ⟨_, _, _, _, (hdigit j).1, (hdigit j).2.1, (hdigit j).2.1, (hdigit j).2.2.1, rfl⟩,
        hu j⟩⟩
  have controlV : ∀ j, controlled 10000000 (s j).v :=
    bounded_of_admissible ⟨⟨n, fun j hj => congrArg State.v (hn j hj)⟩, hv₀, fun j =>
      ⟨_, ⟨_, _, _, _, (hdigit j).2.1, (hdigit j).2.2.1, (hdigit j).2.2.1, (hdigit j).2.2.2,
        rfl⟩, hv j⟩⟩
  have controlUV : ∀ j, controlled 10000000 (plus (s j).u (s j).v) :=
    bounded_of_admissible ⟨⟨n, fun j hj => congrArg (fun p => plus p.u p.v) (hn j hj)⟩,
      lattice_add hu₀ hv₀, fun j => ⟨_, ⟨_, _, _, _, (hdigit j).1, (hdigit j).2.1, (hdigit j).2.2.1,
        (hdigit j).2.2.2, rfl⟩, huv j⟩⟩
  apply List.all_eq_true.mpr
  intro ax _
  apply decide_eq_true
  exact ⟨within_of_path hu ha hb hb hc controlU ax i,
    within_of_path hv hb hc hc hd controlV ax i, within_of_path huv ha hb hc hd controlUV ax i⟩

private theorem fine_within {s : State} {ax : Axis} (h : fine s = true) (ha : ax ∈ axes) :
    within ax s.letters.a s.letters.b s.letters.b s.letters.c s.u ∧
      within ax s.letters.b s.letters.c s.letters.c s.letters.d s.v ∧
      within ax s.letters.a s.letters.b s.letters.c s.letters.d (plus s.u s.v) :=
  of_decide_eq_true (List.all_eq_true.mp h ax ha)

private theorem suffixBounds_real_range (a : Letter) :
    -122000 ≤ (suffixBounds .real a).1 ∧ (suffixBounds .real a).2 ≤ 729000 := by
  cases a <;> decide

private theorem suffixBounds_imag_range (a : Letter) :
    -671000 ≤ (suffixBounds .imag a).1 ∧ (suffixBounds .imag a).2 ≤ 302000 := by
  cases a <;> decide

private theorem mem_latticeCandidates {x : Vec} {a b c d : Letter}
    (h : lattice x) (hr : within .real a b c d x) (hs : within .imag a b c d x) :
    x ∈ latticeCandidates := by
  have hR : -1800000 ≤ dot rRow x ∧ dot rRow x ≤ 1800000 := by
    obtain ⟨ha₁, ha₂⟩ := suffixBounds_real_range a
    obtain ⟨hb₁, hb₂⟩ := suffixBounds_real_range b
    obtain ⟨hc₁, hc₂⟩ := suffixBounds_real_range c
    obtain ⟨hd₁, hd₂⟩ := suffixBounds_real_range d
    unfold within at hr
    dsimp only [axisRow] at hr
    omega
  have hS : -2050000 ≤ dot sRow x ∧ dot sRow x ≤ 2050000 := by
    obtain ⟨ha₁, ha₂⟩ := suffixBounds_imag_range a
    obtain ⟨hb₁, hb₂⟩ := suffixBounds_imag_range b
    obtain ⟨hc₁, hc₂⟩ := suffixBounds_imag_range c
    obtain ⟨hd₁, hd₂⟩ := suffixBounds_imag_range d
    unfold within at hs
    dsimp only [axisRow] at hs
    omega
  obtain ⟨hLen, hSum⟩ := h
  obtain ⟨hr₁, hr₂⟩ := hR
  obtain ⟨hs₁, hs₂⟩ := hS
  simp only [dot, lengthRow, sumRow, rRow, sRow] at hLen hSum hr₁ hr₂ hs₁ hs₂
  let m := x.c + x.d
  let n := x.c + 2 * x.d
  have hm₁ : -2 < m := by dsimp [m]; linarith only [hLen, hSum, hr₁, hr₂, hs₁, hs₂]
  have hm₂ : m < 2 := by dsimp [m]; linarith only [hLen, hSum, hr₁, hr₂, hs₁, hs₂]
  have hn₁ : -2 < n := by dsimp [n]; linarith only [hLen, hSum, hr₁, hr₂, hs₁, hs₂]
  have hn₂ : n < 2 := by dsimp [n]; linarith only [hLen, hSum, hr₁, hr₂, hs₁, hs₂]
  have hm : m ∈ ([-1, 0, 1] : List ℤ) := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    omega
  have hn : n ∈ ([-1, 0, 1] : List ℤ) := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    omega
  refine List.mem_flatMap.mpr ⟨m, hm, List.mem_map.mpr ⟨n, hn, ?_⟩⟩
  cases x
  dsimp only [latticeVector, m, n] at *
  simp only [Vec.mk.injEq]
  omega

private theorem mem_terminalStates {s : State} (hu : lattice s.u) (hv : lattice s.v)
    (hf : fine s = true) : s ∈ terminalStates s.letters := by
  obtain ⟨⟨a, b, c, d⟩, u, v⟩ := s
  have hr := fine_within hf (ax := .real) (by simp [axes])
  have hs := fine_within hf (ax := .imag) (by simp [axes])
  simp only [terminalStates, List.bind_eq_flatMap, List.mem_flatMap]
  refine ⟨u, ?_, v, ?_, ?_⟩
  · apply List.mem_filter.mpr
    refine ⟨mem_latticeCandidates hu hr.1 hs.1, List.all_eq_true.mpr ?_⟩
    exact fun ax hx => decide_eq_true (fine_within hf hx).1
  · apply List.mem_filter.mpr
    refine ⟨mem_latticeCandidates hv hr.2.1 hs.2.1, List.all_eq_true.mpr ?_⟩
    exact fun ax hx => decide_eq_true (fine_within hf hx).2.1
  · simp [hf]

private theorem walk_diagonal {s : ℕ → State} (hs : Walk s)
    (hu : lattice (s 0).u) (hv : lattice (s 0).v) (i : ℕ) : diagonal (s i) := by
  have hf := fine_of_walk hs hu hv
  obtain ⟨⟨n, hn⟩, hstep⟩ := hs
  have checked {p q : State} (hq : listed q = true) (h : Step p q) :=
    Bool.and_eq_true_iff.mp (List.all_eq_true.mp (incoming_of_listed hq) p (mem_previous h))
  have hmem (j : ℕ) : listed (s j) = true := by
    induction j with
    | zero =>
      exact List.all_eq_true.mp (Bool.and_eq_true_iff.mp (certificate_valid (s 0).letters)).1
        _ (mem_terminalStates hu hv (hf 0))
    | succ j ih =>
      have h := (checked ih (hstep j)).1
      simpa [hf (j + 1)] using h
  have descend : ∀ k j : ℕ, n ≤ j + k → diagonal (s j) := by
    intro k
    induction k with
    | zero =>
      intro j hj
      rw [hn j (by omega)]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    | succ k ih =>
      intro j hj
      have hd := ih (j + 1) (by omega)
      have h := (checked (hmem j) (hstep j)).2
      simpa [hd] using h
  exact descend n i (by omega)

/-! ## The paths of four boundaries in a substitution iterate -/

private def parikh : List Letter → Vec
  | [] => zero
  | a :: w => plus (unit a) (parikh w)

private theorem parikh_append (x y : List Letter) :
    parikh (x ++ y) = plus (parikh x) (parikh y) := by
  induction x with
  | nil =>
    simp [parikh, plus, zero]
  | cons a x ih =>
    simp only [List.cons_append, parikh, ih, plus, Vec.mk.injEq]
    exact ⟨by ring, by ring, by ring, by ring⟩

private theorem parikh_flatMap (w : List Letter) :
    parikh (w.flatMap substitution) = incidence (parikh w) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [List.flatMap_cons, parikh_append, ih]
    cases a <;> simp [substitution, parikh, unit, zero, plus, incidence, Vec.mk.injEq] <;>
      omega

private theorem length_parikh (w : List Letter) : dot lengthRow (parikh w) = w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [parikh, dot_plus, ih, List.length_cons, Nat.cast_add, Nat.cast_one, add_comm]
    cases a <;> rfl

private theorem value_unit (a : Letter) : dot sumRow (unit a) = letterValue a := by
  cases a <;> rfl

private theorem get_parent (w : List Letter) (i : Fin (w.flatMap substitution).length) :
    ∃ (j : Fin w.length) (k : Fin (substitution w[j.val]).length),
      (w.flatMap substitution)[i.val] = (substitution w[j.val])[k.val] ∧
      (w.flatMap substitution).take i.val =
        (w.take j.val).flatMap substitution ++ (substitution w[j.val]).take k.val ∧
      i.val = ((w.take j.val).flatMap substitution).length + k.val := by
  induction w with
  | nil => exact Fin.elim0 i
  | cons a w ih =>
    have hi : i.val < (substitution a).length + (w.flatMap substitution).length := by
      simpa only [List.flatMap_cons, List.length_append] using i.isLt
    by_cases h : i.val < (substitution a).length
    · refine ⟨⟨0, by simp⟩, ⟨i.val, h⟩, ?_, ?_, ?_⟩
      · exact List.getElem_append_left h
      · simp [List.take_append_of_le_length (Nat.le_of_lt h)]
      · simp
    · let i' : Fin (w.flatMap substitution).length :=
        ⟨i.val - (substitution a).length, by omega⟩
      obtain ⟨j, k, hletter, htake, hindex⟩ := ih i'
      refine ⟨j.succ, k, ?_, ?_, ?_⟩
      · exact (List.getElem_append_right (by omega)).trans hletter
      · change (substitution a ++ w.flatMap substitution).take i.val =
          (substitution a ++ (w.take j.val).flatMap substitution) ++
            (substitution w[j.val]).take k.val
        rw [List.take_append, List.take_of_length_le (by omega), List.append_assoc]
        exact congrArg (substitution a ++ ·) htake
      · change i.val = (substitution a ++ (w.take j.val).flatMap substitution).length + k.val
        rw [List.length_append]
        dsimp [i'] at hindex
        omega

private theorem substitution_edge (a : Letter) (i : Fin (substitution a).length) :
    (a, parikh ((substitution a).take i.val)) ∈ predecessors (substitution a)[i.val] := by
  cases a <;> fin_cases i <;> simp [predecessors, substitution, parikh, zero, plus, unit]

private theorem substitution_nodup (a : Letter) : (substitution a).Nodup := by
  cases a <;> simp [substitution]

private def stateAt (w : List Letter) (a b c d : Fin w.length) : State :=
  let x := parikh (w.take a.val)
  let y := parikh (w.take b.val)
  let z := parikh (w.take c.val)
  let t := parikh (w.take d.val)
  ⟨⟨w[a.val], w[b.val], w[c.val], w[d.val]⟩, difference x y y z, difference y z z t⟩

private def prependState (q : State) (s : ℕ → State) : ℕ → State
  | 0 => q
  | i + 1 => s i

private theorem walk_prepend {s : ℕ → State} {q : State} (hs : Walk s) (hq : Step (s 0) q) :
    Walk (prependState q s) := by
  obtain ⟨⟨n, hn⟩, hstep⟩ := hs
  refine ⟨⟨n + 1, fun i hi => ?_⟩, fun i => ?_⟩
  · cases i with
    | zero => omega
    | succ i => exact hn i (by omega)
  · cases i with
    | zero => exact hq
    | succ i => exact hstep i

private theorem difference_substitution (a b c d x y z t : Vec) :
    difference (plus (incidence a) x) (plus (incidence b) y)
      (plus (incidence c) z) (plus (incidence d) t) =
    plus (incidence (difference a b c d)) (difference x y z t) := by
  simp only [difference, incidence, plus, minus, Vec.mk.injEq]
  exact ⟨by ring, by ring, by ring, by ring⟩

private theorem walk_from_iterate (n : ℕ) (a b c d : Fin (substitutionIterate n).length) :
    ∃ s : ℕ → State, Walk s ∧ s 0 = stateAt (substitutionIterate n) a b c d ∧
      ((∀ i, diagonal (s i)) → a = d) := by
  induction n with
  | zero =>
    have ha : a.val = 0 := by have := a.isLt; change a.val < 1 at this; omega
    have hb : b.val = 0 := by have := b.isLt; change b.val < 1 at this; omega
    have hc : c.val = 0 := by have := c.isLt; change c.val < 1 at this; omega
    have hd : d.val = 0 := by have := d.isLt; change d.val < 1 at this; omega
    refine ⟨fun _ => root, ⟨⟨0, fun _ _ => rfl⟩, fun _ => step_root⟩, ?_,
      fun _ => Fin.ext (ha.trans hd.symm)⟩
    simp [stateAt, substitutionIterate, ha, hb, hc, hd, root, parikh, difference, plus, minus, zero]
  | succ n ih =>
    let w := substitutionIterate n
    obtain ⟨a', ia, haL, haT, haI⟩ := get_parent w a
    obtain ⟨b', ib, hbL, hbT, hbI⟩ := get_parent w b
    obtain ⟨c', ic, hcL, hcT, hcI⟩ := get_parent w c
    obtain ⟨d', id, hdL, hdT, hdI⟩ := get_parent w d
    obtain ⟨s, hs, hs₀, hcollapsed⟩ := ih a' b' c' d'
    let q := stateAt (w.flatMap substitution) a b c d
    have hStep : Step (s 0) q := by
      rw [hs₀]
      refine ⟨parikh ((substitution w[a'.val]).take ia.val),
        parikh ((substitution w[b'.val]).take ib.val),
        parikh ((substitution w[c'.val]).take ic.val),
        parikh ((substitution w[d'.val]).take id.val), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [q, stateAt, haL] using substitution_edge w[a'.val] ia
      · simpa only [q, stateAt, hbL] using substitution_edge w[b'.val] ib
      · simpa only [q, stateAt, hcL] using substitution_edge w[c'.val] ic
      · simpa only [q, stateAt, hdL] using substitution_edge w[d'.val] id
      · dsimp only [q, stateAt]
        rw [haT, hbT, hcT]
        simp only [parikh_append, parikh_flatMap, difference_substitution, w]
      · dsimp only [q, stateAt]
        rw [hbT, hcT, hdT]
        simp only [parikh_append, parikh_flatMap, difference_substitution, w]
    refine ⟨prependState q s, walk_prepend hs hStep, rfl, fun hAll => ?_⟩
    have hParent : a' = d' := hcollapsed fun i => hAll (i + 1)
    have hLetter : (w.flatMap substitution)[a.val] = (w.flatMap substitution)[d.val] :=
      (hAll 0).1.trans ((hAll 0).2.1.trans (hAll 0).2.2.1)
    subst d'
    have hLocal : ia = id := by
      exact (List.nodup_iff_injective_get.mp (substitution_nodup w[a'.val]))
        (haL.symm.trans (hLetter.trans hdL))
    exact Fin.ext (haI.trans (hLocal ▸ hdI.symm))

/-! ## Passing to the infinite word -/

private theorem flatMap_nonempty {w : List Letter} (hw : w ≠ []) :
    w.flatMap substitution ≠ [] := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons a w => cases a <;> simp [substitution]

private theorem iterate_growth (k : ℕ) :
    ∃ t : List Letter, t ≠ [] ∧ substitutionIterate (k + 1) = substitutionIterate k ++ t := by
  induction k with
  | zero => exact ⟨[.three], by simp, rfl⟩
  | succ k ih =>
    obtain ⟨t, ht, h⟩ := ih
    refine ⟨t.flatMap substitution, flatMap_nonempty ht, ?_⟩
    change (substitutionIterate (k + 1)).flatMap substitution = _
    calc
      _ = (substitutionIterate k ++ t).flatMap substitution :=
        congrArg (List.flatMap substitution) h
      _ = _ := List.flatMap_append

private theorem iterate_prefix {k l : ℕ} (h : k ≤ l) :
    substitutionIterate k <+: substitutionIterate l := by
  induction h with
  | refl => exact List.prefix_refl _
  | @step l _ ih =>
    obtain ⟨t, _, ht⟩ := iterate_growth l
    exact ih.trans ⟨t, ht.symm⟩

private theorem iterate_length (k : ℕ) : k < (substitutionIterate k).length := by
  induction k with
  | zero => decide
  | succ k ih =>
    obtain ⟨t, ht, he⟩ := iterate_growth k
    rw [he, List.length_append]
    have hpos : 0 < t.length := List.length_pos_iff.mpr ht
    omega

private def fixedWord (i : ℕ) : Letter := (substitutionIterate i)[i]'(iterate_length i)

private theorem generated_fixedWord : IsGeneratedFixedPoint fixedWord := by
  intro k i hi
  rcases le_total i k with h | h
  · exact (iterate_prefix h).getElem (iterate_length i)
  · exact ((iterate_prefix h).getElem hi).symm

private theorem value_prefix (k i : ℕ) (hi : i ≤ (substitutionIterate k).length) :
    dot sumRow (parikh ((substitutionIterate k).take i)) = factorSum fixedWord 0 i := by
  induction i with
  | zero => simp [factorSum, parikh, dot, zero]
  | succ i ih =>
    have h : i < (substitutionIterate k).length := by omega
    rw [List.take_succ_eq_append_getElem h, parikh_append, dot_plus, ih (by omega)]
    simp only [factorSum, Finset.sum_range_succ, zero_add, parikh, dot_plus, value_unit]
    have he : fixedWord i = (substitutionIterate k)[i] := generated_fixedWord k i h
    rw [he]
    simp [dot, zero]

private theorem prefix_add (w : ℕ → Letter) (s l : ℕ) :
    factorSum w 0 (s + l) = factorSum w 0 s + factorSum w s l := by
  simp only [factorSum, zero_add]
  rw [Finset.sum_range_add]

private theorem fixedWord_avoids : AvoidsPVHHCubes fixedWord := by
  intro s l hl ⟨hl₁, hl₂⟩
  let n := s + l + l + l
  have hn := iterate_length n
  let a : Fin (substitutionIterate n).length := ⟨s, by omega⟩
  let b : Fin (substitutionIterate n).length := ⟨s + l, by omega⟩
  let c : Fin (substitutionIterate n).length := ⟨s + l + l, by omega⟩
  let d : Fin (substitutionIterate n).length := ⟨n, hn⟩
  obtain ⟨q, hq, he, hcollapsed⟩ := walk_from_iterate n a b c d
  have hLen (i : Fin (substitutionIterate n).length) :
      dot lengthRow (parikh ((substitutionIterate n).take i.val)) = (i.val : ℤ) := by
    rw [length_parikh, List.length_take, min_eq_left (Nat.le_of_lt i.isLt)]
  have hSum (i : Fin (substitutionIterate n).length) :
      dot sumRow (parikh ((substitutionIterate n).take i.val)) = factorSum fixedWord 0 i.val :=
    value_prefix n i.val (Nat.le_of_lt i.isLt)
  have heq : a = d := by
    apply hcollapsed
    apply walk_diagonal hq
    · rw [he]
      simp only [stateAt, lattice, dot_difference, hLen, hSum]
      dsimp only [a, b, c]
      rw [prefix_add fixedWord (s + l) l, prefix_add fixedWord s l]
      omega
    · rw [he]
      simp only [stateAt, lattice, dot_difference, hLen, hSum]
      dsimp only [b, c, d, n]
      rw [prefix_add fixedWord (s + l + l) l, prefix_add fixedWord (s + l) l]
      rw [show s + l + l = s + 2 * l by omega] at *
      omega
  have hIndex := congrArg Fin.val heq
  dsimp [a, d, n] at hIndex
  omega

/-- **The Cassaigne–Currie–Schaeffer–Shallit word avoids additive cubes.** Let $\sigma$ be the
substitution $0 \mapsto 03$, $1 \mapsto 43$, $3 \mapsto 1$, $4 \mapsto 01$ on the alphabet
$\{0, 1, 3, 4\}$, extended to words by replacing each letter with its image. There is an infinite
word $w = w_0 w_1 w_2 \cdots$ over $\{0, 1, 3, 4\}$ such that $\sigma^k(0)$ is a prefix of $w$ for
every $k \ge 0$, and $w$ contains no additive cube: there are no natural numbers $s$ and
$\ell \ge 1$ such that the three consecutive factors of length $\ell$ starting at positions $s$,
$s + \ell$ and $s + 2\ell$ all have the same sum of letter values.

Source: Julien Cassaigne, James
D. Currie, Luke Schaeffer and Jeffrey Shallit, Avoiding three consecutive blocks of the same
size and same sum, J. ACM 61(2) (2014), Article 10, arXiv:1106.5204,
https://arxiv.org/abs/1106.5204. Moved from `OpenConjectures/Combinatorics/PVHHCubeMorphicWord`.
-/
public theorem conjecture_holds : conjecture :=
  ⟨fixedWord, generated_fixedWord, fixedWord_avoids⟩

end MathlibExt.Combinatorics.PVHHCubeMorphicWordWanted
