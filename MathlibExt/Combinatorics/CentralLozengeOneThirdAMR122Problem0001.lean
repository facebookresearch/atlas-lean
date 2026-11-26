/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The central lozenge of the 2n - 1, 2n, 2n - 1 hexagon (Propp, Problem 1)

J. Propp, Twenty open problems in enumeration of matchings, Problem 1: show that in the `2n - 1, 2n,
2n - 1` semiregular hexagon, the central location (consisting of the two innermost triangles) is
covered by a lozenge in exactly one-third of the tilings. (Equivalently: if one chooses a random
perfect matching of the dual graph, the probability that the central edge is contained in the
matching is exactly 1/3.)
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Matching

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Chain
import Mathlib.Data.List.OfFn
import MathlibExt.Combinatorics.Enumerative.LindstromGesselViennot
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Int.Interval
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace MathlibExt.Combinatorics.CentralLozengeOneThirdAMR122Problem0001Wanted

@[expose] public section

/-!
Source: J. Propp, Twenty open problems in enumeration of matchings (1998), arXiv:math/9801060,
Problem 1. UnsolvedMath record UM-00800330 (`AMR-122-0001`), dataset ulamai/UnsolvedMath v1.8.0.

The `a, b, c` semiregular hexagon has side lengths `a, b, c, a, b, c` (Propp); it is placed in the
triangular lattice with vertices `0, a e₁, a e₁ + b e₂, (a - c) e₁ + (b + c) e₂, -c e₁ + (b + c) e₂,
-c e₁ + c e₂`, and lozenge tilings are the perfect matchings (Mathlib's
`Subgraph.IsPerfectMatching`) of the dual honeycomb graph, the correspondence Propp states. For `a =
c = 2n - 1`, `b = 2n` the center `(2n - 1/2) e₂` is the midpoint of the edge shared by the upward
triangle `(0, 2n - 1)` and the downward triangle `(-1, 2n - 1)`, the two innermost triangles.
Checked by computation (Kasteleyn determinants): the encoding gives MacMahon's counts (2, 20, 490
tilings for the 1,1,1, 2,2,2 and 2,3,4 hexagons; 3, 4116, 3184461423 for n = 1, 2, 3) and the
central lozenge lies in exactly one third of the tilings for n = 1, …, 5.
-/

/-- **Unit triangles of the triangular lattice.** Let $e_1 = (1, 0)$ and
$e_2 = (1/2, \sqrt{3}/2)$, and write $p(i, j) = i e_1 + j e_2$ for integers $i, j$. A unit
triangle is a triple $(i, j, d)$ of integers $i, j$ and a boolean $d$: for $d$ false it is the
upward triangle $(i, j)$ with vertices $p(i, j)$, $p(i + 1, j)$, $p(i, j + 1)$, and for $d$ true
it is the downward triangle $(i, j)$ with vertices $p(i + 1, j)$, $p(i, j + 1)$, $p(i + 1, j + 1)$.
-/
abbrev LatticeTriangle := ℤ × ℤ × Bool

/-- **Unit triangles of a semiregular hexagon.** Let $e_1 = (1, 0)$, $e_2 = (1/2, \sqrt{3}/2)$ and
$p(i, j) = i e_1 + j e_2$, and call the triangles with vertices $p(i, j), p(i + 1, j), p(i, j + 1)$
and $p(i + 1, j), p(i, j + 1), p(i + 1, j + 1)$ the upward and the downward unit triangle $(i, j)$.
For integers $a, b, c$, the upward unit triangle $(i, j)$ lies in the $a, b, c$ hexagon when
$0 \le j \le b + c - 1$, $-c \le i \le a - 1$ and $0 \le i + j \le a + b - 1$, and the downward
unit triangle $(i, j)$ lies in it when $0 \le j \le b + c - 1$, $-c \le i \le a - 1$ and
$-1 \le i + j \le a + b - 2$.

These are exactly the unit triangles whose three vertices lie in the region of points
$i e_1 + j e_2$ with $0 \le j \le b + c$, $-c \le i \le a$ and $0 \le i + j \le a + b$. For
$a, b, c \ge 0$ this region is the (possibly degenerate) semiregular hexagon with side lengths
$a, b, c, a, b, c$ and vertices $0$, $a e_1$, $a e_1 + b e_2$, $(a - c) e_1 + (b + c) e_2$,
$-c e_1 + (b + c) e_2$ and $-c e_1 + c e_2$. -/
def InHexagon (a b c : ℤ) : LatticeTriangle → Prop
  | (i, j, false) => 0 ≤ j ∧ j ≤ b + c - 1 ∧ -c ≤ i ∧ i ≤ a - 1 ∧ 0 ≤ i + j ∧ i + j ≤ a + b - 1
  | (i, j, true) => 0 ≤ j ∧ j ≤ b + c - 1 ∧ -c ≤ i ∧ i ≤ a - 1 ∧ -1 ≤ i + j ∧ i + j ≤ a + b - 2

/-- **Unit triangles sharing an edge.** The relation between unit triangles $s$ and $t$ that holds
exactly when $s$ is an upward triangle $(i, j)$ and $t$ is one of the downward triangles $(i, j)$,
$(i - 1, j)$ and $(i, j - 1)$. These are the three downward triangles that share an edge with
the upward triangle $(i, j)$; the relation never holds with $s$ downward or $t$ upward. -/
def SharesEdge : LatticeTriangle → LatticeTriangle → Prop
  | (i, j, false), (i', j', true) =>
    (i', j') = (i, j) ∨ (i', j') = (i - 1, j) ∨ (i', j') = (i, j - 1)
  | _, _ => False

/-- **Dual honeycomb graph of a hexagon.** For integers $a, b, c$, the dual graph of the $a, b, c$
hexagon is the simple graph whose vertices are the unit triangles lying in the $a, b, c$ hexagon,
two of them being adjacent when one is an upward unit triangle $(i, j)$ and the other is one of the
downward unit triangles $(i, j)$, $(i - 1, j)$ and $(i, j - 1)$, that is, when they share an edge.

Its perfect matchings are the lozenge tilings of the hexagon (a lozenge is the union of the two
triangles of a matching edge). -/
def hexagonGraph (a b c : ℤ) : SimpleGraph {t : LatticeTriangle // InHexagon a b c t} :=
  SimpleGraph.fromRel fun s t => SharesEdge s.1 t.1

/-- **Propp's central lozenge problem.** Let $e_1 = (1, 0)$ and $e_2 = (1/2, \sqrt{3}/2)$, write
$p(i, j) = i e_1 + j e_2$, and call the triangles with vertices $p(i, j), p(i + 1, j), p(i, j + 1)$
and $p(i + 1, j), p(i, j + 1), p(i + 1, j + 1)$ the upward and the downward unit triangle $(i, j)$.
The statement that for every integer $n \ge 1$, with $a = c = 2n - 1$ and $b = 2n$, in the
semiregular hexagon with side lengths $a, b, c, a, b, c$ and vertices $0$, $a e_1$,
$a e_1 + b e_2$, $(a - c) e_1 + (b + c) e_2$, $-c e_1 + (b + c) e_2$ and $-c e_1 + c e_2$, three
times the number of perfect matchings of the dual honeycomb graph of the hexagon (whose vertices
are the unit triangles inside the hexagon and whose edges join triangles sharing an edge) that
contain the edge joining the upward unit triangle $(0, 2n - 1)$ and the downward unit triangle
$(-1, 2n - 1)$ equals the number of all perfect matchings of that graph.

These two triangles are the innermost ones: the edge they share has the center of the hexagon as
its midpoint. Since perfect matchings of the dual graph are lozenge tilings, the statement says
that the central location is covered by a lozenge in exactly one third of the lozenge tilings. -/
def centralLozengeOneThird : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    3 * Nat.card {M : (hexagonGraph (2 * n - 1) (2 * n) (2 * n - 1)).Subgraph //
        M.IsPerfectMatching ∧ ∀ s t, s.1 = (0, 2 * (n : ℤ) - 1, false) →
          t.1 = (-1, 2 * (n : ℤ) - 1, true) → M.Adj s t} =
      Nat.card {M : (hexagonGraph (2 * n - 1) (2 * n) (2 * n - 1)).Subgraph // M.IsPerfectMatching}

end

/-! ### The cells of the dual honeycomb

Place the downward triangle `(i,j)` in cell `(i+1,j)`, and the upward triangle in
cell `(i,j)`. This turns the same-cell lozenges into the reference matching on the
interior; every other lozenge advances by one column. -/

section Honeycomb

private abbrev Cell := ℤ × ℤ

private abbrev Vertex (k : ℤ) := {v : LatticeTriangle // InHexagon k (k + 1) k v}

private def inStrip (k : ℤ) (p : Cell) : Prop :=
  0 ≤ p.2 ∧ p.2 ≤ 2 * k ∧ 0 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 2 * k

private def upCell (k : ℤ) (p : Cell) : Prop :=
  inStrip k p ∧ -k ≤ p.1 ∧ p.1 < k

private def downCell (k : ℤ) (p : Cell) : Prop :=
  inStrip k p ∧ -k < p.1 ∧ p.1 ≤ k

private def advances (p q : Cell) : Prop :=
  q.1 = p.1 + 1 ∧ (q.2 = p.2 ∨ q.2 = p.2 - 1)

private lemma inHexagon_up (k : ℤ) (p : Cell) :
    InHexagon k (k + 1) k (p.1, p.2, false) ↔ upCell k p := by
  rcases p with ⟨x, y⟩
  simp only [InHexagon, upCell, inStrip]
  omega

private lemma inHexagon_down (k : ℤ) (p : Cell) :
    InHexagon k (k + 1) k (p.1 - 1, p.2, true) ↔ downCell k p := by
  rcases p with ⟨x, y⟩
  simp only [InHexagon, downCell, inStrip]
  omega

private def up {k : ℤ} {p : Cell} (h : upCell k p) : Vertex k :=
  ⟨(p.1, p.2, false), (inHexagon_up k p).mpr h⟩

private def down {k : ℤ} {p : Cell} (h : downCell k p) : Vertex k :=
  ⟨(p.1 - 1, p.2, true), (inHexagon_down k p).mpr h⟩

private lemma up_inj {k : ℤ} {p q : Cell} {hp : upCell k p} {hq : upCell k q}
    (h : up hp = up hq) : p = q := by
  have he := congrArg Subtype.val h
  rcases p with ⟨x, y⟩
  rcases q with ⟨a, b⟩
  simpa [up] using he

private lemma down_inj {k : ℤ} {p q : Cell} {hp : downCell k p} {hq : downCell k q}
    (h : down hp = down hq) : p = q := by
  have he := congrArg Subtype.val h
  rcases p with ⟨x, y⟩
  rcases q with ⟨a, b⟩
  simp only [down, Prod.mk.injEq, sub_left_inj, and_true] at he
  exact Prod.ext he.1 he.2

private lemma vertex_cases {k : ℤ} (v : Vertex k) :
    (∃ (p : Cell) (h : upCell k p), v = up h) ∨
      ∃ (p : Cell) (h : downCell k p), v = down h := by
  rcases v with ⟨⟨i, j, b⟩, hv⟩
  cases b
  · exact Or.inl ⟨(i, j), (inHexagon_up k (i, j)).mp hv, rfl⟩
  · have he : i + 1 - 1 = i := by omega
    have h : downCell k (i + 1, j) := by
      apply (inHexagon_down k (i + 1, j)).mp
      simpa only [he] using hv
    refine Or.inr ⟨(i + 1, j), h, Subtype.ext ?_⟩
    simp [down, he]

private lemma adj_up_down {k : ℤ} {p q : Cell} (hp : upCell k p) (hq : downCell k q) :
    (hexagonGraph k (k + 1) k).Adj (up hp) (down hq) ↔ q = p ∨ advances p q := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨a, b⟩
  rw [hexagonGraph, SimpleGraph.fromRel_adj]
  simp only [up, down, SharesEdge, or_false, Prod.mk.injEq, advances]
  constructor
  · grind
  · intro h
    refine ⟨fun he ↦ ?_, by grind⟩
    have hb := congrArg (fun v : Vertex k ↦ v.val.2.2) he
    exact Bool.false_ne_true hb

private lemma not_adj_up_up {k : ℤ} {p q : Cell} (hp : upCell k p) (hq : upCell k q) :
    ¬(hexagonGraph k (k + 1) k).Adj (up hp) (up hq) := by
  rw [hexagonGraph, SimpleGraph.fromRel_adj]
  rcases p with ⟨x, y⟩
  rcases q with ⟨a, b⟩
  simp [up, SharesEdge]

private lemma not_adj_down_down {k : ℤ} {p q : Cell} (hp : downCell k p) (hq : downCell k q) :
    ¬(hexagonGraph k (k + 1) k).Adj (down hp) (down hq) := by
  rw [hexagonGraph, SimpleGraph.fromRel_adj]
  rcases p with ⟨x, y⟩
  rcases q with ⟨a, b⟩
  simp [down, SharesEdge]

private lemma down_of_up {k : ℤ} {p : Cell} (hp : upCell k p) (hx : -k < p.1) :
    downCell k p := ⟨hp.1, hx, hp.2.2.le⟩

private lemma up_of_down {k : ℤ} {p : Cell} (hp : downCell k p) (hx : p.1 < k) :
    upCell k p := ⟨hp.1, hp.2.1.le, hx⟩

private lemma center_up {k : ℤ} (hk : 0 < k) : upCell k (0, k) := by
  simp [upCell, inStrip]
  omega

private lemma center_down {k : ℤ} (hk : 0 < k) : downCell k (0, k) :=
  down_of_up (center_up hk) (by omega)

private lemma marked_iff_center {k : ℤ} (hk : 0 < k)
    (M : (hexagonGraph k (k + 1) k).Subgraph) :
    (∀ s t, s.val = (0, k, false) → t.val = (-1, k, true) → M.Adj s t) ↔
      M.Adj (up (center_up hk)) (down (center_down hk)) := by
  constructor
  · intro h
    exact h _ _ rfl rfl
  · intro h s t hs ht
    rwa [show s = up (center_up hk) from Subtype.ext hs,
      show t = down (center_down hk) from Subtype.ext ht]

private lemma finite_vertex (k : ℤ) : Finite (Vertex k) := by
  let f : Vertex k → Set.Icc (-k) (k - 1) × Set.Icc (0 : ℤ) (2 * k) × Bool := fun v ↦
    let h : 0 ≤ v.val.2.1 ∧ v.val.2.1 ≤ 2 * k ∧ -k ≤ v.val.1 ∧ v.val.1 ≤ k - 1 := by
      rcases v with ⟨⟨i, j, b⟩, hv⟩
      cases b <;> simp only [InHexagon] at hv <;> dsimp <;> omega
    (⟨v.val.1, h.2.2⟩, ⟨v.val.2.1, h.1, h.2.1⟩, v.val.2.2)
  refine Finite.of_injective f fun v w h ↦ Subtype.ext ?_
  exact Prod.ext (congrArg (fun z ↦ z.1.val) h)
    (Prod.ext (congrArg (fun z ↦ z.2.1.val) h) (congrArg (fun z ↦ z.2.2) h))

private lemma finite_subgraphs (k : ℤ) : Finite (hexagonGraph k (k + 1) k).Subgraph := by
  let := finite_vertex k
  let f : (hexagonGraph k (k + 1) k).Subgraph → Set (Vertex k) × Set (Vertex k × Vertex k) :=
    fun M ↦ (M.verts, {p | M.Adj p.1 p.2})
  apply Finite.of_injective f
  intro M N h
  apply SimpleGraph.Subgraph.ext
  · exact congrArg Prod.fst h
  · funext s t
    exact congrArg (fun z : Set (Vertex k) × Set (Vertex k × Vertex k) ↦ (s, t) ∈ z.2) h

private abbrev Perfect (k : ℤ) := {M : (hexagonGraph k (k + 1) k).Subgraph // M.IsPerfectMatching}

private lemma existsUnique_next {k : ℤ} (M : Perfect k) {p : Cell} (hp : upCell k p) :
    ∃! q : Cell, ∃ hq : downCell k q, M.val.Adj (up hp) (down hq) := by
  obtain ⟨w, hw, hu⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp M.property (up hp)
  rcases vertex_cases w with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
  · exact (not_adj_up_up hp hq hw.adj_sub).elim
  · refine ⟨q, ⟨hq, hw⟩, ?_⟩
    rintro s ⟨hs, hsM⟩
    exact down_inj (hu _ hsM)

private lemma existsUnique_prev {k : ℤ} (M : Perfect k) {q : Cell} (hq : downCell k q) :
    ∃! p : Cell, ∃ hp : upCell k p, M.val.Adj (up hp) (down hq) := by
  obtain ⟨w, hw, hu⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp M.property (down hq)
  rcases vertex_cases w with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · refine ⟨p, ⟨hp, hw.symm⟩, ?_⟩
    rintro s ⟨hs, hsM⟩
    exact up_inj (hu _ hsM.symm)
  · exact (not_adj_down_down hq hp hw.adj_sub).elim


/-! ### From a perfect matching to directed tracks

An interior cell has both colors. If a track reaches its downward triangle from the left,
the upward triangle cannot be matched to that same downward triangle and must continue right. -/

private def chosenEdge {k : ℤ} (M : Perfect k) (p q : Cell) : Prop :=
  ∃ (hp : upCell k p) (hq : downCell k q), M.val.Adj (up hp) (down hq)

private lemma chosenEdge_unique_target {k : ℤ} {M : Perfect k} {p q r : Cell}
    (hq : chosenEdge M p q) (hr : chosenEdge M p r) : q = r := by
  obtain ⟨_, hq, hq'⟩ := hq
  obtain ⟨_, hr, hr'⟩ := hr
  exact down_inj (M.property.1.eq_of_adj_left hq' hr')

private lemma chosenEdge_unique_source {k : ℤ} {M : Perfect k} {p q r : Cell}
    (hp : chosenEdge M p r) (hq : chosenEdge M q r) : p = q := by
  obtain ⟨_, _, hp'⟩ := hp
  obtain ⟨_, _, hq'⟩ := hq
  exact up_inj (M.property.1.eq_of_adj_right hp' hq')

private lemma chosenEdge_advance_or_eq {k : ℤ} {M : Perfect k} {p q : Cell}
    (h : chosenEdge M p q) : q = p ∨ advances p q := by
  obtain ⟨hp, hq, hadj⟩ := h
  exact (adj_up_down hp hq).mp hadj.adj_sub

private lemma outgoing_of_up {k : ℤ} (M : Perfect k) {p : Cell} (hp : upCell k p) :
    ∃ q, chosenEdge M p q := by
  obtain ⟨q, ⟨hq, hadj⟩, _⟩ := existsUnique_next M hp
  exact ⟨q, hp, hq, hadj⟩

private lemma incoming_of_down {k : ℤ} (M : Perfect k) {q : Cell} (hq : downCell k q) :
    ∃ p, chosenEdge M p q := by
  obtain ⟨p, ⟨hp, hadj⟩, _⟩ := existsUnique_prev M hq
  exact ⟨p, hp, hq, hadj⟩

private lemma advance_of_incoming {k : ℤ} {M : Perfect k} {p q r : Cell}
    (hpq : chosenEdge M p q) (hqr : chosenEdge M q r) (hpq' : advances p q) : advances q r := by
  rcases chosenEdge_advance_or_eq hqr with rfl | h
  · have he := chosenEdge_unique_source hpq hqr
    exact (by have := hpq'.1; rw [he] at this; omega : False).elim
  · exact h

private lemma advance_of_outgoing {k : ℤ} {M : Perfect k} {p q r : Cell}
    (hpq : chosenEdge M p q) (hqr : chosenEdge M q r) (hqr' : advances q r) : advances p q := by
  rcases chosenEdge_advance_or_eq hpq with he | h
  · subst p
    have he := chosenEdge_unique_target hpq hqr
    exact (by have := hqr'.1; rw [← he] at this; omega : False).elim
  · exact h

private def source (k : ℕ) (i : Fin (k + 1)) : Cell := (-(k : ℤ), (k : ℤ) + i.val)

private def sink (k : ℕ) (i : Fin (k + 1)) : Cell := ((k : ℤ), i.val)

private lemma source_up {k : ℕ} (hk : 0 < k) (i : Fin (k + 1)) : upCell k (source k i) := by
  have hi := i.isLt
  dsimp [source, upCell, inStrip]
  omega

private lemma sink_down {k : ℕ} (hk : 0 < k) (i : Fin (k + 1)) : downCell k (sink k i) := by
  have hi := i.isLt
  dsimp [sink, downCell, inStrip]
  omega

private lemma source_index {k : ℕ} {p : Cell} (hp : inStrip k p) (hx : p.1 = -(k : ℤ)) :
    ∃ i, p = source k i := by
  obtain ⟨x, y⟩ := p
  change x = -(k : ℤ) at hx
  subst x
  rcases hp with ⟨_, h₂, h₃, _⟩
  have h₄ : 0 ≤ y - k := by omega
  let i : Fin (k + 1) := ⟨(y - k).toNat, by omega⟩
  refine ⟨i, Prod.ext rfl ?_⟩
  change y = (k : ℤ) + ((y - k).toNat : ℤ)
  omega

private lemma sink_index {k : ℕ} {p : Cell} (hp : inStrip k p) (hx : p.1 = k) :
    ∃ i, p = sink k i := by
  obtain ⟨x, y⟩ := p
  change x = (k : ℤ) at hx
  subst x
  rcases hp with ⟨h₁, _, _, h₄⟩
  let i : Fin (k + 1) := ⟨y.toNat, by omega⟩
  exact ⟨i, Prod.ext rfl (by change y = (y.toNat : ℤ); omega)⟩

private noncomputable def nextCell {k : ℤ} (M : Perfect k) (p : Cell) : Cell := by
  classical
  exact if h : ∃ q, chosenEdge M p q then h.choose else p

private lemma chosenEdge_nextCell {k : ℤ} (M : Perfect k) {p : Cell} (hp : upCell k p) :
    chosenEdge M p (nextCell M p) := by
  classical
  rw [nextCell, dite_eq_left (outgoing_of_up M hp)]
  exact (outgoing_of_up M hp).choose_spec

private noncomputable def track {k : ℕ} (M : Perfect k) (i : Fin (k + 1)) : ℕ → Cell
  | 0 => source k i
  | t + 1 => nextCell M (track M i t)

private lemma track_step {k : ℕ} (hk : 0 < k) (M : Perfect k) (i : Fin (k + 1)) :
    ∀ t < 2 * k,
      (track M i t).1 = (t : ℤ) - k ∧
        chosenEdge M (track M i t) (track M i (t + 1)) ∧
          advances (track M i t) (track M i (t + 1)) := by
  intro t
  induction t with
  | zero =>
    intro _
    have hp : upCell k (source k i) := source_up hk i
    have hc := chosenEdge_nextCell M hp
    refine ⟨by simp [track, source], hc, ?_⟩
    rcases chosenEdge_advance_or_eq hc with he | ha
    · obtain ⟨_, hq, _⟩ := hc
      rw [he] at hq
      exact (lt_irrefl _ hq.2.1).elim
    · exact ha
  | succ t ih =>
    intro ht
    obtain ⟨hx, hc, ha⟩ := ih (by omega)
    have hx' : (track M i (t + 1)).1 = ((t + 1 : ℕ) : ℤ) - k := by
      rw [ha.1, hx]
      omega
    have hd : downCell k (track M i (t + 1)) := by
      obtain ⟨_, hd, _⟩ := hc
      exact hd
    have hu := up_of_down hd (by omega)
    have hn := chosenEdge_nextCell M hu
    exact ⟨hx', hn, advance_of_incoming hc hn ha⟩

private lemma track_inStrip {k : ℕ} (hk : 0 < k) (M : Perfect k) (i : Fin (k + 1))
    {t : ℕ} (ht : t ≤ 2 * k) : inStrip k (track M i t) := by
  cases t with
  | zero => exact (source_up hk i).1
  | succ t =>
    have hs := (track_step hk M i t (by omega)).2.1
    obtain ⟨_, h, _⟩ := hs
    exact h.1

private lemma track_column {k : ℕ} (hk : 0 < k) (M : Perfect k) (i : Fin (k + 1))
    {t : ℕ} (ht : t ≤ 2 * k) : (track M i t).1 = (t : ℤ) - k := by
  cases t with
  | zero => simp [track, source]
  | succ t =>
    have h := track_step hk M i t (by omega)
    rw [h.2.2.1, h.1]
    omega

private lemma track_distinct {k : ℕ} (hk : 0 < k) (M : Perfect k) {i j : Fin (k + 1)}
    (hij : i ≠ j) {t : ℕ} (ht : t ≤ 2 * k) : track M i t ≠ track M j t := by
  induction t with
  | zero =>
    intro h
    apply hij
    apply Fin.ext
    have he := congrArg Prod.snd h
    change (k : ℤ) + i.val = (k : ℤ) + j.val at he
    omega
  | succ t ih =>
    intro h
    apply ih (by omega)
    have hi := (track_step hk M i t (by omega)).2.1
    have hj := (track_step hk M j t (by omega)).2.1
    rw [← h] at hj
    exact chosenEdge_unique_source hi hj

private lemma track_sink {k : ℕ} (hk : 0 < k) (M : Perfect k) (i : Fin (k + 1)) :
    ∃ j, track M i (2 * k) = sink k j := by
  refine sink_index (track_inStrip hk M i le_rfl) ((track_column hk M i le_rfl).trans ?_)
  omega

private lemma track_height_lt {k : ℕ} (hk : 0 < k) (M : Perfect k) {i j : Fin (k + 1)}
    (hij : i < j) {t : ℕ} (ht : t ≤ 2 * k) : (track M i t).2 < (track M j t).2 := by
  induction t with
  | zero =>
    have hij' : i.val < j.val := hij
    change (k : ℤ) + i.val < (k : ℤ) + j.val
    omega
  | succ t ih =>
    have hlt := ih (by omega)
    have hi := (track_step hk M i t (by omega)).2.2.2
    have hj := (track_step hk M j t (by omega)).2.2.2
    have hx := (track_column hk M i ht).trans (track_column hk M j ht).symm
    have hne := track_distinct hk M (ne_of_lt hij) ht
    have hy : (track M i (t + 1)).2 ≠ (track M j (t + 1)).2 := fun he ↦ hne (Prod.ext hx he)
    omega

private lemma strictMono_fin_lower {m : ℕ} {f : Fin m → Fin m} (hf : StrictMono f)
    (t : ℕ) (ht : t < m) : t ≤ (f ⟨t, ht⟩).val := by
  induction t with
  | zero => exact Nat.zero_le _
  | succ t ih =>
    have ht' : t < m := by omega
    have hi := ih ht'
    have hh : (f ⟨t, ht'⟩).val < (f ⟨t + 1, ht⟩).val := hf (show t < t + 1 by omega)
    omega

private lemma strictMono_fin_eq {m : ℕ} {f : Fin m → Fin m} (hf : StrictMono f) (i : Fin m) :
    f i = i := by
  have h₁ := strictMono_fin_lower hf i.val i.isLt
  change i.val ≤ (f i).val at h₁
  let g : Fin m → Fin m := fun j ↦ (f j.rev).rev
  have hg : StrictMono g := fun a b hab ↦ Fin.rev_lt_rev.mpr (hf (Fin.rev_lt_rev.mpr hab))
  have h₂ := strictMono_fin_lower hg i.rev.val i.rev.isLt
  change i.rev.val ≤ (f i.rev.rev).rev.val at h₂
  rw [Fin.rev_rev] at h₂
  simp only [Fin.val_rev] at h₂
  apply Fin.ext
  have hi := i.isLt
  have hf' := (f i).isLt
  omega

private lemma track_ends {k : ℕ} (hk : 0 < k) (M : Perfect k) (i : Fin (k + 1)) :
    track M i (2 * k) = sink k i := by
  classical
  choose f hf using track_sink hk M
  have hmono : StrictMono f := by
    intro a b hab
    have h := track_height_lt hk M hab (t := 2 * k) le_rfl
    rw [hf, hf] at h
    change ((f a).val : ℤ) < (f b).val at h
    exact_mod_cast h
  simpa only [strictMono_fin_eq hmono] using hf i

/-- Every nonreference edge is encountered from some source, including at the left boundary. -/
private lemma track_covers {k : ℕ} (M : Perfect k) (t : ℕ) {p q : Cell}
    (hx : p.1 = (t : ℤ) - k) (he : chosenEdge M p q) (ha : advances p q) :
    ∃ i, track M i t = p ∧ track M i (t + 1) = q := by
  induction t generalizing p q with
  | zero =>
    have hu : upCell k p := by obtain ⟨hu, _, _⟩ := he; exact hu
    obtain ⟨i, rfl⟩ := source_index hu.1 (by omega)
    exact ⟨i, rfl, chosenEdge_unique_target (chosenEdge_nextCell M hu) he⟩
  | succ t ih =>
    have hu : upCell k p := by obtain ⟨hu, _, _⟩ := he; exact hu
    have hd := down_of_up hu (by omega)
    obtain ⟨r, hr⟩ := incoming_of_down M hd
    have hra := advance_of_outgoing hr he ha
    have hrx : r.1 = (t : ℤ) - k := by have := hra.1; omega
    obtain ⟨i, _, hip⟩ := ih hrx hr hra
    refine ⟨i, hip, ?_⟩
    change nextCell M (track M i (t + 1)) = q
    rw [hip]
    exact chosenEdge_unique_target (chosenEdge_nextCell M hu) he

private lemma track_avoids_iff_center {k : ℕ} (hk : 0 < k) (M : Perfect k) :
    (∀ i : Fin (k + 1), track M i k ≠ (0, (k : ℤ))) ↔
      M.val.Adj (up (center_up (by exact_mod_cast hk)))
        (down (center_down (by exact_mod_cast hk))) := by
  constructor
  · intro hAvoid
    have hu : upCell k (0, k) := center_up (by exact_mod_cast hk)
    obtain ⟨q, hq⟩ := outgoing_of_up M hu
    rcases chosenEdge_advance_or_eq hq with rfl | ha
    · obtain ⟨_, _, hm⟩ := hq
      exact hm
    · obtain ⟨i, hi, _⟩ := track_covers M k (p := (0, (k : ℤ))) (by simp) hq ha
      exact (hAvoid i hi).elim
  · intro h i hi
    have he : chosenEdge M (0, k) (0, k) := ⟨_, _, h⟩
    have hs := (track_step hk M i k (by omega)).2
    rw [hi] at hs
    have eq := chosenEdge_unique_target hs.1 he
    have hh := hs.2.1
    rw [eq] at hh
    simp at hh

/-- The bounded track data determines all matching edges, including the reference edges. -/
private lemma chosenEdge_of_track_eq {k : ℕ} (hk : 0 < k) {M N : Perfect k}
    (h : ∀ (i : Fin (k + 1)) (t : ℕ), t ≤ 2 * k → track M i t = track N i t)
    {p q : Cell} (he : chosenEdge M p q) : chosenEdge N p q := by
  have hu : upCell k p := by obtain ⟨hp, _, _⟩ := he; exact hp
  let t := (p.1 + (k : ℤ)).toNat
  have hx : p.1 = (t : ℤ) - k := by
    have h₁ := hu.2.1
    dsimp [t]
    omega
  have ht : t < 2 * k := by have := hu.2.2; omega
  rcases chosenEdge_advance_or_eq he with rfl | ha
  · obtain ⟨r, hr⟩ := outgoing_of_up N hu
    rcases chosenEdge_advance_or_eq hr with rfl | har
    · exact hr
    · obtain ⟨i, hp, hq⟩ := track_covers N t hx hr har
      have hn := (track_step hk M i t ht).2.1
      rw [h i t ht.le, h i (t + 1) (by omega), hp, hq] at hn
      have hrp := chosenEdge_unique_target hn he
      have hcol := har.1
      rw [hrp] at hcol
      omega
  · obtain ⟨i, hp, hq⟩ := track_covers M t hx he ha
    have hn := (track_step hk N i t ht).2.1
    rwa [← h i t ht.le, ← h i (t + 1) (by omega), hp, hq] at hn

private lemma perfect_eq_of_chosenEdge {k : ℤ} {M N : Perfect k}
    (h : ∀ p q : Cell, chosenEdge M p q ↔ chosenEdge N p q) : M = N := by
  have adj {p q : Cell} (hp : upCell k p) (hq : downCell k q) :
      M.val.Adj (up hp) (down hq) ↔ N.val.Adj (up hp) (down hq) := by
    constructor
    · intro hm
      obtain ⟨_, _, hn⟩ := (h p q).mp ⟨hp, hq, hm⟩
      exact hn
    · intro hn
      obtain ⟨_, _, hm⟩ := (h p q).mpr ⟨hp, hq, hn⟩
      exact hm
  apply Subtype.ext
  apply SimpleGraph.Subgraph.ext
  · exact M.property.2.verts_eq_univ.trans N.property.2.verts_eq_univ.symm
  · funext v w
    apply propext
    rcases vertex_cases v with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ <;>
      rcases vertex_cases w with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact ⟨fun hM ↦ (not_adj_up_up hp hq hM.adj_sub).elim,
        fun hN ↦ (not_adj_up_up hp hq hN.adj_sub).elim⟩
    · exact adj hp hq
    · rw [M.val.adj_comm, N.val.adj_comm]
      exact adj hq hp
    · exact ⟨fun hM ↦ (not_adj_down_down hp hq hM.adj_sub).elim,
        fun hN ↦ (not_adj_down_down hp hq hN.adj_sub).elim⟩

private lemma track_injective {k : ℕ} (hk : 0 < k) :
    Function.Injective (fun (M : Perfect k) (i : Fin (k + 1)) (t : Fin (2 * k + 1)) ↦
      track M i t) := by
  intro M N h
  have h' (i : Fin (k + 1)) (t : ℕ) (ht : t ≤ 2 * k) : track M i t = track N i t :=
    congrFun (congrFun h i) ⟨t, by omega⟩
  apply perfect_eq_of_chosenEdge
  intro p q
  exact ⟨chosenEdge_of_track_eq hk h', chosenEdge_of_track_eq hk (fun i t ht ↦ (h' i t ht).symm)⟩

/-! ### A disjoint track family determines a spanning matching -/

private structure StripPath (k : ℕ) (i j : Fin (k + 1)) where
  cell : Fin (2 * k + 1) → Cell
  column : ∀ t, (cell t).1 = (t.val : ℤ) - k
  strip : ∀ t, inStrip k (cell t)
  first : cell 0 = source k i
  last : cell (Fin.last (2 * k)) = sink k j
  step : ∀ (t : ℕ) (ht : t < 2 * k),
    advances (cell ⟨t, by omega⟩) (cell ⟨t + 1, by omega⟩)

private lemma StripPath.ext_cell {k : ℕ} {i j : Fin (k + 1)} {P Q : StripPath k i j}
    (h : P.cell = Q.cell) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

private structure TrackFamily (k : ℕ) where
  path : ∀ i : Fin (k + 1), StripPath k i i
  disjoint : ∀ ⦃i j⦄, i ≠ j → ∀ t, (path i).cell t ≠ (path j).cell t

private lemma TrackFamily.ext_cell {k : ℕ} {F G : TrackFamily k}
    (h : ∀ i t, (F.path i).cell t = (G.path i).cell t) : F = G := by
  have he : F.path = G.path := funext fun i ↦ StripPath.ext_cell (funext (h i))
  cases F
  cases G
  cases he
  rfl

private noncomputable def tracksOf {k : ℕ} (hk : 0 < k) (M : Perfect k) : TrackFamily k where
  path i := {
    cell := fun t ↦ track M i t.val
    column := fun t ↦ track_column hk M i (by have := t.isLt; omega)
    strip := fun t ↦ track_inStrip hk M i (by have := t.isLt; omega)
    first := rfl
    last := track_ends hk M i
    step := fun t ht ↦ (track_step hk M i t ht).2.2 }
  disjoint := fun _ _ hij t ↦ track_distinct hk M hij (by have := t.isLt; omega)

private lemma track_location {k : ℕ} {F : TrackFamily k} {i j : Fin (k + 1)}
    {s t : Fin (2 * k + 1)} (h : (F.path i).cell s = (F.path j).cell t) : i = j ∧ s = t := by
  have hx := congrArg Prod.fst h
  rw [(F.path i).column, (F.path j).column] at hx
  have he : s = t := Fin.ext (by omega)
  subst t
  exact ⟨Classical.byContradiction fun hn ↦ F.disjoint hn s h, rfl⟩

private def visited {k : ℕ} (F : TrackFamily k) (p : Cell) : Prop :=
  ∃ i t, (F.path i).cell t = p

private def trackEdge {k : ℕ} (F : TrackFamily k) (p q : Cell) : Prop :=
  ∃ (i : Fin (k + 1)) (t : ℕ) (ht : t < 2 * k),
    (F.path i).cell ⟨t, by omega⟩ = p ∧ (F.path i).cell ⟨t + 1, by omega⟩ = q

private def paired {k : ℕ} (F : TrackFamily k) (p q : Cell) : Prop :=
  trackEdge F p q ∨ (q = p ∧ ¬visited F p)

private lemma trackEdge_advances {k : ℕ} {F : TrackFamily k} {p q : Cell}
    (h : trackEdge F p q) : advances p q := by
  obtain ⟨i, t, ht, hp, hq⟩ := h
  simpa only [hp, hq] using (F.path i).step t ht

private lemma trackEdge_visits {k : ℕ} {F : TrackFamily k} {p q : Cell}
    (h : trackEdge F p q) : visited F p ∧ visited F q := by
  obtain ⟨i, t, ht, hp, hq⟩ := h
  exact ⟨⟨i, ⟨t, by omega⟩, hp⟩, ⟨i, ⟨t + 1, by omega⟩, hq⟩⟩

private lemma trackEdge_unique_target {k : ℕ} {F : TrackFamily k} {p q r : Cell}
    (hq : trackEdge F p q) (hr : trackEdge F p r) : q = r := by
  obtain ⟨i, s, hs, hp, hq⟩ := hq
  obtain ⟨j, t, ht, hp', hr⟩ := hr
  obtain ⟨hij, hst⟩ := track_location (F := F) (hp.trans hp'.symm)
  have hh := congrArg Fin.val hst
  change s = t at hh
  subst j
  subst t
  exact hq.symm.trans hr

private lemma trackEdge_unique_source {k : ℕ} {F : TrackFamily k} {p q r : Cell}
    (hp : trackEdge F p r) (hq : trackEdge F q r) : p = q := by
  obtain ⟨i, s, hs, hp, hr⟩ := hp
  obtain ⟨j, t, ht, hq, hr'⟩ := hq
  obtain ⟨hij, hst⟩ := track_location (F := F) (hr.trans hr'.symm)
  have hh := congrArg Fin.val hst
  change s + 1 = t + 1 at hh
  have : s = t := by omega
  subst j
  subst t
  exact hp.symm.trans hq

private lemma paired_unique_target {k : ℕ} {F : TrackFamily k} {p q r : Cell}
    (hq : paired F p q) (hr : paired F p r) : q = r := by
  rcases hq with hq | ⟨hq, hnu⟩ <;> rcases hr with hr | ⟨hr, hnv⟩
  · exact trackEdge_unique_target hq hr
  · exact (hnv (trackEdge_visits hq).1).elim
  · exact (hnu (trackEdge_visits hr).1).elim
  · exact hq.trans hr.symm

private lemma paired_unique_source {k : ℕ} {F : TrackFamily k} {p q r : Cell}
    (hp : paired F p r) (hq : paired F q r) : p = q := by
  rcases hp with hp | ⟨hp, hnu⟩ <;> rcases hq with hq | ⟨hq, hnv⟩
  · exact trackEdge_unique_source hp hq
  · exact (hnv (hq ▸ (trackEdge_visits hp).2)).elim
  · exact (hnu (hp ▸ (trackEdge_visits hq).2)).elim
  · exact hp.symm.trans hq

private lemma visited_source {k : ℕ} {F : TrackFamily k} {p : Cell}
    (hp : inStrip k p) (hx : p.1 = -(k : ℤ)) : visited F p := by
  obtain ⟨i, rfl⟩ := source_index hp hx
  exact ⟨i, 0, (F.path i).first⟩

private lemma visited_sink {k : ℕ} {F : TrackFamily k} {p : Cell}
    (hp : inStrip k p) (hx : p.1 = k) : visited F p := by
  obtain ⟨i, rfl⟩ := sink_index hp hx
  exact ⟨i, Fin.last (2 * k), (F.path i).last⟩

private lemma paired_target {k : ℕ} (F : TrackFamily k) {p : Cell} (hp : upCell k p) :
    ∃ q, downCell k q ∧ paired F p q := by
  by_cases hv : visited F p
  · obtain ⟨i, t, he⟩ := hv
    have hx := (F.path i).column t
    rw [he] at hx
    have ht : t.val < 2 * k := by have := hp.2.2; omega
    let s : Fin (2 * k + 1) := ⟨t.val + 1, by omega⟩
    have hs := (F.path i).column s
    change ((F.path i).cell s).1 = ((t.val + 1 : ℕ) : ℤ) - k at hs
    refine ⟨(F.path i).cell s, ⟨(F.path i).strip s, by omega, by omega⟩, Or.inl ?_⟩
    exact ⟨i, t.val, ht, he, rfl⟩
  · have hx : -(k : ℤ) < p.1 := by
      rcases hp with ⟨hs, hl, _⟩
      exact lt_of_le_of_ne hl (fun h ↦ hv (visited_source hs h.symm))
    exact ⟨p, down_of_up hp hx, Or.inr ⟨rfl, hv⟩⟩

private lemma paired_source {k : ℕ} (F : TrackFamily k) {q : Cell} (hq : downCell k q) :
    ∃ p, upCell k p ∧ paired F p q := by
  by_cases hv : visited F q
  · obtain ⟨i, t, he⟩ := hv
    have hx := (F.path i).column t
    rw [he] at hx
    have ht₀ : 0 < t.val := by have := hq.2.1; omega
    have ht : t.val - 1 < 2 * k := by have := t.isLt; omega
    let s : Fin (2 * k + 1) := ⟨t.val - 1, by omega⟩
    have hs := (F.path i).column s
    change ((F.path i).cell s).1 = ((t.val - 1 : ℕ) : ℤ) - k at hs
    refine ⟨(F.path i).cell s, ⟨(F.path i).strip s, by omega, by omega⟩, Or.inl ?_⟩
    refine ⟨i, t.val - 1, ht, rfl, ?_⟩
    have ht' : (⟨t.val - 1 + 1, by omega⟩ : Fin (2 * k + 1)) = t := Fin.ext (by
      change t.val - 1 + 1 = t.val
      omega)
    rwa [ht']
  · have hx : q.1 < (k : ℤ) := by
      rcases hq with ⟨hs, _, hr⟩
      exact lt_of_le_of_ne hr (fun h ↦ hv (visited_sink hs h))
    exact ⟨q, up_of_down hq hx, Or.inr ⟨rfl, hv⟩⟩

private def cellOf {k : ℤ} (v : Vertex k) : Cell :=
  (v.val.1 + if v.val.2.2 then 1 else 0, v.val.2.1)

private def reconstructedAdj {k : ℕ} (F : TrackFamily k) (v w : Vertex k) : Prop :=
  (v.val.2.2 = false ∧ w.val.2.2 = true ∧ paired F (cellOf v) (cellOf w)) ∨
  (w.val.2.2 = false ∧ v.val.2.2 = true ∧ paired F (cellOf w) (cellOf v))

private lemma reconstructed_up_down {k : ℕ} (F : TrackFamily k) {p q : Cell}
    (hp : upCell k p) (hq : downCell k q) :
    reconstructedAdj F (up hp) (down hq) ↔ paired F p q := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨a, b⟩
  simp [reconstructedAdj, cellOf, up, down]

private lemma reconstructed_symm {k : ℕ} {F : TrackFamily k} {v w : Vertex k}
    (h : reconstructedAdj F v w) : reconstructedAdj F w v := h.symm

private def reconstructed {k : ℕ} (F : TrackFamily k) : (hexagonGraph k (k + 1) k).Subgraph where
  verts := Set.univ
  Adj := reconstructedAdj F
  adj_sub {v w} h := by
    have aux {p q : Cell} (hp : upCell k p) (hq : downCell k q)
        (ha : reconstructedAdj F (up hp) (down hq)) :
        (hexagonGraph k (k + 1) k).Adj (up hp) (down hq) := by
      apply (adj_up_down hp hq).mpr
      rcases (reconstructed_up_down F hp hq).mp ha with he | ⟨he, _⟩
      · exact Or.inr (trackEdge_advances he)
      · exact Or.inl he
    rcases vertex_cases v with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ <;>
      rcases vertex_cases w with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · simp [reconstructedAdj, up] at h
    · exact aux hp hq h
    · exact (aux hq hp (reconstructed_symm h)).symm
    · simp [reconstructedAdj, down] at h
  edge_vert _ := Set.mem_univ _
  symm := ⟨fun _ _ h ↦ reconstructed_symm h⟩

private lemma reconstructed_perfect {k : ℕ} (F : TrackFamily k) :
    (reconstructed F).IsPerfectMatching := by
  apply SimpleGraph.Subgraph.isPerfectMatching_iff.mpr
  intro v
  rcases vertex_cases v with ⟨p, hp, rfl⟩ | ⟨q, hq, rfl⟩
  · obtain ⟨q, hq, hpq⟩ := paired_target F hp
    refine ⟨down hq, (reconstructed_up_down F hp hq).mpr hpq, ?_⟩
    intro w hw
    change reconstructedAdj F (up hp) w at hw
    rcases vertex_cases w with ⟨p', hp', rfl⟩ | ⟨q', hq', rfl⟩
    · simp [reconstructedAdj, up] at hw
    · have he := paired_unique_target ((reconstructed_up_down F hp hq').mp hw) hpq
      subst q'
      rfl
  · obtain ⟨p, hp, hpq⟩ := paired_source F hq
    refine ⟨up hp, reconstructed_symm ((reconstructed_up_down F hp hq).mpr hpq), ?_⟩
    intro w hw
    change reconstructedAdj F (down hq) w at hw
    rcases vertex_cases w with ⟨p', hp', rfl⟩ | ⟨q', hq', rfl⟩
    · have he := paired_unique_source
        ((reconstructed_up_down F hp' hq).mp (reconstructed_symm hw)) hpq
      subst p'
      rfl
    · simp [reconstructedAdj, down] at hw

private def matchingOf {k : ℕ} (F : TrackFamily k) : Perfect k :=
  ⟨reconstructed F, reconstructed_perfect F⟩

private lemma track_matchingOf {k : ℕ} (F : TrackFamily k) (i : Fin (k + 1))
    (t : ℕ) (ht : t ≤ 2 * k) : track (matchingOf F) i t = (F.path i).cell ⟨t, by omega⟩ := by
  induction t with
  | zero => exact (F.path i).first.symm
  | succ t ih =>
    have ht' : t < 2 * k := by omega
    let p := (F.path i).cell ⟨t, by omega⟩
    let q := (F.path i).cell ⟨t + 1, by omega⟩
    have hx : p.1 = (t : ℤ) - k := (F.path i).column _
    have hy : q.1 = ((t + 1 : ℕ) : ℤ) - k := (F.path i).column _
    have hp : upCell k p := ⟨(F.path i).strip _, by omega, by omega⟩
    have hq : downCell k q := ⟨(F.path i).strip _, by omega, by omega⟩
    have he : chosenEdge (matchingOf F) p q :=
      ⟨hp, hq, (reconstructed_up_down F hp hq).mpr (Or.inl ⟨i, t, ht', rfl, rfl⟩)⟩
    change nextCell (matchingOf F) (track (matchingOf F) i t) = q
    rw [ih ht'.le]
    exact chosenEdge_unique_target (chosenEdge_nextCell (matchingOf F) hp) he

private noncomputable def perfectEquivTracks {k : ℕ} (hk : 0 < k) : Perfect k ≃ TrackFamily k where
  toFun := tracksOf hk
  invFun := matchingOf
  left_inv M := track_injective hk (funext fun i ↦ funext fun t ↦
    track_matchingOf (tracksOf hk M) i t.val (by have := t.isLt; omega))
  right_inv F := TrackFamily.ext_cell fun i t ↦
    track_matchingOf F i t.val (by have := t.isLt; omega)

private noncomputable def markedEquivTracks {k : ℕ} (hk : 0 < k) :
    {M : Perfect k // ∀ s t, s.val = (0, (k : ℤ), false) → t.val = (-1, (k : ℤ), true) →
      M.val.Adj s t} ≃
    {F : TrackFamily k // ∀ i, (F.path i).cell ⟨k, by omega⟩ ≠ (0, (k : ℤ))} :=
  (perfectEquivTracks hk).subtypeEquiv fun M ↦
    (marked_iff_center (by exact_mod_cast hk) M.val).trans (track_avoids_iff_center hk M).symm

private def descendingTracks (k : ℕ) : TrackFamily k where
  path i := {
    cell := fun t ↦ ((t.val : ℤ) - k, (k : ℤ) + i.val - (min t.val k : ℕ))
    column := fun _ ↦ rfl
    strip := fun t ↦ by
      have h₁ := t.isLt
      have h₂ := i.isLt
      dsimp [inStrip]
      by_cases ht : t.val ≤ k
      · rw [min_eq_left ht]
        omega
      · rw [min_eq_right (by omega)]
        omega
    first := by simp [source]
    last := by
      simp [sink, min_eq_right (show k ≤ 2 * k by omega)]
      omega
    step := fun t _ ↦ by
      dsimp [advances]
      by_cases ht : t < k
      · rw [min_eq_left ht.le, min_eq_left (show t + 1 ≤ k by omega)]
        omega
      · rw [min_eq_right (by omega : k ≤ t), min_eq_right (by omega : k ≤ t + 1)]
        omega }
  disjoint := fun _ _ hij _ h ↦ by
    apply hij
    apply Fin.ext
    have he := congrArg Prod.snd h
    dsimp at he
    omega

private lemma perfect_nonempty (k : ℕ) : Nonempty (Perfect k) :=
  ⟨matchingOf (descendingTracks k)⟩

end Honeycomb

open Polynomial

namespace CentralLozengeDifferences

noncomputable section

/-- Translation by `a` minus the identity, acting on rational polynomials. -/
private def difference (a : ℚ) : ℚ[X] →ₗ[ℚ] ℚ[X] := taylor a - LinearMap.id

private lemma eval_difference (a x : ℚ) (f : ℚ[X]) :
    (difference a f).eval x = f.eval (x + a) - f.eval x := by
  simp [difference, taylor_eval]

private lemma difference_natDegree_le {a : ℚ} {f : ℚ[X]} {m : ℕ} (hm : f.natDegree ≤ m + 1) :
    (difference a f).natDegree ≤ m := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  have hdeg := (natDegree_hasseDeriv_le f j).trans (Nat.sub_eq_zero_of_le (by omega) |>.le)
  have hc := eq_C_of_natDegree_le_zero hdeg
  change (taylor a f - f).coeff j = 0
  rw [coeff_sub, taylor_coeff, hc, eval_C, hasseDeriv_coeff]
  simp

private lemma coeff_difference {a : ℚ} {f : ℚ[X]} {m : ℕ} (hm : f.natDegree ≤ m + 1) :
    (difference a f).coeff m = a * (m + 1) * f.coeff (m + 1) := by
  have hdeg : (hasseDeriv m f).natDegree ≤ 1 := (natDegree_hasseDeriv_le f m).trans (by omega)
  have he (x : ℚ) : (hasseDeriv m f).eval x =
      (hasseDeriv m f).coeff 1 * x + (hasseDeriv m f).coeff 0 := by
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hdeg]
    simp
  change (taylor a f - f).coeff m = _
  rw [coeff_sub, taylor_coeff, he, hasseDeriv_coeff, hasseDeriv_coeff]
  rw [show 1 + m = m + 1 by omega, Nat.choose_succ_self_right, zero_add, Nat.choose_self,
    Nat.cast_one, one_mul]
  push_cast
  ring

/-- `d` successive finite differences. The recursion applies the last difference on the outside. -/
private def differences (a : ℚ) : ℕ → ℚ[X] → ℚ[X]
  | 0, f => f
  | d + 1, f => difference a (differences a d f)

private lemma differences_top (a : ℚ) (d m : ℕ) (f : ℚ[X]) (hf : f.natDegree ≤ m + d) :
    (differences a d f).natDegree ≤ m ∧
      (differences a d f).coeff m =
        ((m + d).factorial : ℚ) / (m.factorial : ℚ) * a^d * f.coeff (m + d) := by
  induction d generalizing m with
  | zero =>
      simpa [differences, div_self (by positivity : (m.factorial : ℚ) ≠ 0)] using hf
  | succ d ih =>
      have e : m + (d + 1) = m + 1 + d := by omega
      obtain ⟨hd, hc⟩ := ih (m + 1) (e ▸ hf)
      rw [differences, e]
      refine ⟨difference_natDegree_le hd, ?_⟩
      rw [coeff_difference hd, hc, Nat.factorial_succ m, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        pow_succ]
      field_simp (disch := positivity)

private lemma differences_eq_zero (a : ℚ) (d : ℕ) (f : ℚ[X]) (hf : f.natDegree < d) :
    differences a d f = 0 := by
  obtain ⟨hdeg, hcoeff⟩ := differences_top a d 0 f (by omega)
  rw [eq_C_of_natDegree_le_zero hdeg, hcoeff, Nat.zero_add,
    coeff_eq_zero_of_natDegree_lt hf, mul_zero, C_0]

private lemma differences_eval_succ (a x : ℚ) (d : ℕ) (f : ℚ[X]) :
    (differences a (d + 1) f).eval x =
      (differences a d f).eval (x + a) - (differences a d f).eval x :=
  eval_difference a x (differences a d f)

private lemma difference_pow_apply (a : ℚ) (d : ℕ) (f : ℚ[X]) :
    ((difference a)^d : Module.End ℚ ℚ[X]) f = differences a d f := by
  induction d with
  | zero => rfl
  | succ d ih => rw [pow_succ', mul_apply_eq_comp, ih, differences]

private lemma taylor_pow_apply (a : ℚ) (d : ℕ) (f : ℚ[X]) :
    ((taylor a)^d : Module.End ℚ ℚ[X]) f = taylor ((d : ℚ) * a) f := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, taylor_taylor, Nat.cast_succ]
    congr 2
    ring

/-- Pascal coefficients are the entries of the iterated difference operator. -/
private lemma differences_eval_sum (a x : ℚ) (d : ℕ) (f : ℚ[X]) :
    (differences a d f).eval x = ∑ j ∈ Finset.range (d + 1),
      (d.choose j : ℚ) * (-1 : ℚ)^(d - j) * f.eval (x + (j : ℚ) * a) := by
  rw [← difference_pow_apply]
  let T : Module.End ℚ ℚ[X] := taylor a
  change (((T - 1)^d : Module.End ℚ ℚ[X]) f).eval x = _
  have hc : Commute T (-1) := by
    have he := (Algebra.commutes (R := ℚ) (A := Module.End ℚ ℚ[X]) (-1) T).symm
    change T * -1 = -1 * T
    simpa only [map_neg, map_one] using he
  rw [sub_eq_add_neg, hc.add_pow',
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun j m ↦ d.choose j • (T^j * (-1)^m))]
  simp only [LinearMap.sum_apply]
  change evalRingHom x (∑ j ∈ Finset.range (d + 1), _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hsign (p : ℕ) : ((-1 : Module.End ℚ ℚ[X])^p) = ((-1 : ℚ)^p) • 1 := by
    rw [← Algebra.algebraMap_eq_smul_one, map_pow]
    simp
  have hn (l : ℕ) (S : Module.End ℚ ℚ[X]) (p : ℚ[X]) : (l • S) p = l • S p := by
    induction l with
    | zero => simp
    | succ l ih => rw [succ_nsmul, LinearMap.add_apply, succ_nsmul, ih]
  rw [hsign, hn, map_nsmul]
  simp only [mul_apply_eq_comp, LinearMap.smul_apply, one_apply_eq_self, T,
    taylor_pow_apply, coe_evalRingHom, qsmul_eq_C_mul, Rat.cast_id, eval_mul, eval_C,
    taylor_eval, nsmul_eq_mul, mul_assoc]

private lemma difference_of_zero_window (a x : ℚ) (d : ℕ) (f : ℚ[X])
    (h : ∀ j ≤ d, f.eval (x + (j : ℚ) * a) = 0) : (differences a d f).eval x = 0 := by
  rw [differences_eval_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [h j (by simpa using hj), mul_zero]

end

end CentralLozengeDifferences

open scoped BigOperators

namespace CentralLozengeArithmetic

/-- Consecutive even-degree contributions to the central projection. -/
private def step (n j : ℚ) : ℚ :=
  ((2 * j - 1)^2 * (4 * n + 2 * j - 2) * (4 * n - 2 * j) * (4 * j + 1)) /
    ((2 * j)^2 * (4 * n + 2 * j - 1) * (4 * n - 2 * j - 1) * (4 * j - 3))

/-- The normalized summand in the Helfgott–Gessel telescope. -/
private def term (n i : ℕ) : ℚ :=
  (∏ j ∈ Finset.range i, step n (j + 1 : ℚ)) / (4 * (n : ℚ) - 1)

private lemma term_succ (n i : ℕ) :
    term n (i + 1) = term n i * step n (i + 1 : ℚ) := by
  rw [term, Finset.prod_range_succ, term]
  ring

/-- The ratio when the hexagon parameter increases at fixed polynomial degree. -/
private def shift (n i : ℚ) : ℚ :=
  ((4 * n + 2 * i) * (4 * n + 2 * i + 2) * (4 * n - 2 * i - 1) * (4 * n - 2 * i + 1)) /
    ((4 * n + 2 * i + 1) * (4 * n + 2 * i + 3) * (4 * n - 2 * i) * (4 * n - 2 * i + 2))

private lemma shift_zero {n : ℚ} (hn : 1 ≤ n) :
    shift n 0 * (4 * n + 3) = 4 * n - 1 := by
  simp only [shift, mul_zero, add_zero, sub_zero]
  field_simp (disch := linarith)

private lemma shift_step {n i : ℚ} (hn : 1 ≤ n) (hi : 0 ≤ i) (hin : i + 1 ≤ n) :
    shift n i * step (n + 1) (i + 1) = step n (i + 1) * shift n (i + 1) := by
  unfold shift step
  field_simp (disch := first | positivity | linarith)
  ring

private lemma term_shift {n i : ℕ} (hn : 1 ≤ n) (hi : i ≤ n) :
    term (n + 1) i = term n i * shift n i := by
  have hn' : (1 : ℚ) ≤ n := by exact_mod_cast hn
  induction i with
  | zero =>
      have h₀ : (4 * (n : ℚ) - 1) ≠ 0 := by linarith
      have h₁ : (4 * (n : ℚ) + 3) ≠ 0 := by positivity
      simp only [term, Finset.range_zero, Finset.prod_empty, Nat.cast_add, Nat.cast_one,
        Nat.cast_zero]
      rw [show 4 * ((n : ℚ) + 1) - 1 = 4 * n + 3 by ring]
      rw [div_mul_eq_mul_div, one_mul]
      apply (div_eq_div_iff h₁ h₀).mpr
      simpa [one_mul, mul_comm] using (shift_zero hn').symm
  | succ i ih =>
      rw [term_succ, term_succ, ih (by omega), Nat.cast_add, Nat.cast_one, mul_assoc]
      rw [shift_step hn' (by positivity) (by exact_mod_cast hi), ← mul_assoc]
      norm_cast

/-- Rational certificate from Helfgott–Gessel, arXiv:math/9810143, Lemma 16. -/
private def certificate (n i : ℚ) : ℚ :=
  (i^2 * (2 * i + 1 - 4 * n) * (1 + 4 * n) * (8 * n^2 + 4 * n - 2 * i^2 + i + 1)) /
    ((4 * i + 1) * (2 * i + 1 + 4 * n) * (i - 2 * n) * (i - 1 - 2 * n) * (2 * n + 1) * n)

private lemma certificate_step {n i : ℚ} (hn : 1 ≤ n) (hi : 0 ≤ i) (hin : i + 1 ≤ n) :
    certificate n (i + 1) * step n (i + 1) - certificate n i = shift n i - 1 := by
  unfold certificate step shift
  field_simp (disch := first | positivity | linarith)
  ring

private lemma certificate_end {n : ℚ} (hn : 1 ≤ n) :
    certificate n n = -shift n n := by
  unfold certificate shift
  field_simp (disch := first | positivity | linarith)
  ring

private def boundary (n i : ℕ) : ℚ := certificate n i * term n i

private lemma boundary_zero (n : ℕ) : boundary n 0 = 0 := by
  simp [boundary, certificate]

private lemma boundary_end {n : ℕ} (hn : 1 ≤ n) :
    boundary n n = -term (n + 1) n := by
  rw [boundary, term_shift hn le_rfl, certificate_end (by exact_mod_cast hn)]
  ring

private lemma boundary_step {n i : ℕ} (hn : 1 ≤ n) (hi : i < n) :
    boundary n (i + 1) - boundary n i = term (n + 1) i - term n i := by
  have hin : (i : ℚ) + 1 ≤ n := by exact_mod_cast (show i + 1 ≤ n by omega)
  have h := certificate_step (by exact_mod_cast hn) (Nat.cast_nonneg (α := ℚ) i) hin
  rw [boundary, boundary, term_shift hn hi.le, term_succ, Nat.cast_add, Nat.cast_one]
  calc
    _ = term n i * (certificate n (i + 1) * step n (i + 1) - certificate n i) := by ring
    _ = _ := by rw [h]; ring

private lemma sum_term_succ {n : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ Finset.range (n + 1), term (n + 1) i = ∑ i ∈ Finset.range n, term n i := by
  have hs : (∑ i ∈ Finset.range n, (boundary n i - boundary n (i + 1))) =
      ∑ i ∈ Finset.range n, (term n i - term (n + 1) i) := by
    apply Finset.sum_congr rfl
    intro i hi
    linarith [boundary_step hn (Finset.mem_range.mp hi)]
  rw [Finset.sum_range_sub', boundary_end hn, boundary_zero, zero_sub, neg_neg,
    Finset.sum_sub_distrib] at hs
  rw [Finset.sum_range_succ]
  linarith

/-- The central projection sum is exactly one third for every positive parameter. -/
private lemma sum_term_eq_third {n : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ Finset.range n, term n i = 1 / 3 := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h : n = 0
      · subst n
        norm_num [term, Finset.sum_range_succ]
      · rw [sum_term_succ (by omega : 1 ≤ n), ih (by omega)]

end CentralLozengeArithmetic

open Matrix

namespace CentralLozengeGram

/-- Half-path counts by middle height. Entries below the allowed integer range are zero,
and `Nat.choose` makes the entries above that range zero. -/
private def halfPaths (k : ℕ) : Matrix (Fin (2 * k + 1)) (Fin (k + 1)) ℚ :=
  of fun r i ↦ if i.val ≤ r.val then (k.choose (r.val - i.val) : ℚ) else 0

private lemma halfPaths_injective (k : ℕ) : Function.Injective (halfPaths k *ᵥ ·) := by
  have hzero (u : Fin (k + 1) → ℚ) (hu : halfPaths k *ᵥ u = 0) : u = 0 := by
    have hz : ∀ (t : ℕ) (ht : t < k + 1), u ⟨t, ht⟩ = 0 := by
      intro t
      induction t using Nat.strong_induction_on with
      | ind t ih =>
        intro ht
        let i : Fin (k + 1) := ⟨t, ht⟩
        let r : Fin (2 * k + 1) := ⟨t, by omega⟩
        have h := congrFun hu r
        change (∑ j, halfPaths k r j * u j) = 0 at h
        rw [Finset.sum_eq_single i] at h
        · simpa [halfPaths, i, r] using h
        · intro j _ hji
          by_cases hj : j.val ≤ r.val
          · have he : j.val ≠ t := fun he ↦ hji (Fin.ext he)
            have hj' : j.val < t := by change j.val ≤ t at hj; omega
            rw [show u j = 0 from ih j.val hj' j.isLt, mul_zero]
          · simp [halfPaths, hj]
        · simp
    funext i
    exact hz i.val i.isLt
  intro u v h
  change halfPaths k *ᵥ u = halfPaths k *ᵥ v at h
  apply sub_eq_zero.mp
  apply hzero
  rw [Matrix.mulVec_sub, h, sub_self]

/-- The full Gram matrix is nonsingular: the leading square block of the half-path
matrix is lower triangular with diagonal entries 1. -/
private lemma gram_isUnit (k : ℕ) : IsUnit ((halfPaths k)ᵀ * halfPaths k) := by
  apply mulVec_injective_iff_isUnit.mp
  let B := halfPaths k
  have hzero (u : Fin (k + 1) → ℚ) (hu : (Bᵀ * B) *ᵥ u = 0) : u = 0 := by
    have h : (B *ᵥ u) ⬝ᵥ (B *ᵥ u) = 0 := by
      rw [← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, hu, dotProduct_zero]
    have h' := dotProduct_self_eq_zero.mp h
    exact halfPaths_injective k (by simpa [B] using h')
  intro u v h
  apply sub_eq_zero.mp
  apply hzero
  rw [Matrix.mulVec_sub, h, sub_self]

/-! ### Finite path lists for Lindström–Gessel–Viennot -/

private def directedStep (k : ℕ) (p q : Cell) : Prop := -(k : ℤ) ≤ p.1 ∧ advances p q

private def pathRank (k : ℕ) (p : Cell) : ℕ := (p.1 + (k : ℤ)).toNat

private lemma pathRank_increases {k : ℕ} {p q : Cell} (h : directedStep k p q) :
    pathRank k p < pathRank k q := by
  have hx := h.1
  have hy := h.2.1
  dsimp [pathRank]
  omega

private lemma chain_iff_steps {α : Type} {R : α → α → Prop} (l : List α) :
    l.IsChain R ↔ ∀ (t : ℕ) (ht : t + 1 < l.length), R l[t] l[t + 1] := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      rw [List.isChain_cons_cons, ih]
      constructor
      · rintro ⟨hab, h⟩ t ht
        cases t with
        | zero => exact hab
        | succ t => exact h t (by simpa using ht)
      · intro h
        exact ⟨h 0 (by simp), fun t ht ↦ h (t + 1) (by simpa using ht)⟩

private lemma chain_column {k : ℕ} {i : Fin (k + 1)} {l : List Cell}
    (hl : l.head? = some (source k i)) (hc : l.IsChain (directedStep k)) :
    ∀ (t : ℕ) (ht : t < l.length), l[t].1 = (t : ℤ) - k := by
  intro t
  induction t with
  | zero =>
    intro ht
    have hh : l[0] = source k i := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem ht] at hl
      exact Option.some.inj hl
    rw [hh]
    simp [source]
  | succ t ih =>
    intro ht
    have h := ((chain_iff_steps l).mp hc t ht).2.1
    rw [h, ih (by omega)]
    omega

private lemma chain_length {k : ℕ} {i j : Fin (k + 1)} {l : List Cell}
    (hl : l.head? = some (source k i)) (hr : l.getLast? = some (sink k j))
    (hc : l.IsChain (directedStep k)) : l.length = 2 * k + 1 := by
  have hn : l ≠ [] := by rintro rfl; simp at hl
  have hp := List.length_pos_iff.mpr hn
  have ht : l.length - 1 < l.length := by omega
  have hs : l[l.length - 1] = sink k j := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem ht] at hr
    exact Option.some.inj hr
  have hc' := chain_column hl hc (l.length - 1) ht
  rw [hs] at hc'
  change (k : ℤ) = ((l.length - 1 : ℕ) : ℤ) - k at hc'
  omega

private lemma sequence_order {m : ℕ} {f : Fin (m + 1) → ℤ}
    (h : ∀ (t : ℕ) (ht : t < m), f ⟨t, by omega⟩ ≤ f ⟨t + 1, by omega⟩)
    {a b : Fin (m + 1)} (hab : a.val ≤ b.val) : f a ≤ f b := by
  obtain ⟨b, hb⟩ := b
  change a.val ≤ b at hab
  induction b with
  | zero =>
    have he : a = ⟨0, hb⟩ := Fin.ext (by change a.val = 0; omega)
    rw [he]
  | succ b ih =>
    by_cases he : a.val ≤ b
    · exact (ih (by omega) he).trans (h b (by omega))
    · have hf : a = ⟨b + 1, hb⟩ := Fin.ext (by change a.val = b + 1; omega)
      rw [hf]

private lemma strip_of_steps {k : ℕ} {i j : Fin (k + 1)} {f : Fin (2 * k + 1) → Cell}
    (h₀ : f 0 = source k i) (h₁ : f (Fin.last (2 * k)) = sink k j)
    (hs : ∀ (t : ℕ) (ht : t < 2 * k), advances (f ⟨t, by omega⟩) (f ⟨t + 1, by omega⟩))
    (t : Fin (2 * k + 1)) : inStrip k (f t) := by
  have hy (u : ℕ) (hu : u < 2 * k) :
      -(f ⟨u, by omega⟩).2 ≤ -(f ⟨u + 1, by omega⟩).2 := by
    have h := (hs u hu).2
    omega
  let xy := fun p : Cell ↦ p.1 + p.2
  have hxy (u : ℕ) (hu : u < 2 * k) :
      xy (f ⟨u, by omega⟩) ≤ xy (f ⟨u + 1, by omega⟩) := by
    obtain ⟨hx, hy⟩ := hs u hu
    dsimp [xy]
    omega
  have ht₀ : (0 : Fin (2 * k + 1)).val ≤ t.val := Nat.zero_le _
  have ht₁ : t.val ≤ (Fin.last (2 * k)).val := by simpa using Nat.le_of_lt_succ t.isLt
  have hy₀ := sequence_order (f := fun t ↦ -(f t).2) hy ht₀
  have hy₁ := sequence_order (f := fun t ↦ -(f t).2) hy ht₁
  have hx₀ := sequence_order (f := fun t ↦ xy (f t)) hxy ht₀
  have hx₁ := sequence_order (f := fun t ↦ xy (f t)) hxy ht₁
  simp only [h₀, h₁, source, sink, xy] at hy₀ hy₁ hx₀ hx₁
  have hi := i.isLt
  have hj := j.isLt
  dsimp only [inStrip]
  omega

private def pathList {k : ℕ} {i j : Fin (k + 1)} (P : StripPath k i j) : List Cell :=
  List.ofFn P.cell

private lemma pathList_injective {k : ℕ} {i j : Fin (k + 1)} :
    Function.Injective (@pathList k i j) := fun _ _ h ↦
  StripPath.ext_cell (List.ofFn_injective h)

private lemma pathList_chain {k : ℕ} {i j : Fin (k + 1)} (P : StripPath k i j) :
    (pathList P).head? = some (source k i) ∧ (pathList P).getLast? = some (sink k j) ∧
      (pathList P).IsChain (directedStep k) := by
  have he : (pathList P).length = 2 * k + 1 := List.length_ofFn
  constructor
  · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    simp only [pathList, List.getElem_ofFn]
    exact congrArg some P.first
  constructor
  · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    simp only [pathList, List.getElem_ofFn]
    have ht : (⟨(List.ofFn P.cell).length - 1, by simp⟩ : Fin (2 * k + 1)) =
        Fin.last (2 * k) := Fin.ext (by simp)
    rw [ht, P.last]
  · apply (chain_iff_steps _).mpr
    intro t ht
    simp only [pathList, List.getElem_ofFn]
    have ht' : t < 2 * k := by omega
    exact ⟨by rw [P.column]; have := Nat.cast_nonneg (α := ℤ) t; omega, P.step t ht'⟩

private lemma pathList_exists {k : ℕ} {i j : Fin (k + 1)} {l : List Cell}
    (hl : l.head? = some (source k i)) (hr : l.getLast? = some (sink k j))
    (hc : l.IsChain (directedStep k)) : ∃ P : StripPath k i j, pathList P = l := by
  have len := chain_length hl hr hc
  let f : Fin (2 * k + 1) → Cell := fun t ↦ l[t.val]'(by omega)
  have h₀ : f 0 = source k i := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hl
    exact Option.some.inj hl
  have h₁ : f (Fin.last (2 * k)) = sink k j := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hr
    have he := Option.some.inj hr
    have e : l.length - 1 = 2 * k := by omega
    change l[2 * k] = sink k j
    simpa only [e] using he
  have hstep (u : ℕ) (hu : u < 2 * k) :
      advances (f ⟨u, by omega⟩) (f ⟨u + 1, by omega⟩) :=
    ((chain_iff_steps l).mp hc u (by omega)).2
  refine ⟨⟨f, fun t ↦ chain_column hl hc t.val (by have := t.isLt; omega),
    strip_of_steps h₀ h₁ hstep, h₀, h₁, hstep⟩, ?_⟩
  apply List.ext_getElem
  · exact List.length_ofFn.trans len.symm
  · intro n hn hn'
    change n < (List.ofFn f).length at hn
    change (List.ofFn f)[n]'hn = l[n]
    exact List.getElem_ofFn hn

private lemma finite_stripPath (k : ℕ) (i j : Fin (k + 1)) : Finite (StripPath k i j) := by
  let encode (P : StripPath k i j) (t : Fin (2 * k + 1)) : Set.Icc (0 : ℤ) (2 * k) :=
    ⟨(P.cell t).2, (P.strip t).1, (P.strip t).2.1⟩
  apply Finite.of_injective encode
  intro P Q h
  apply StripPath.ext_cell
  funext t
  exact Prod.ext ((P.column t).trans (Q.column t).symm)
    (congrArg Subtype.val (congrFun h t))

private noncomputable def pathFinset (k : ℕ) (i j : Fin (k + 1)) : Finset (List Cell) :=
  let := finite_stripPath k i j
  letI := Fintype.ofFinite (StripPath k i j)
  (Finset.univ : Finset (StripPath k i j)).map ⟨pathList, pathList_injective⟩

private lemma mem_pathFinset_iff {k : ℕ} {i j : Fin (k + 1)} {l : List Cell} :
    l ∈ pathFinset k i j ↔ ∃ P : StripPath k i j, pathList P = l := by
  simp [pathFinset]

private lemma pathFinset_spec {k : ℕ} (i j : Fin (k + 1)) (l : List Cell) :
    l ∈ pathFinset k i j ↔ l.head? = some (source k i) ∧ l.getLast? = some (sink k j) ∧
      l.IsChain (directedStep k) := by
  rw [mem_pathFinset_iff]
  constructor
  · rintro ⟨P, rfl⟩
    exact pathList_chain P
  · rintro ⟨h₀, h₁, hc⟩
    exact pathList_exists h₀ h₁ hc

private lemma inverted_paths_meet {k : ℕ} (i j a b : Fin (k + 1)) (hij : i < j) (hba : b < a)
    (P : StripPath k i a) (Q : StripPath k j b) : ∃ t, P.cell t = Q.cell t := by
  by_contra! hne
  have h (t : ℕ) (ht : t ≤ 2 * k) : (P.cell ⟨t, by omega⟩).2 < (Q.cell ⟨t, by omega⟩).2 := by
    induction t with
    | zero =>
      have hf : (⟨0, by omega⟩ : Fin (2 * k + 1)) = 0 := rfl
      rw [hf, P.first, Q.first]
      have hij' : i.val < j.val := hij
      simp only [source]
      omega
    | succ t ih =>
      let s : Fin (2 * k + 1) := ⟨t + 1, by omega⟩
      have hneq : (P.cell s).2 ≠ (Q.cell s).2 := fun he ↦
        hne s (Prod.ext ((P.column s).trans (Q.column s).symm) he)
      dsimp only [s] at hneq
      have hp := (P.step t (by omega)).2
      have hq := (Q.step t (by omega)).2
      have hlt := ih (by omega)
      omega
  have he := h (2 * k) le_rfl
  change (P.cell (Fin.last (2 * k))).2 < (Q.cell (Fin.last (2 * k))).2 at he
  rw [P.last, Q.last] at he
  change (a.val : ℤ) < b.val at he
  have hb : b.val < a.val := hba
  omega

private lemma pathFinset_planar {k : ℕ} (i j a b : Fin (k + 1)) (hij : i < j) (hba : b < a)
    (p : List Cell) (hp : p ∈ pathFinset k i a) (q : List Cell) (hq : q ∈ pathFinset k j b) :
    ∃ u, u ∈ p ∧ u ∈ q := by
  obtain ⟨P, rfl⟩ := mem_pathFinset_iff.mp hp
  obtain ⟨Q, rfl⟩ := mem_pathFinset_iff.mp hq
  obtain ⟨t, ht⟩ := inverted_paths_meet i j a b hij hba P Q
  exact ⟨P.cell t, List.mem_ofFn.mpr ⟨t, rfl⟩, List.mem_ofFn.mpr ⟨t, ht.symm⟩⟩

/-! ### Binomial enumeration by the positions of the descending steps -/

private abbrev Word (m : ℕ) := Fin m → Bool

private def bitStep {m : ℕ} (w : Word m) (t : ℕ) : ℕ :=
  if ht : t < m then if w ⟨t, ht⟩ then 1 else 0 else 0

private def descents {m : ℕ} (w : Word m) (t : ℕ) : ℕ :=
  ∑ s ∈ Finset.range t, bitStep w s

private lemma descents_succ {m : ℕ} (w : Word m) (t : ℕ) :
    descents w (t + 1) = descents w t + bitStep w t := by
  exact Finset.sum_range_succ (bitStep w) t

private def pathWord {k : ℕ} {i j : Fin (k + 1)} (P : StripPath k i j) : Word (2 * k) :=
  fun t ↦ decide ((P.cell ⟨t.val + 1, by have := t.isLt; omega⟩).2 =
    (P.cell ⟨t.val, by have := t.isLt; omega⟩).2 - 1)

private lemma pathWord_height {k : ℕ} {i j : Fin (k + 1)} (P : StripPath k i j)
    (t : ℕ) (ht : t ≤ 2 * k) :
    (P.cell ⟨t, by omega⟩).2 = (k : ℤ) + i.val - (descents (pathWord P) t : ℤ) := by
  induction t with
  | zero =>
    change (P.cell 0).2 = _
    rw [P.first]
    simp [source, descents]
  | succ t ih =>
    have ht' : t < 2 * k := by omega
    have hy := (P.step t ht').2
    have hp := ih ht'.le
    rw [descents_succ, Nat.cast_add, bitStep, dite_eq_left ht']
    simp only [pathWord, decide_eq_true_eq]
    split <;> omega

private lemma pathWord_total {k : ℕ} {i j : Fin (k + 1)} (P : StripPath k i j) :
    (descents (pathWord P) (2 * k) : ℤ) = (k : ℤ) + i.val - j.val := by
  have h := pathWord_height P (2 * k) le_rfl
  change (P.cell (Fin.last (2 * k))).2 = _ at h
  rw [P.last] at h
  change (j.val : ℤ) = _ at h
  omega

private def wordPath {k : ℕ} {i j : Fin (k + 1)} (w : Word (2 * k))
    (hw : (descents w (2 * k) : ℤ) = (k : ℤ) + i.val - j.val) : StripPath k i j := by
  let cell (t : Fin (2 * k + 1)) : Cell := ((t.val : ℤ) - k, (k : ℤ) + i.val - descents w t.val)
  have h₀ : cell 0 = source k i := by simp [cell, source, descents]
  have h₁ : cell (Fin.last (2 * k)) = sink k j := by
    simp only [cell, Fin.val_last, Nat.cast_mul, Nat.cast_ofNat, hw, sink, Prod.mk.injEq]
    omega
  have hstep (t : ℕ) (ht : t < 2 * k) :
      advances (cell ⟨t, by omega⟩) (cell ⟨t + 1, by omega⟩) := by
    dsimp only [advances, cell]
    rw [descents_succ, Nat.cast_add, bitStep, dite_eq_left ht]
    cases w ⟨t, ht⟩ <;> simp <;> omega
  exact ⟨cell, fun _ ↦ rfl, strip_of_steps h₀ h₁ hstep, h₀, h₁, hstep⟩

private lemma pathWord_wordPath {k : ℕ} {i j : Fin (k + 1)} (w : Word (2 * k))
    (hw : (descents w (2 * k) : ℤ) = (k : ℤ) + i.val - j.val) :
    pathWord (wordPath w hw) = w := by
  funext t
  have ht := t.isLt
  change decide ((k : ℤ) + i.val - (descents w (t.val + 1) : ℤ) =
    (k : ℤ) + i.val - (descents w t.val : ℤ) - 1) = w t
  rw [descents_succ, Nat.cast_add, bitStep, dite_eq_left ht]
  cases w t <;> simp <;> omega

private def stripPathEquivWord {k : ℕ} (i j : Fin (k + 1)) :
    StripPath k i j ≃ {w : Word (2 * k) //
      (descents w (2 * k) : ℤ) = (k : ℤ) + i.val - j.val} where
  toFun P := ⟨pathWord P, pathWord_total P⟩
  invFun w := wordPath w.val w.property
  left_inv P := StripPath.ext_cell (funext fun t ↦
    Prod.ext (P.column t).symm (pathWord_height P t.val (by have := t.isLt; omega)).symm)
  right_inv w := Subtype.ext (pathWord_wordPath w.val w.property)

private def leftWord {k : ℕ} (w : Word (2 * k)) : Word k :=
  fun t ↦ w ⟨t.val, by have := t.isLt; omega⟩

private def rightWord {k : ℕ} (w : Word (2 * k)) : Word k :=
  fun t ↦ w ⟨k + t.val, by have := t.isLt; omega⟩

private def joinWord {k : ℕ} (a b : Word k) : Word (2 * k) := fun t ↦
  if h : t.val < k then a ⟨t.val, h⟩ else b ⟨t.val - k, by have := t.isLt; omega⟩

private lemma leftWord_joinWord {k : ℕ} (a b : Word k) : leftWord (joinWord a b) = a := by
  funext t
  simp [leftWord, joinWord, t.isLt]

private lemma rightWord_joinWord {k : ℕ} (a b : Word k) : rightWord (joinWord a b) = b := by
  funext t
  have h : ¬k + t.val < k := by omega
  simp [rightWord, joinWord, h]

private lemma joinWord_split {k : ℕ} (w : Word (2 * k)) :
    joinWord (leftWord w) (rightWord w) = w := by
  funext t
  by_cases ht : t.val < k
  · simp [joinWord, leftWord, ht]
  · simp only [joinWord, dite_eq_right ht, rightWord]
    apply congrArg w
    apply Fin.ext
    change k + (t.val - k) = t.val
    omega

private lemma descents_left {k : ℕ} (w : Word (2 * k)) :
    descents w k = descents (leftWord w) k := by
  apply Finset.sum_congr rfl
  intro t ht
  have h := Finset.mem_range.mp ht
  simp [bitStep, leftWord, h, (show t < 2 * k by omega)]
  rfl

private lemma descents_split {k : ℕ} (w : Word (2 * k)) :
    descents w (2 * k) = descents (leftWord w) k + descents (rightWord w) k := by
  have e : 2 * k = k + k := by omega
  calc
    descents w (2 * k) = descents w (k + k) := congrArg (descents w) e
    _ = descents w k + ∑ t ∈ Finset.range k, bitStep w (k + t) :=
      Finset.sum_range_add (bitStep w) k k
    _ = _ := by
      rw [descents_left w]
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      have h := Finset.mem_range.mp ht
      simp [bitStep, rightWord, h, (show k + t < 2 * k by omega)]
      rfl

private def wordSet {m : ℕ} (w : Word m) : Finset (Fin m) := Finset.univ.filter (fun t ↦ w t)

private lemma descents_card_wordSet {m : ℕ} (w : Word m) : descents w m = (wordSet w).card := by
  rw [descents, ← Fin.sum_univ_eq_sum_range (bitStep w), wordSet, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  simp [bitStep, t.isLt]

private def setWord {m : ℕ} (s : Finset (Fin m)) : Word m := fun t ↦ decide (t ∈ s)

private lemma wordSet_setWord {m : ℕ} (s : Finset (Fin m)) : wordSet (setWord s) = s := by
  ext t
  simp [wordSet, setWord]

private lemma setWord_wordSet {m : ℕ} (w : Word m) : setWord (wordSet w) = w := by
  funext t
  simp [setWord, wordSet]

private def wordsOfSizeEquiv (m d : ℕ) : {w : Word m // descents w m = d} ≃
    ↑((Finset.univ : Finset (Fin m)).powersetCard d) where
  toFun w := ⟨wordSet w.val, Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _, (descents_card_wordSet w.val).symm.trans w.property⟩⟩
  invFun s := ⟨setWord s.val, by
    rw [descents_card_wordSet, wordSet_setWord]
    exact (Finset.mem_powersetCard.mp s.property).2⟩
  left_inv w := Subtype.ext (setWord_wordSet w.val)
  right_inv s := Subtype.ext (wordSet_setWord s.val)

private lemma card_wordsOfSize (m d : ℕ) :
    Nat.card {w : Word m // descents w m = d} = m.choose d := by
  rw [Nat.card_congr (wordsOfSizeEquiv m d), Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

private def signedChoose (m : ℕ) (d : ℤ) : ℕ := if 0 ≤ d then m.choose d.toNat else 0

private lemma card_wordsWithDescents (m : ℕ) (d : ℤ) :
    Nat.card {w : Word m // (descents w m : ℤ) = d} = signedChoose m d := by
  by_cases hd : 0 ≤ d
  · rw [signedChoose, ite_eq_left hd, ← card_wordsOfSize m d.toNat]
    have e : {w : Word m // (descents w m : ℤ) = d} ≃
        {w : Word m // descents w m = d.toNat} := {
      toFun := fun w ↦ ⟨w.val, by have := w.property; omega⟩
      invFun := fun w ↦ ⟨w.val, by have := w.property; omega⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
    exact Nat.card_congr e
  · rw [signedChoose, ite_eq_right hd]
    have : IsEmpty {w : Word m // (descents w m : ℤ) = d} :=
      ⟨fun w ↦ hd (w.property ▸ by positivity)⟩
    let := Fintype.ofFinite {w : Word m // (descents w m : ℤ) = d}
    rw [Nat.card_eq_fintype_card, Fintype.card_of_isEmpty]

private def middle (k : ℕ) : Fin (2 * k + 1) := ⟨k, by omega⟩

private def middleHeight {k : ℕ} {i j : Fin (k + 1)} (P : StripPath k i j) : Fin (2 * k + 1) :=
  ⟨(P.cell (middle k)).2.toNat, by have := (P.strip (middle k)).2.1; omega⟩

private lemma middle_cell {k : ℕ} {i j : Fin (k + 1)} (P : StripPath k i j) :
    P.cell (middle k) = (0, ((middleHeight P).val : ℤ)) := by
  apply Prod.ext
  · simpa [middle] using P.column (middle k)
  · have h := (P.strip (middle k)).1
    dsimp [middleHeight]
    omega

private lemma middleHeight_eq_iff {k : ℕ} {i j : Fin (k + 1)} (P : StripPath k i j)
    (r : Fin (2 * k + 1)) : middleHeight P = r ↔ (P.cell (middle k)).2 = (r.val : ℤ) := by
  have hh := congrArg Prod.snd (middle_cell P)
  constructor
  · intro h
    rw [h] at hh
    exact hh
  · intro h
    apply Fin.ext
    omega

private def halfWordsEquiv {k : ℕ} {i j : Fin (k + 1)} (r : Fin (2 * k + 1)) :
    {P : StripPath k i j // middleHeight P = r} ≃
      {a : Word k // (descents a k : ℤ) = (k : ℤ) + i.val - r.val} ×
      {b : Word k // (descents b k : ℤ) = (r.val : ℤ) - j.val} where
  toFun P := by
    let w := pathWord P.val
    have h₀ := (middleHeight_eq_iff P.val r).mp P.property
    have hh := pathWord_height P.val k (by omega)
    change (P.val.cell (middle k)).2 = (k : ℤ) + i.val - (descents w k : ℤ) at hh
    have hl : (descents (leftWord w) k : ℤ) = (k : ℤ) + i.val - r.val := by
      rw [← descents_left]
      omega
    have ht : (descents w (2 * k) : ℤ) = (k : ℤ) + i.val - j.val := pathWord_total P.val
    rw [descents_split, Nat.cast_add] at ht
    exact (⟨leftWord w, hl⟩, ⟨rightWord w, by omega⟩)
  invFun p := by
    let w := joinWord p.1.val p.2.val
    have hw : (descents w (2 * k) : ℤ) = (k : ℤ) + i.val - j.val := by
      rw [descents_split, Nat.cast_add]
      dsimp only [w]
      rw [leftWord_joinWord, rightWord_joinWord, p.1.property, p.2.property]
      omega
    refine ⟨wordPath w hw, (middleHeight_eq_iff _ r).mpr ?_⟩
    change (k : ℤ) + i.val - (descents w k : ℤ) = r.val
    rw [descents_left]
    dsimp only [w]
    rw [leftWord_joinWord, p.1.property]
    omega
  left_inv P := by
    apply Subtype.ext
    apply (stripPathEquivWord i j).injective
    apply Subtype.ext
    let w := pathWord P.val
    have hw : (descents (joinWord (leftWord w) (rightWord w)) (2 * k) : ℤ) =
        (k : ℤ) + i.val - j.val := by
      rw [joinWord_split]
      exact pathWord_total P.val
    change pathWord (wordPath (joinWord (leftWord w) (rightWord w)) hw) = w
    rw [pathWord_wordPath, joinWord_split]
  right_inv p := by
    have hw : (descents (joinWord p.1.val p.2.val) (2 * k) : ℤ) = (k : ℤ) + i.val - j.val := by
      rw [descents_split, Nat.cast_add, leftWord_joinWord, rightWord_joinWord,
        p.1.property, p.2.property]
      omega
    apply Prod.ext <;> apply Subtype.ext
    · change leftWord (pathWord (wordPath (joinWord p.1.val p.2.val) hw)) = p.1.val
      rw [pathWord_wordPath, leftWord_joinWord]
    · change rightWord (pathWord (wordPath (joinWord p.1.val p.2.val) hw)) = p.2.val
      rw [pathWord_wordPath, rightWord_joinWord]

private lemma signedChoose_reflect (k : ℕ) (d : ℤ) :
    signedChoose k ((k : ℤ) - d) = signedChoose k d := by
  by_cases hd₀ : 0 ≤ d
  · by_cases hd₁ : d ≤ k
    · rw [signedChoose, signedChoose, ite_eq_left (by omega), ite_eq_left hd₀]
      have e : ((k : ℤ) - d).toNat = k - d.toNat := by omega
      rw [e, Nat.choose_symm (by omega)]
    · rw [signedChoose, signedChoose, ite_eq_right (by omega), ite_eq_left hd₀,
        Nat.choose_eq_zero_of_lt (by omega)]
  · rw [signedChoose, signedChoose, ite_eq_left (by omega), ite_eq_right hd₀,
      Nat.choose_eq_zero_of_lt (by omega)]

private lemma halfPaths_signedChoose (k : ℕ) (r : Fin (2 * k + 1)) (i : Fin (k + 1)) :
    halfPaths k r i = (signedChoose k ((r.val : ℤ) - i.val) : ℚ) := by
  by_cases h : i.val ≤ r.val <;> simp [halfPaths, signedChoose, h]

private lemma card_middle_fiber {k : ℕ} (i j : Fin (k + 1)) (r : Fin (2 * k + 1)) :
    (Nat.card {P : StripPath k i j // middleHeight P = r} : ℚ) =
      halfPaths k r i * halfPaths k r j := by
  rw [Nat.card_congr (halfWordsEquiv (i := i) (j := j) r), Nat.card_prod,
    card_wordsWithDescents, card_wordsWithDescents, Nat.cast_mul,
    halfPaths_signedChoose, halfPaths_signedChoose]
  have e : (k : ℤ) + i.val - r.val = (k : ℤ) - ((r.val : ℤ) - i.val) := by omega
  rw [e, signedChoose_reflect]

/-! ### The two matching counts as Gram determinants -/

private lemma finite_trackFamily (k : ℕ) : Finite (TrackFamily k) := by
  let : ∀ i : Fin (k + 1), Finite (StripPath k i i) := fun i ↦ finite_stripPath k i i
  exact Finite.of_injective (fun F : TrackFamily k ↦ F.path) fun F G h ↦
    TrackFamily.ext_cell fun i t ↦ congrFun (congrArg StripPath.cell (congrFun h i)) t

private def familyList {k : ℕ} (F : TrackFamily k) : Fin (k + 1) → List Cell :=
  fun i ↦ pathList (F.path i)

private lemma familyList_injective (k : ℕ) : Function.Injective (@familyList k) := by
  intro F G h
  apply TrackFamily.ext_cell
  intro i t
  have h' := pathList_injective (congrFun h i)
  exact congrFun (congrArg StripPath.cell h') t

private noncomputable def familyFinset (k : ℕ) : Finset (Fin (k + 1) → List Cell) :=
  let := finite_trackFamily k
  letI := Fintype.ofFinite (TrackFamily k)
  (Finset.univ : Finset (TrackFamily k)).map ⟨familyList, familyList_injective k⟩

private lemma mem_familyFinset {k : ℕ} (F : Fin (k + 1) → List Cell) :
    F ∈ familyFinset k ↔ (∀ i, F i ∈ pathFinset k i i) ∧
      ∀ i j, i ≠ j → Disjoint (F i).toFinset (F j).toFinset := by
  classical
  simp only [familyFinset, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨G, rfl⟩
    refine ⟨fun i ↦ mem_pathFinset_iff.mpr ⟨G.path i, rfl⟩, ?_⟩
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro a hai haj
    obtain ⟨s, hs⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hai)
    obtain ⟨t, ht⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp haj)
    exact hij (track_location (F := G) (hs.trans ht.symm)).1
  · rintro ⟨h₁, h₂⟩
    choose P hP using fun i ↦ mem_pathFinset_iff.mp (h₁ i)
    let G : TrackFamily k := {
      path := P
      disjoint := fun i j hij t h ↦ by
        have hi : (P i).cell t ∈ (F i).toFinset := by
          rw [← hP i, List.mem_toFinset]
          exact List.mem_ofFn.mpr ⟨t, rfl⟩
        have hj : (P i).cell t ∈ (F j).toFinset := by
          rw [h, ← hP j, List.mem_toFinset]
          exact List.mem_ofFn.mpr ⟨t, rfl⟩
        exact Finset.disjoint_left.mp (h₂ i j hij) hi hj }
    exact ⟨G, funext hP⟩

private def centralCell (k : ℕ) : Cell := (0, (k : ℤ))

private def avoidsCenter {k : ℕ} (F : TrackFamily k) : Prop :=
  ∀ i, middleHeight (F.path i) ≠ middle k

private lemma centralCell_iff_middleHeight {k : ℕ} {i j : Fin (k + 1)}
    (P : StripPath k i j) : P.cell (middle k) = centralCell k ↔ middleHeight P = middle k := by
  rw [middle_cell]
  constructor
  · intro h
    apply Fin.ext
    have he := congrArg Prod.snd h
    change ((middleHeight P).val : ℤ) = k at he
    change (middleHeight P).val = k
    omega
  · intro h
    rw [h]
    rfl

private lemma centralCell_mem_iff {k : ℕ} {i j : Fin (k + 1)} (P : StripPath k i j) :
    centralCell k ∈ pathList P ↔ middleHeight P = middle k := by
  rw [← centralCell_iff_middleHeight P]
  constructor
  · intro h
    obtain ⟨t, ht⟩ := List.mem_ofFn.mp h
    have hx := (P.column t).symm.trans (congrArg Prod.fst ht)
    change (t.val : ℤ) - k = 0 at hx
    have ht' : t = middle k := Fin.ext (by change t.val = k; omega)
    exact ht' ▸ ht
  · intro h
    exact List.mem_ofFn.mpr ⟨middle k, h⟩

private def lozengeWeight (k : ℕ) (marked : Bool) (_ v : Cell) : ℚ :=
  if marked = true ∧ v = centralCell k then 0 else 1

private lemma pathWeight_tail (k : ℕ) (marked : Bool) (l : List Cell) :
    MetaMathlibExt.lgvPathWeight (lozengeWeight k marked) l =
      if marked = true ∧ centralCell k ∈ l.tail then 0 else 1 := by
  induction l with
  | nil => simp [MetaMathlibExt.lgvPathWeight]
  | cons a l ih =>
    cases l with
    | nil => simp [MetaMathlibExt.lgvPathWeight]
    | cons b l =>
      rw [MetaMathlibExt.lgvPathWeight, ih]
      by_cases hm : marked = true <;> by_cases h : b = centralCell k <;>
        simp [lozengeWeight, hm, h, eq_comm]

private lemma pathWeight_middle {k : ℕ} (hk : 0 < k) {i j : Fin (k + 1)} (marked : Bool)
    (P : StripPath k i j) :
    MetaMathlibExt.lgvPathWeight (lozengeWeight k marked) (pathList P) =
      if marked = true ∧ middleHeight P = middle k then 0 else 1 := by
  rw [pathWeight_tail]
  have h₁ : source k i ≠ centralCell k := by
    intro h
    have he := congrArg Prod.fst h
    change -(k : ℤ) = 0 at he
    omega
  have ht : centralCell k ∈ (pathList P).tail ↔ centralCell k ∈ pathList P := by
    have h₀ := (pathList_chain P).1
    obtain ⟨tail, h⟩ := List.head?_eq_some_iff.mp h₀
    simp [h, Ne.symm h₁]
  by_cases h : marked = true ∧ middleHeight P = middle k
  · rw [ite_eq_left h, ite_eq_left ⟨h.1, ht.mpr ((centralCell_mem_iff P).mpr h.2)⟩]
  · rw [ite_eq_right h, ite_eq_right]
    rintro ⟨hm, hv⟩
    exact h ⟨hm, (centralCell_mem_iff P).mp (ht.mp hv)⟩

private lemma path_weight_sum {k : ℕ} (hk : 0 < k) (marked : Bool) (i j : Fin (k + 1)) :
    (∑ l ∈ pathFinset k i j, MetaMathlibExt.lgvPathWeight (lozengeWeight k marked) l) =
      ∑ r : Fin (2 * k + 1), if marked = true ∧ r = middle k then 0
        else halfPaths k r i * halfPaths k r j := by
  classical
  let := finite_stripPath k i j
  let := Fintype.ofFinite (StripPath k i j)
  rw [pathFinset, Finset.sum_map]
  change (∑ P : StripPath k i j, MetaMathlibExt.lgvPathWeight (lozengeWeight k marked)
    (pathList P)) = _
  rw [← Fintype.sum_fiberwise middleHeight]
  apply Finset.sum_congr rfl
  intro r _
  have h (P : {P : StripPath k i j // middleHeight P = r}) :
      MetaMathlibExt.lgvPathWeight (lozengeWeight k marked) (pathList P.val) =
        if marked = true ∧ r = middle k then 0 else 1 := by
    have he := pathWeight_middle hk marked P.val
    simpa only [P.property] using he
  rw [Finset.sum_congr rfl (fun P _ ↦ h P)]
  by_cases hm : marked = true ∧ r = middle k
  · simp [hm]
  · simp only [hm, ite_false, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    exact card_middle_fiber i j r

open scoped Classical in
private lemma family_weight {k : ℕ} (hk : 0 < k) (marked : Bool) (F : TrackFamily k) :
    (∏ i, MetaMathlibExt.lgvPathWeight (lozengeWeight k marked) (familyList F i)) =
      if marked = true → avoidsCenter F then 1 else 0 := by
  classical
  by_cases h : marked = true → avoidsCenter F
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro i _
    rw [familyList, pathWeight_middle hk marked, ite_eq_right]
    rintro ⟨hm, he⟩
    exact h hm i he
  · rw [ite_eq_right h]
    have hm : marked = true := Classical.byContradiction fun hn ↦ h (fun hh ↦ (hn hh).elim)
    have hbad : ¬avoidsCenter F := fun ha ↦ h (fun _ ↦ ha)
    obtain ⟨i, hi⟩ := not_forall.mp hbad
    have hi' : middleHeight (F.path i) = middle k := not_ne_iff.mp hi
    let f (j : Fin (k + 1)) := MetaMathlibExt.lgvPathWeight (lozengeWeight k marked)
      (familyList F j)
    have hf : f i = 0 := by
      dsimp only [f, familyList]
      rw [pathWeight_middle hk marked]
      simp [hm, hi']
    change ∏ j, f j = 0
    rw [← Finset.mul_prod_erase _ f (Finset.mem_univ i), hf, zero_mul]

private lemma family_weight_sum {k : ℕ} (hk : 0 < k) (marked : Bool) :
    (∑ F ∈ familyFinset k, ∏ i, MetaMathlibExt.lgvPathWeight (lozengeWeight k marked) (F i)) =
      (Nat.card {F : TrackFamily k // marked = true → avoidsCenter F} : ℚ) := by
  classical
  let := finite_trackFamily k
  let := Fintype.ofFinite (TrackFamily k)
  rw [familyFinset, Finset.sum_map]
  change (∑ F : TrackFamily k,
    ∏ i, MetaMathlibExt.lgvPathWeight (lozengeWeight k marked) (familyList F i)) = _
  simp_rw [family_weight hk marked]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

private def countMatrix (k : ℕ) (marked : Bool) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  of fun i j ↦ ∑ r : Fin (2 * k + 1), if marked = true ∧ r = middle k then 0
    else halfPaths k r i * halfPaths k r j

private lemma card_families_eq_det {k : ℕ} (hk : 0 < k) (marked : Bool) :
    (Nat.card {F : TrackFamily k // marked = true → avoidsCenter F} : ℚ) =
      (countMatrix k marked).det := by
  rw [← family_weight_sum hk marked]
  exact MetaMathlibExt.lindstrom_gessel_viennot_weighted (k + 1) (directedStep k)
    (source k) (sink k) (pathRank k) (fun _ _ h ↦ pathRank_increases h) (pathFinset k)
    pathFinset_spec (lozengeWeight k marked) (countMatrix k marked)
    (fun i j ↦ (path_weight_sum hk marked i j).symm)
    (fun i j a b hij hba p hp q hq ↦ pathFinset_planar i j a b hij hba p hp q hq)
    (familyFinset k) mem_familyFinset

private lemma countMatrix_total (k : ℕ) : countMatrix k false = (halfPaths k)ᵀ * halfPaths k := by
  ext i j
  simp [countMatrix, Matrix.mul_apply]

private lemma countMatrix_marked (k : ℕ) : countMatrix k true =
    (halfPaths k)ᵀ * halfPaths k - vecMulVec (halfPaths k (middle k)) (halfPaths k (middle k)) := by
  ext i j
  simp only [countMatrix, Matrix.of_apply, true_and, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.transpose_apply, vecMulVec_apply]
  let f (r : Fin (2 * k + 1)) := halfPaths k r i * halfPaths k r j
  change (∑ r, if r = middle k then 0 else f r) = ∑ r, f r - f (middle k)
  have hs : (∑ r, if r = middle k then 0 else f r) +
      (∑ r, if r = middle k then f r else 0) = ∑ r, f r := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : r = middle k <;> simp [hr]
  rw [Fintype.sum_ite_eq'] at hs
  exact eq_sub_iff_add_eq.mpr hs

private abbrev MarkedPerfect (k : ℕ) :=
  {M : (hexagonGraph k (k + 1) k).Subgraph // M.IsPerfectMatching ∧
    ∀ s t, s.val = (0, (k : ℤ), false) → t.val = (-1, (k : ℤ), true) → M.Adj s t}

private noncomputable def totalFamilyEquiv {k : ℕ} (hk : 0 < k) : Perfect k ≃
    {F : TrackFamily k // false = true → avoidsCenter F} :=
  (perfectEquivTracks hk).trans {
    toFun F := ⟨F, by simp⟩
    invFun := Subtype.val
    left_inv _ := rfl
    right_inv _ := rfl }

private noncomputable def markedFamilyEquiv {k : ℕ} (hk : 0 < k) : MarkedPerfect k ≃
    {F : TrackFamily k // true = true → avoidsCenter F} := by
  let e : MarkedPerfect k ≃
      {M : Perfect k // ∀ s t, s.val = (0, (k : ℤ), false) → t.val = (-1, (k : ℤ), true) →
        M.val.Adj s t} := {
    toFun M := ⟨⟨M.val, M.property.1⟩, M.property.2⟩
    invFun M := ⟨M.val.val, M.val.property, M.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  refine e.trans ((markedEquivTracks hk).trans ?_)
  refine {
    toFun := fun F ↦ ⟨F.val, fun _ i ↦ fun he ↦
      F.property i ((centralCell_iff_middleHeight (F.val.path i)).mpr he)⟩
    invFun := fun F ↦ ⟨F.val, fun i h ↦ F.property rfl i
      ((centralCell_iff_middleHeight (F.val.path i)).mp h)⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }

/-- Total number of exact perfect-matching subgraphs, after casting to the rationals. -/
private lemma card_perfect_eq_det {k : ℕ} (hk : 0 < k) :
    (Nat.card (Perfect (k : ℤ)) : ℚ) = ((halfPaths k)ᵀ * halfPaths k).det := by
  rw [Nat.card_congr (totalFamilyEquiv hk), card_families_eq_det hk false, countMatrix_total]

/-- The exact marked-edge condition deletes just the middle row of the Gram factor. -/
private lemma card_marked_eq_det {k : ℕ} (hk : 0 < k) :
    (Nat.card (MarkedPerfect k) : ℚ) =
      ((halfPaths k)ᵀ * halfPaths k -
        vecMulVec (halfPaths k (middle k)) (halfPaths k (middle k))).det := by
  rw [Nat.card_congr (markedFamilyEquiv hk), card_families_eq_det hk true, countMatrix_marked]

end CentralLozengeGram

open Matrix

namespace CentralLozengeProjection

private def joinCols {α β γ : Type} (B : Matrix α β ℚ) (C : Matrix α γ ℚ) :
    Matrix α (β ⊕ γ) ℚ := of fun i ↦ Sum.elim (B i) (C i)

private def joinRows {α β γ : Type} (L : Matrix β α ℚ) (M : Matrix γ α ℚ) :
    Matrix (β ⊕ γ) α ℚ := of (Sum.elim L M)

private lemma joinRows_mul_joinCols {α β γ : Type} [Fintype α]
    (L : Matrix β α ℚ) (M : Matrix γ α ℚ) (B : Matrix α β ℚ) (C : Matrix α γ ℚ) :
    joinRows L M * joinCols B C = fromBlocks (L * B) (L * C) (M * B) (M * C) := by
  ext i j
  cases i <;> cases j <;> rfl

private lemma joinCols_mul_joinRows {α β γ : Type} [Fintype β] [Fintype γ]
    (L : Matrix β α ℚ) (M : Matrix γ α ℚ) (B : Matrix α β ℚ) (C : Matrix α γ ℚ) :
    joinCols B C * joinRows L M = B * L + C * M := by
  ext i j
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.add_apply]
  rfl

/-- The two complementary column spans give complementary projectors. -/
private lemma complementary_projectors {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (e : β ⊕ γ ≃ α) (B : Matrix α β ℚ) (C : Matrix α γ ℚ)
    (h : γ → ℚ) (hG : IsUnit (Bᵀ * B).det) (hh : ∀ j, h j ≠ 0)
    (hBC : Bᵀ * C = 0) (hCC : Cᵀ * C = diagonal h) :
    B * ((Bᵀ * B)⁻¹ * Bᵀ) + C * (diagonal (fun j ↦ (h j)⁻¹) * Cᵀ) = 1 := by
  let L : Matrix β α ℚ := (Bᵀ * B)⁻¹ * Bᵀ
  let M : Matrix γ α ℚ := diagonal (fun j ↦ (h j)⁻¹) * Cᵀ
  have hCB : Cᵀ * B = 0 := by
    simpa only [transpose_mul, transpose_transpose, transpose_zero] using
      congrArg Matrix.transpose hBC
  have hMM : diagonal (fun j ↦ (h j)⁻¹) * diagonal h = 1 := by
    rw [diagonal_mul_diagonal]
    simpa only [inv_mul_cancel₀ (hh _)] using (diagonal_one : diagonal (fun _ : γ ↦ (1 : ℚ)) = 1)
  have hLeft : joinRows L M * joinCols B C = 1 := by
    rw [joinRows_mul_joinCols]
    dsimp only [L, M]
    simp only [Matrix.mul_assoc, hBC, hCB, hCC, Matrix.mul_zero, hMM,
      nonsing_inv_mul _ hG, fromBlocks_one]
  have hRight := (Matrix.mul_eq_one_comm_of_equiv e).mp hLeft
  simpa only [joinCols_mul_joinRows, L, M] using hRight

/-- Deleting one row in the rectangular Gram factor gives the complementary projection at it. -/
private lemma determinant_remove_row {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    (e : β ⊕ γ ≃ α) (B : Matrix α β ℚ) (C : Matrix α γ ℚ)
    (h : γ → ℚ) (hG : IsUnit (Bᵀ * B).det) (hh : ∀ j, h j ≠ 0)
    (hBC : Bᵀ * C = 0) (hCC : Cᵀ * C = diagonal h) (r : α) :
    ((Bᵀ * B) - vecMulVec (B r) (B r)).det =
      (Bᵀ * B).det * ∑ j, C r j ^ 2 / h j := by
  classical
  let G : Matrix β β ℚ := Bᵀ * B
  have hp := congrArg (fun A : Matrix α α ℚ ↦ A r r)
    (complementary_projectors e B C h hG hh hBC hCC)
  have hB : (B * (G⁻¹ * Bᵀ)) r r = B r ⬝ᵥ G⁻¹ *ᵥ B r := by
    simp [Matrix.mul_apply, mulVec, dotProduct]
  have hC : (C * (diagonal (fun j ↦ (h j)⁻¹) * Cᵀ)) r r =
      ∑ j, C r j ^ 2 / h j := by
    rw [← Matrix.mul_assoc, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.mul_diagonal, transpose_apply, div_eq_mul_inv]
    ring
  change (G - vecMulVec (B r) (B r)).det = G.det * _
  have hw : vecMulVec (B r) (B r) = replicateCol Unit (B r) * replicateRow Unit (B r) := by
    ext i j
    simp [vecMulVec_apply, Matrix.mul_apply]
  have hg : G * G⁻¹ = 1 := mul_nonsing_inv _ hG
  have hm : G - vecMulVec (B r) (B r) =
      G * (1 - (G⁻¹ * replicateCol Unit (B r)) * replicateRow Unit (B r)) := by
    rw [hw, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc G, ← Matrix.mul_assoc G,
      hg, Matrix.one_mul]
  rw [hm, Matrix.det_mul, Matrix.det_one_sub_mul_comm]
  congr 1
  rw [Matrix.det_unique]
  change (B * (G⁻¹ * Bᵀ)) r r + (C * (diagonal (fun j ↦ (h j)⁻¹) * Cᵀ)) r r = _ at hp
  rw [hB, hC, Matrix.one_apply_eq] at hp
  have hs : (replicateRow Unit (B r) * (G⁻¹ * replicateCol Unit (B r))) () () =
      B r ⬝ᵥ G⁻¹ *ᵥ B r := by
    simp [Matrix.mul_apply, mulVec, dotProduct]
  change 1 - (replicateRow Unit (B r) * (G⁻¹ * replicateCol Unit (B r))) () () = _
  rw [hs, ← hp]
  ring

end CentralLozengeProjection

namespace CentralLozengeComplement

/-- Signed evaluations of the polynomials on the middle rows. -/
private def complement (k : ℕ) (q : ℕ → ℚ[X]) : Matrix (Fin (2 * k + 1)) (Fin k) ℚ :=
  Matrix.of fun r d ↦ (-1 : ℚ) ^ r.val * (q d.val).eval (r.val : ℚ)

private lemma sign_shift (i k j : ℕ) (hj : j ≤ k) :
    (-1 : ℚ) ^ (i + j) = (-1 : ℚ) ^ (i + k) * (-1 : ℚ) ^ (k - j) := by
  calc
    (-1 : ℚ) ^ (i + j) = (-1 : ℚ) ^ ((i + j) + 2 * (k - j)) := by
      rw [pow_add (-1 : ℚ) (i + j), pow_mul]
      norm_num
    _ = _ := by
      rw [show (i + j) + 2 * (k - j) = i + k + (k - j) by omega, pow_add]

/-- The binomial coefficients are supported on the translated difference window. -/
private lemma halfPaths_transpose_mul_complement (k : ℕ) (q : ℕ → ℚ[X])
    (hdeg : ∀ d < k, (q d).natDegree ≤ d) :
    (CentralLozengeGram.halfPaths k)ᵀ * complement k q = 0 := by
  ext i d
  let f : ℕ → ℚ := fun x ↦
    (if i.val ≤ x then (k.choose (x - i.val) : ℚ) else 0) *
      ((-1 : ℚ) ^ x * (q d.val).eval (x : ℚ))
  change (∑ r : Fin (2 * k + 1), f r.val) = 0
  rw [Fin.sum_univ_eq_sum_range]
  have hwindow :
      (∑ x ∈ Finset.range (2 * k + 1), f x) =
        ∑ x ∈ Finset.Ico i.val (i.val + (k + 1)), f x := by
    symm
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_Ico] at hx
      have hi := i.isLt
      exact Finset.mem_range.mpr (by omega)
    · intro x _ hx
      by_cases hi : i.val ≤ x
      · have hchoose : k < x - i.val := by
          simp only [Finset.mem_Ico, not_and, not_lt] at hx
          have := hx hi
          omega
        simp [f, hi, Nat.choose_eq_zero_of_lt hchoose]
      · simp [f, hi]
  rw [hwindow, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  calc
    (∑ j ∈ Finset.range (k + 1), f (i.val + j)) =
        (-1 : ℚ) ^ (i.val + k) *
          (CentralLozengeDifferences.differences 1 k (q d.val)).eval (i.val : ℚ) := by
      rw [CentralLozengeDifferences.differences_eval_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjk : j ≤ k := by simpa using hj
      simp only [f, Nat.le_add_right, ite_true, Nat.add_sub_cancel_left, Nat.cast_add, mul_one]
      rw [sign_shift i.val k j hjk]
      ring
    _ = 0 := by
      have hd : (q d.val).natDegree < k := (hdeg d.val d.isLt).trans_lt d.isLt
      rw [CentralLozengeDifferences.differences_eq_zero 1 k _ hd, eval_zero, mul_zero]

/-- The row signs cancel in the Gram matrix of the complementary columns. -/
private lemma complement_gram (k : ℕ) (q : ℕ → ℚ[X]) (h : ℕ → ℚ)
    (horth : ∀ i j : Fin k,
      (∑ x ∈ Finset.range (2 * k + 1), (q i.val).eval (x : ℚ) * (q j.val).eval (x : ℚ)) =
        if i = j then h i.val else 0) :
    (complement k q)ᵀ * complement k q = diagonal (fun i ↦ h i.val) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  simp only [Matrix.transpose_apply, complement, Matrix.of_apply]
  rw [← horth i j, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r _
  have hs : (-1 : ℚ) ^ r.val * (-1 : ℚ) ^ r.val = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    ((-1 : ℚ) ^ r.val * (q i.val).eval (r.val : ℚ)) *
        ((-1 : ℚ) ^ r.val * (q j.val).eval (r.val : ℚ)) =
        ((-1 : ℚ) ^ r.val * (-1 : ℚ) ^ r.val) *
          ((q i.val).eval (r.val : ℚ) * (q j.val).eval (r.val : ℚ)) := by ring
    _ = _ := by rw [hs, one_mul]

/-- The middle-row deletion determinant in terms of the squared polynomial evaluations. -/
private lemma determinant_eq_projection (k : ℕ) (q : ℕ → ℚ[X]) (h : ℕ → ℚ)
    (hdeg : ∀ d < k, (q d).natDegree ≤ d)
    (horth : ∀ i j : Fin k,
      (∑ x ∈ Finset.range (2 * k + 1), (q i.val).eval (x : ℚ) * (q j.val).eval (x : ℚ)) =
        if i = j then h i.val else 0)
    (hh : ∀ d < k, h d ≠ 0) :
    let B := CentralLozengeGram.halfPaths k
    let G := Bᵀ * B
    let r : Fin (2 * k + 1) := ⟨k, by omega⟩
    (G - Matrix.vecMulVec (B r) (B r)).det =
      G.det * ∑ d ∈ Finset.range k, (q d).eval (k : ℚ) ^ 2 / h d := by
  let B := CentralLozengeGram.halfPaths k
  let G := Bᵀ * B
  let r : Fin (2 * k + 1) := ⟨k, by omega⟩
  let e : Fin (k + 1) ⊕ Fin k ≃ Fin (2 * k + 1) :=
    finSumFinEquiv.trans (finCongr (by omega))
  change (G - Matrix.vecMulVec (B r) (B r)).det = _
  rw [CentralLozengeProjection.determinant_remove_row e B (complement k q) (fun d ↦ h d.val)
    (Matrix.isUnit_iff_isUnit_det _ |>.mp (CentralLozengeGram.gram_isUnit k))
    (fun d ↦ hh d.val d.isLt) (halfPaths_transpose_mul_complement k q hdeg)
    (complement_gram k q h horth) r]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro d _
  simp only [complement, Matrix.of_apply, r]
  rw [mul_pow, ← pow_mul, Nat.mul_comm k 2, pow_mul]
  norm_num

end CentralLozengeComplement

namespace CentralLozengeNormArithmetic

/-- The squared norm used to normalize the degree `d` contribution. -/
private def sqNorm (N d : ℕ) : ℚ :=
  (d.factorial : ℚ)^4 / ((2 * d).factorial : ℚ) * ((N + d + 1).choose (2 * d + 1) : ℚ)

/-- The degree `d` coefficient in the monic three-term recurrence. -/
private def recCoeff (N d : ℕ) : ℚ :=
  (d : ℚ)^2 * (N + (d : ℚ) + 1) * (N - (d : ℚ) + 1) /
    (4 * (2 * (d : ℚ) - 1) * (2 * (d : ℚ) + 1))

private lemma sqNorm_pos {N d : ℕ} (hd : d ≤ N) : 0 < sqNorm N d := by
  have hc : 0 < (N + d + 1).choose (2 * d + 1) := Nat.choose_pos (by omega)
  unfold sqNorm
  positivity

private lemma sqNorm_factorial {N d : ℕ} (hd : d ≤ N) :
    sqNorm N d = (d.factorial : ℚ)^4 * ((N + d + 1).factorial : ℚ) /
      (((2 * d).factorial : ℚ)^2 * (2 * (d : ℚ) + 1) * ((N - d).factorial : ℚ)) := by
  have h := Nat.choose_mul_factorial_mul_factorial
    (show 2 * d + 1 ≤ N + d + 1 by omega)
  rw [show N + d + 1 - (2 * d + 1) = N - d by omega] at h
  have hc : ((N + d + 1).choose (2 * d + 1) : ℚ) * ((2 * d + 1).factorial : ℚ) *
      ((N - d).factorial : ℚ) = ((N + d + 1).factorial : ℚ) := by exact_mod_cast h
  rw [Nat.factorial_succ (2 * d)] at hc
  push_cast at hc
  rw [sqNorm, ← hc]
  field_simp

private lemma sqNorm_succ {N d : ℕ} (hd : d + 1 ≤ N) :
    sqNorm N (d + 1) = recCoeff N (d + 1) * sqNorm N d := by
  rw [sqNorm_factorial hd, sqNorm_factorial (show d ≤ N by omega), recCoeff,
    show N + (d + 1) + 1 = (N + d + 1) + 1 by omega, Nat.factorial_succ (N + d + 1),
    show 2 * (d + 1) = (2 * d + 1) + 1 by omega, Nat.factorial_succ (2 * d + 1),
    Nat.factorial_succ (2 * d), Nat.factorial_succ d,
    show N - d = (N - (d + 1)) + 1 by omega, Nat.factorial_succ (N - (d + 1))]
  push_cast
  rw [Nat.cast_sub hd]
  push_cast
  have hd' : (d : ℚ) + 1 ≤ N := by exact_mod_cast hd
  have hd₀ : 0 ≤ (d : ℚ) := by positivity
  field_simp (disch := first | positivity | linarith)
  ring

private lemma center_step_ratio {n i : ℕ} (hi : i + 1 < n) :
    recCoeff (2 * (2 * n - 1)) (2 * i + 1) / recCoeff (2 * (2 * n - 1)) (2 * i + 2) =
      CentralLozengeArithmetic.step n (i + 1 : ℚ) := by
  have hn : 1 ≤ 2 * n := by omega
  have hi' : (i : ℚ) + 1 + 1 ≤ n := by exact_mod_cast (show i + 1 + 1 ≤ n by omega)
  have hi₀ : 0 ≤ (i : ℚ) := by positivity
  unfold recCoeff CentralLozengeArithmetic.step
  rw [Nat.cast_mul, Nat.cast_sub hn]
  push_cast
  field_simp (disch := first | positivity | linarith)
  ring

/-- The in-range center recurrence gives the summands of the one-third telescope. -/
private lemma sum_center_weights {n : ℕ} (hn : 1 ≤ n) (v : ℕ → ℚ)
    (h0 : v 0 = 1) (h1 : v 1 = 0)
    (hrec : ∀ d : ℕ, d + 2 < 2 * n - 1 →
      v (d + 2) = -recCoeff (2 * (2 * n - 1)) (d + 1) * v d) :
    ∑ d ∈ Finset.range (2 * n - 1), v d ^ 2 / sqNorm (2 * (2 * n - 1)) d = 1 / 3 := by
  let N := 2 * (2 * n - 1)
  let w (d : ℕ) := v d ^ 2 / sqNorm N d
  have wzero : w 0 = CentralLozengeArithmetic.term n 0 := by
    simp only [w, sqNorm, h0, N, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.factorial_zero,
      Nat.cast_one, one_pow, div_one, one_mul, Nat.choose_one_right,
      CentralLozengeArithmetic.term, Finset.range_zero, Finset.prod_empty]
    push_cast
    rw [Nat.cast_sub (show 1 ≤ 2 * n by omega)]
    push_cast
    ring
  have wstep (d : ℕ) (hd : d + 2 < 2 * n - 1) :
      w (d + 2) = w d * (recCoeff N (d + 1) / recCoeff N (d + 2)) := by
    have hd₀ : d ≤ N := by dsimp [N]; omega
    have hd₁ : d + 1 ≤ N := by dsimp [N]; omega
    have hd₂ : d + 1 + 1 ≤ N := by dsimp [N]; omega
    have hnorm₀ := (sqNorm_pos hd₀).ne'
    have hnorm₁ := (sqNorm_pos hd₁).ne'
    have hnorm₂ := (sqNorm_pos hd₂).ne'
    have hco₁ := (mul_ne_zero_iff.mp (sqNorm_succ hd₁ ▸ hnorm₁)).1
    have hco₂ := (mul_ne_zero_iff.mp (sqNorm_succ hd₂ ▸ hnorm₂)).1
    dsimp only [w]
    rw [hrec d hd, sqNorm_succ hd₂, sqNorm_succ hd₁]
    field_simp
    ring
  have heven (i : ℕ) (hi : i < n) : w (2 * i) = CentralLozengeArithmetic.term n i := by
    induction i with
    | zero => simpa only [Nat.mul_zero] using wzero
    | succ i ih =>
        rw [show 2 * (i + 1) = 2 * i + 2 by omega, wstep _ (by omega), ih (by omega),
          center_step_ratio hi, CentralLozengeArithmetic.term_succ]
  have hodd (i : ℕ) (hi : i + 1 < n) : v (2 * i + 1) = 0 := by
    induction i with
    | zero => simpa only [Nat.mul_zero, Nat.zero_add] using h1
    | succ i ih =>
        rw [show 2 * (i + 1) + 1 = (2 * i + 1) + 2 by omega,
          hrec _ (by omega), ih (by omega), mul_zero]
  have hsum (i : ℕ) (hi : i < n) :
      ∑ d ∈ Finset.range (2 * i + 1), w d =
        ∑ j ∈ Finset.range (i + 1), CentralLozengeArithmetic.term n j := by
    induction i with
    | zero => simpa only [Nat.mul_zero, Nat.zero_add, Finset.sum_range_one] using wzero
    | succ i ih =>
        conv_lhs =>
          rw [show 2 * (i + 1) + 1 = (2 * i + 1) + 1 + 1 by omega,
            Finset.sum_range_succ, Finset.sum_range_succ]
        rw [ih (by omega), show w (2 * i + 1) = 0 by simp [w, hodd i hi], add_zero,
          show 2 * i + 1 + 1 = 2 * (i + 1) by omega, heven _ hi]
        conv_rhs => rw [Finset.sum_range_succ]
  change ∑ d ∈ Finset.range (2 * n - 1), w d = _
  have h := hsum (n - 1) (by omega)
  rw [show 2 * (n - 1) + 1 = 2 * n - 1 by omega, show n - 1 + 1 = n by omega] at h
  rw [h, CentralLozengeArithmetic.sum_term_eq_third hn]

end CentralLozengeNormArithmetic

namespace CentralLozengeOrthogonal

noncomputable section

open CentralLozengeDifferences CentralLozengeNormArithmetic
open Finset

/-! Use discrete Rodrigues polynomials and their recurrence at the center to turn the
complementary projection into the sum evaluated above. -/

/-- The boundary factors in the discrete Rodrigues formula. -/
private def rod (N d : ℕ) : ℚ[X] :=
  ∏ j ∈ range d, (X - C (j : ℚ)) * (X - C ((N : ℚ) + d - j))

private lemma rod_monic (N d : ℕ) : (rod N d).Monic := by
  apply monic_prod_of_monic
  intro j _
  exact (monic_X_sub_C _).mul (monic_X_sub_C _)

private lemma rod_degree (N d : ℕ) : (rod N d).natDegree = 2 * d := by
  rw [rod, natDegree_prod_of_monic _ _ (fun _ _ ↦ (monic_X_sub_C _).mul (monic_X_sub_C _))]
  calc
    _ = ∑ _j ∈ range d, (2 : ℕ) := by
      apply sum_congr rfl
      intro j _
      rw [natDegree_mul (monic_X_sub_C (j : ℚ)).ne_zero
        (monic_X_sub_C ((N : ℚ) + d - j)).ne_zero, natDegree_X_sub_C, natDegree_X_sub_C]
    _ = _ := by simp [Nat.mul_comm]

/-- The monic polynomial of degree `d` for the uniform grid `0, …, N`. -/
private def gridPoly (N d : ℕ) : ℚ[X] :=
  C ((d.factorial : ℚ) / ((2 * d).factorial : ℚ)) * differences 1 d (rod N d)

private lemma gridPoly_top (N d : ℕ) :
    (gridPoly N d).natDegree ≤ d ∧ (gridPoly N d).coeff d = 1 := by
  have hr : (rod N d).natDegree = d + d := by rw [rod_degree, two_mul]
  have hc : (rod N d).coeff (d + d) = 1 := by
    rw [← hr]; exact rod_monic N d
  obtain ⟨hdeg, hcoeff⟩ := differences_top 1 d d (rod N d) hr.le
  refine ⟨(natDegree_C_mul_le _ _).trans hdeg, ?_⟩
  rw [gridPoly, coeff_C_mul, hcoeff, hc, one_pow, mul_one, mul_one, ← two_mul]
  field_simp

private lemma gridPoly_degree (N d : ℕ) : (gridPoly N d).natDegree = d := by
  obtain ⟨h, hc⟩ := gridPoly_top N d
  exact natDegree_eq_of_le_of_coeff_ne_zero h (by simp [hc])

private lemma gridPoly_monic (N d : ℕ) : (gridPoly N d).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one d (gridPoly_top N d).1 (gridPoly_top N d).2

private lemma gridPoly_zero (N : ℕ) : gridPoly N 0 = 1 :=
  eq_one_of_monic_natDegree_zero (gridPoly_monic N 0) (gridPoly_degree N 0)

private lemma rod_eval (N d : ℕ) (x : ℚ) : (rod N d).eval x =
    ∏ j ∈ range d, (x - j) * (x - ((N : ℚ) + d - j)) := by
  simp [rod, eval_prod]

private lemma rod_eval_reflect (N d : ℕ) (x : ℚ) :
    (rod N d).eval ((N : ℚ) + d - x) = (rod N d).eval x := by
  rw [rod_eval, rod_eval]
  apply prod_congr rfl
  intro j _
  ring

private lemma rod_eval_zero {N d y : ℕ} (h : y < d ∨ N < y ∧ y ≤ N + d) :
    (rod N d).eval (y : ℚ) = 0 := by
  rw [rod_eval]
  rcases h with h | ⟨h₁, h₂⟩
  · exact prod_eq_zero (mem_range.mpr h) (by simp)
  · have hj : N + d - y < d := by omega
    refine prod_eq_zero (mem_range.mpr hj) ?_
    have he : ((N : ℚ) + d - (N + d - y : ℕ)) = y := by
      rw [Nat.cast_sub h₂, Nat.cast_add]; ring
    rw [he, sub_self, mul_zero]

private lemma signed_coeff (d j : ℕ) (hj : j ≤ d) :
    (-1 : ℚ)^d * (-1 : ℚ)^(d - j) = (-1 : ℚ)^j := by
  rw [← Nat.sub_add_cancel hj, pow_add]
  have hs (a : ℕ) : (-1 : ℚ)^a * (-1 : ℚ)^a = 1 := by rw [← mul_pow]; norm_num
  have he : (d - j + j - j) = d - j := by omega
  rw [he]
  calc
    _ = ((-1 : ℚ)^(d - j) * (-1 : ℚ)^(d - j)) * (-1 : ℚ)^j := by ring
    _ = _ := by rw [hs, one_mul]

private lemma gridPoly_reflect (N d : ℕ) (x : ℚ) :
    (gridPoly N d).eval ((N : ℚ) - x) = (-1 : ℚ)^d * (gridPoly N d).eval x := by
  simp only [gridPoly, eval_mul, eval_C, differences_eval_sum, mul_one, mul_sum]
  rw [← sum_flip]
  apply sum_congr rfl
  intro j hj
  have hj' : j ≤ d := by simpa using hj
  rw [Nat.choose_symm hj', show d - (d - j) = j by omega, Nat.cast_sub hj']
  rw [show (N : ℚ) - x + (d - (j : ℚ)) = (N : ℚ) + d - (x + j) by ring,
    rod_eval_reflect, ← signed_coeff d j hj']
  ring

/-- Move a forward translate to the other factor of the sum and drop the zero boundary terms. -/
private lemma shift_rod_sum {N d j : ℕ} (hj : j ≤ d) (f : ℚ[X]) :
    (∑ x ∈ range (N + 1), f.eval (x : ℚ) * (rod N d).eval ((x : ℚ) + j)) =
      ∑ y ∈ Ico d (N + 1), f.eval ((y : ℚ) - j) * (rod N d).eval (y : ℚ) := by
  let g (y : ℕ) := f.eval ((y : ℚ) - j) * (rod N d).eval (y : ℚ)
  calc
    _ = ∑ x ∈ range (N + 1), g (x + j) := by
      apply sum_congr rfl
      intro x _
      simp [g]
    _ = ∑ y ∈ Ico j (N + 1 + j), g y := by
      rw [range_eq_Ico]
      change (∑ x ∈ Ico 0 (N + 1), g ((addRightEmbedding j) x)) = _
      rw [← sum_map, map_add_right_Ico, zero_add]
    _ = _ := by
      symm
      apply sum_subset
      · intro y hy
        simp only [mem_Ico] at hy ⊢
        omega
      · intro y hy hn
        simp only [mem_Ico, not_and_or] at hy hn
        have hz : y < d ∨ N < y ∧ y ≤ N + d := by omega
        simp [rod_eval_zero hz]

/-- For our convention `Δₐ = Tₐ - 1`, the adjoint of `Δ₁` here is `Δ₋₁` (not its negative). -/
private lemma rod_adjoint (N d : ℕ) (f : ℚ[X]) :
    (∑ x ∈ range (N + 1), f.eval (x : ℚ) * (differences 1 d (rod N d)).eval (x : ℚ)) =
      ∑ y ∈ Ico d (N + 1), (differences (-1) d f).eval (y : ℚ) * (rod N d).eval (y : ℚ) := by
  simp only [differences_eval_sum, mul_one, mul_neg, ← sub_eq_add_neg, mul_sum, sum_mul]
  rw [sum_comm]
  calc
    _ = ∑ j ∈ range (d + 1), (d.choose j : ℚ) * (-1 : ℚ)^(d-j) *
        (∑ x ∈ range (N + 1), f.eval (x : ℚ) * (rod N d).eval ((x : ℚ) + j)) := by
      apply sum_congr rfl
      intro j _
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      ring
    _ = ∑ j ∈ range (d + 1), (d.choose j : ℚ) * (-1 : ℚ)^(d-j) *
        (∑ y ∈ Ico d (N + 1), f.eval ((y : ℚ) - j) * (rod N d).eval (y : ℚ)) := by
      apply sum_congr rfl
      intro j hj
      rw [shift_rod_sum (by simpa using hj)]
    _ = _ := by
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro y _
      apply sum_congr rfl
      intro j _
      ring

/-- The discrete bilinear form on the uniform grid. -/
private def gridPair (N : ℕ) (f g : ℚ[X]) : ℚ :=
  ∑ x ∈ range (N + 1), f.eval (x : ℚ) * g.eval (x : ℚ)

private lemma gridPair_rodrigues (N d : ℕ) (f : ℚ[X]) : gridPair N f (gridPoly N d) =
    (d.factorial : ℚ) / ((2 * d).factorial : ℚ) *
      ∑ y ∈ Ico d (N + 1), (differences (-1) d f).eval (y : ℚ) * (rod N d).eval (y : ℚ) := by
  rw [← rod_adjoint]
  simp only [gridPair, gridPoly, eval_mul, eval_C, mul_sum]
  apply sum_congr rfl
  intro x _
  ring

private lemma gridPair_gridPoly_eq_zero {N d : ℕ} {f : ℚ[X]} (hf : f.natDegree < d) :
    gridPair N f (gridPoly N d) = 0 := by
  simp [gridPair_rodrigues, differences_eq_zero (-1) d f hf]

private def fallValue (d : ℕ) (x : ℚ) : ℚ := ∏ j ∈ range d, (x - j)

private lemma fallValue_eq_desc {d y : ℕ} (h : d ≤ y) :
    fallValue d (y : ℚ) = (y.descFactorial d : ℚ) := by
  induction d with
  | zero => simp [fallValue]
  | succ d ih =>
    rw [fallValue, prod_range_succ, ← fallValue, ih (by omega), Nat.descFactorial_succ,
      Nat.cast_mul, Nat.cast_sub (by omega : d ≤ y), mul_comm]

private lemma rod_eval_choose {N d y : ℕ} (hy : y ∈ Ico d (N + 1)) :
    (rod N d).eval (y : ℚ) = (-1 : ℚ)^d * (d.factorial : ℚ)^2 *
      (y.choose d : ℚ) * ((N + d - y).choose d : ℚ) := by
  have h₁ := (mem_Ico.mp hy).1
  have h₂ := (mem_Ico.mp hy).2
  have hcast : ((N + d - y : ℕ) : ℚ) = (N : ℚ) + d - y := by
    rw [Nat.cast_sub (by omega), Nat.cast_add]
  calc
    _ = ∏ j ∈ range d, ((y : ℚ) - j) * ((-1 : ℚ) * (((N : ℚ) + d - y) - j)) := by
      rw [rod_eval]
      apply prod_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [prod_mul_distrib, prod_mul_distrib, prod_const, card_range,
        ← fallValue, ← fallValue, ← hcast, fallValue_eq_desc h₁,
        fallValue_eq_desc (by omega : d ≤ N + d - y), Nat.descFactorial_eq_factorial_mul_choose,
        Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, Nat.cast_mul]
      ring

/-- A Vandermonde convolution in which `x + a` is the number of positions before a pivot. -/
private lemma choose_pivot (a b L : ℕ) :
    (∑ x ∈ range (L + 1), (x + a).choose a * (L - x + b).choose b) =
      (L + a + b + 1).choose (a + b + 1) := by
  induction b generalizing L with
  | zero => simpa using Nat.sum_range_add_choose L a
  | succ b ih =>
    induction L with
    | zero => simp [Nat.add_assoc]
    | succ L ihL =>
      rw [sum_range_succ]
      simp only [Nat.sub_self, zero_add, Nat.choose_self, mul_one]
      have hsplit :
          (∑ x ∈ range (L + 1), (x + a).choose a * (L + 1 - x + (b + 1)).choose (b + 1)) =
          (∑ x ∈ range (L + 1), (x + a).choose a * (L + 1 - x + b).choose b) +
          (∑ x ∈ range (L + 1), (x + a).choose a * (L - x + (b + 1)).choose (b + 1)) := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro x hx
        have hx' : x ≤ L := by simpa using hx
        rw [show L + 1 - x + (b + 1) = (L + 1 - x + b) + 1 by omega,
          Nat.choose_succ_succ', mul_add,
          show L + 1 - x + b = L - x + (b + 1) by omega]
      have hlast := sum_range_succ (fun x ↦ (x + a).choose a * (L + 1 - x + b).choose b)
        (L + 1)
      simp only [Nat.sub_self, zero_add, Nat.choose_self, mul_one] at hlast
      rw [hsplit, add_right_comm, ← hlast, ih, ihL]
      have e₁ : L + 1 + a + (b + 1) + 1 = (L + a + (b + 1) + 1) + 1 := by omega
      have e₂ : a + (b + 1) + 1 = (a + b + 1) + 1 := by omega
      rw [e₁, e₂]
      conv_rhs => rw [Nat.choose_succ_succ']
      rw [show L + 1 + a + b + 1 = L + a + (b + 1) + 1 by omega]

private lemma rod_choose_sum {N d : ℕ} (hd : d ≤ N) :
    (∑ y ∈ Ico d (N + 1), (y.choose d : ℚ) * ((N + d - y).choose d : ℚ)) =
      ((N + d + 1).choose (2 * d + 1) : ℚ) := by
  rw [sum_Ico_eq_sum_range, show N + 1 - d = N - d + 1 by omega]
  calc
    _ = ∑ x ∈ range (N - d + 1), ((x + d).choose d : ℚ) *
        ((N - d - x + d).choose d : ℚ) := by
      apply sum_congr rfl
      intro x hx
      have hx' : x ≤ N - d := by simpa using hx
      rw [Nat.add_comm d x, show N + d - (x + d) = N - d - x + d by omega]
    _ = _ := by
      have h := congrArg (fun z : ℕ ↦ (z : ℚ)) (choose_pivot d d (N - d))
      push_cast at h
      rwa [show N - d + d + d + 1 = N + d + 1 by omega,
        show d + d + 1 = 2 * d + 1 by omega] at h

/-- The squared norm follows by transferring all differences to the other monic factor. -/
private lemma gridPoly_norm {N d : ℕ} (hd : d ≤ N) :
    gridPair N (gridPoly N d) (gridPoly N d) = sqNorm N d := by
  unfold sqNorm
  obtain ⟨hdeg, hcoeff⟩ := differences_top (-1) d 0 (gridPoly N d) (by simp [gridPoly_degree])
  simp only [Nat.zero_add, Nat.factorial_zero, Nat.cast_one, div_one, (gridPoly_top N d).2,
    mul_one] at hcoeff
  have hconst := eq_C_of_natDegree_le_zero hdeg
  rw [gridPair_rodrigues, hconst, hcoeff]
  have hs : (-1 : ℚ)^d * (-1 : ℚ)^d = 1 := by rw [← mul_pow]; norm_num
  calc
    _ = ((d.factorial : ℚ) / ((2 * d).factorial : ℚ)) * ((d.factorial : ℚ)^3 *
        ∑ y ∈ Ico d (N + 1), (y.choose d : ℚ) * ((N + d - y).choose d : ℚ)) := by
      congr 1
      rw [mul_sum]
      apply sum_congr rfl
      intro y hy
      rw [eval_C, rod_eval_choose hy]
      calc
        _ = ((-1 : ℚ)^d * (-1 : ℚ)^d) * ((d.factorial : ℚ)^3 *
            ((y.choose d : ℚ) * ((N + d - y).choose d : ℚ))) := by ring
        _ = _ := by rw [hs, one_mul]
    _ = _ := by rw [rod_choose_sum hd]; ring

private lemma gridPair_comm (N : ℕ) (f g : ℚ[X]) : gridPair N f g = gridPair N g f := by
  simp only [gridPair, mul_comm]

private lemma gridPair_sub (N : ℕ) (f g h : ℚ[X]) :
    gridPair N (f - g) h = gridPair N f h - gridPair N g h := by
  simp only [gridPair, eval_sub, sub_mul, sum_sub_distrib]

private lemma gridPair_scale (N : ℕ) (a : ℚ) (f g : ℚ[X]) :
    gridPair N (C a * f) g = a * gridPair N f g := by
  simp only [gridPair, eval_mul, eval_C, mul_assoc, mul_sum]

private lemma gridPair_mul_switch (N : ℕ) (p f g : ℚ[X]) :
    gridPair N (p * f) g = gridPair N (p * g) f := by
  simp only [gridPair, eval_mul, mul_right_comm]

private lemma gridPoly_orthogonal {N i j : ℕ} (hi : i ≤ N) :
    gridPair N (gridPoly N i) (gridPoly N j) =
      if i = j then sqNorm N i else 0 := by
  rcases lt_trichotomy i j with h | rfl | h
  · rw [ite_eq_right h.ne, gridPair_gridPoly_eq_zero (by rwa [gridPoly_degree])]
  · simpa using gridPoly_norm hi
  · rw [ite_eq_right h.ne', gridPair_comm, gridPair_gridPoly_eq_zero (by rwa [gridPoly_degree])]

private lemma gridPair_eq_zero_of_degree_lt {N d : ℕ} {f : ℚ[X]} (hf : f.degree < d) :
    gridPair N f (gridPoly N d) = 0 := by
  by_cases hz : f = 0
  · simp [hz, gridPair]
  · apply gridPair_gridPoly_eq_zero
    rw [degree_eq_natDegree hz, Nat.cast_lt] at hf
    exact hf

private lemma gridPoly_wdegree (N d : ℕ) : (gridPoly N d).degree = (d : WithBot ℕ) := by
  rw [degree_eq_natDegree (gridPoly_monic N d).ne_zero, gridPoly_degree]

private lemma gridPair_center_zero (k d : ℕ) :
    gridPair (2 * k) ((X - C (k : ℚ)) * gridPoly (2 * k) d) (gridPoly (2 * k) d) = 0 := by
  simp only [gridPair, eval_mul, eval_sub, eval_X, eval_C]
  let f (x : ℕ) : ℚ := ((x : ℚ) - k) * (gridPoly (2 * k) d).eval (x : ℚ) *
    (gridPoly (2 * k) d).eval (x : ℚ)
  change (∑ x ∈ range (2 * k + 1), f x) = 0
  have hr : (∑ x ∈ range (2 * k + 1), f x) = ∑ x ∈ range (2 * k + 1), -f x := by
    rw [← sum_flip]
    apply sum_congr rfl
    intro x hx
    have hle : x ≤ 2 * k := by simpa using hx
    dsimp [f]
    rw [Nat.cast_sub hle, gridPoly_reflect]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    have hs : (-1 : ℚ)^d * (-1 : ℚ)^d = 1 := by rw [← mul_pow]; norm_num
    calc
      _ = ((-1 : ℚ)^d * (-1 : ℚ)^d) *
          (-(((x : ℚ) - k) * (gridPoly (2 * k) d).eval (x : ℚ) *
            (gridPoly (2 * k) d).eval (x : ℚ))) := by ring
      _ = _ := by rw [hs, one_mul]
  rw [sum_neg_distrib] at hr
  linarith

private lemma gridPoly_one_center (k : ℕ) : (gridPoly (2 * k) 1).eval (k : ℚ) = 0 := by
  have h := gridPoly_reflect (2 * k) 1 (k : ℚ)
  push_cast at h
  rw [show (2 : ℚ) * k - k = k by ring, pow_one, neg_one_mul] at h
  linarith

/-- Subtracting the appropriate monic polynomial removes the top coefficient. -/
private lemma gridPoly_drop_top (N d : ℕ) {f : ℚ[X]} (hf : f.degree ≤ d) :
    (f - C (f.coeff d) * gridPoly N d).degree < d := by
  rw [degree_lt_iff_coeff_zero]
  intro j hj
  rw [coeff_sub, coeff_C_mul]
  rcases hj.eq_or_lt with rfl | hj
  · rw [(gridPoly_top N d).2, mul_one, sub_self]
  · have hfj : f.coeff j = 0 := coeff_eq_zero_of_degree_lt (hf.trans_lt (by exact_mod_cast hj))
    have hqj : (gridPoly N d).coeff j = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rwa [gridPoly_degree])
    rw [hfj, hqj, mul_zero, sub_zero]

private lemma natDegree_le_of_degree_lt_succ {f : ℚ[X]} {m : ℕ}
    (h : f.degree < ((m + 1 : ℕ) : WithBot ℕ)) : f.natDegree ≤ m :=
  natDegree_le_iff_coeff_eq_zero.mpr fun j hj ↦ (degree_lt_iff_coeff_zero _ _).mp h j hj

/-- It suffices to test against the monic polynomials up to the degree of the left factor. -/
private lemma gridPair_test (N m : ℕ) {g : ℚ[X]}
    (h : ∀ i ≤ m, gridPair N (gridPoly N i) g = 0) {f : ℚ[X]} (hf : f.natDegree ≤ m) :
    gridPair N f g = 0 := by
  induction m generalizing f with
  | zero =>
      have he : f = C (f.coeff 0) * gridPoly N 0 := by
        rw [gridPoly_zero, mul_one, ← eq_C_of_natDegree_le_zero hf]
      rw [he, gridPair_scale, h 0 le_rfl, mul_zero]
  | succ m ih =>
      have hd := gridPoly_drop_top N (m + 1) (natDegree_le_iff_degree_le.mp hf)
      have hz := ih (fun i hi ↦ h i (by omega)) (natDegree_le_of_degree_lt_succ hd)
      rwa [gridPair_sub, gridPair_scale, h (m + 1) le_rfl, mul_zero, sub_zero] at hz

private lemma gridPair_self_eval_zero {N x : ℕ} {f : ℚ[X]} (hx : x ≤ N)
    (h : gridPair N f f = 0) : f.eval (x : ℚ) = 0 := by
  unfold gridPair at h
  have hz : f.eval (x : ℚ) * f.eval (x : ℚ) = 0 :=
    (sum_eq_zero_iff_of_nonneg (s := range (N + 1)) (f := fun y : ℕ ↦
      f.eval (y : ℚ) * f.eval (y : ℚ)) (fun y _ ↦ mul_self_nonneg (f.eval (y : ℚ)))).mp h x
      (mem_range.mpr (by omega))
  exact (mul_eq_zero.mp hz).elim id id

private lemma gridPoly_monic_center_mul (k d : ℕ) :
    ((X - C (k : ℚ)) * gridPoly (2 * k) d).Monic :=
  (monic_X_sub_C _).mul (gridPoly_monic _ _)

private lemma gridPoly_center_mul_degree (k d : ℕ) :
    ((X - C (k : ℚ)) * gridPoly (2 * k) d).degree = ((d + 1 : ℕ) : WithBot ℕ) := by
  rw [(gridPoly_monic (2 * k) d).degree_mul, degree_X_sub_C,
    gridPoly_wdegree, Nat.cast_add, Nat.cast_one, add_comm]

private lemma gridPoly_center_sub_degree (k d : ℕ) :
    ((X - C (k : ℚ)) * gridPoly (2 * k) d - gridPoly (2 * k) (d + 1)).degree <
      ((d + 1 : ℕ) : WithBot ℕ) := by
  rw [← gridPoly_center_mul_degree]
  apply degree_sub_lt_left
  · rw [gridPoly_center_mul_degree, gridPoly_wdegree]
  · exact (gridPoly_monic_center_mul k d).ne_zero
  · exact (gridPoly_monic_center_mul k d).trans (gridPoly_monic _ _).symm

/-- The three-term recurrence at the center only needs nondegeneracy at that grid point. -/
private lemma gridPoly_center_step (k d : ℕ) (a : ℚ)
    (hn : gridPair (2 * k) (gridPoly (2 * k) (d + 1)) (gridPoly (2 * k) (d + 1)) =
      a * gridPair (2 * k) (gridPoly (2 * k) d) (gridPoly (2 * k) d)) :
    (gridPoly (2 * k) (d + 2)).eval (k : ℚ) = -a * (gridPoly (2 * k) d).eval (k : ℚ) := by
  let N := 2 * k
  let q := gridPoly N
  let u : ℚ[X] := X - C (k : ℚ)
  let g := u * q (d + 1) - q (d + 2) - C a * q d
  have hlow : (u * q (d + 1) - q (d + 2)).natDegree ≤ d + 1 :=
    natDegree_le_of_degree_lt_succ (gridPoly_center_sub_degree k (d + 1))
  have hdeg : g.natDegree ≤ d + 1 := by
    have hscale := (natDegree_C_mul_le a (q d)).trans_eq (gridPoly_degree N d)
    exact (natDegree_sub_le_of_le hlow hscale).trans (max_le le_rfl (by omega))
  have htest (i : ℕ) (hi : i ≤ d + 1) : gridPair N (q i) g = 0 := by
    rw [gridPair_comm, show g = _ from rfl, gridPair_sub, gridPair_sub, gridPair_scale]
    have he₂ : gridPair N (q (d + 2)) (q i) = 0 := by
      rw [gridPair_comm, gridPair_gridPoly_eq_zero (by simpa [q, gridPoly_degree] using
        (show i < d + 2 by omega))]
    rw [he₂, sub_zero]
    rcases lt_trichotomy i d with h | heq | h
    · have hz₁ : gridPair N (u * q (d + 1)) (q i) = 0 := by
        rw [gridPair_mul_switch]
        apply gridPair_eq_zero_of_degree_lt
        rw [show (u * q i).degree = _ from gridPoly_center_mul_degree k i]
        exact_mod_cast (show i + 1 < d + 1 by omega)
      have hz₂ : gridPair N (q d) (q i) = 0 := by
        rw [gridPair_comm, gridPair_gridPoly_eq_zero (by simpa [q, gridPoly_degree] using h)]
      simp [hz₁, hz₂]
    · subst i
      have he : gridPair N (u * q d) (q (d + 1)) = gridPair N (q (d + 1)) (q (d + 1)) := by
        have hz := gridPair_eq_zero_of_degree_lt (N := N) (d := d + 1)
          (gridPoly_center_sub_degree k d)
        rw [gridPair_sub, sub_eq_zero] at hz
        exact hz
      rw [gridPair_mul_switch, he, hn, sub_self]
    · have e : i = d + 1 := by omega
      rw [e, gridPair_center_zero k (d + 1),
        gridPair_gridPoly_eq_zero (by simp [q, gridPoly_degree]), mul_zero, sub_zero]
  have hz := gridPair_self_eval_zero (show k ≤ N by dsimp [N]; omega)
    (gridPair_test N (d + 1) htest hdeg)
  simp only [g, u, eval_sub, eval_mul, eval_C, eval_X, sub_self, zero_mul, zero_sub] at hz
  linarith

/-- The central row contributes exactly one third of the full Gram determinant. -/
private theorem central_row_determinant (n : ℕ) (hn : 1 ≤ n) :
    let k := 2 * n - 1
    let B := CentralLozengeGram.halfPaths k
    let G := Bᵀ * B
    let r : Fin (2 * k + 1) := ⟨k, by omega⟩
    3 * (G - Matrix.vecMulVec (B r) (B r)).det = G.det := by
  let k := 2 * n - 1
  have hweights : ∑ d ∈ Finset.range k,
      (gridPoly (2 * k) d).eval (k : ℚ) ^ 2 / sqNorm (2 * k) d = 1 / 3 := by
    apply sum_center_weights hn (fun d ↦ (gridPoly (2 * k) d).eval (k : ℚ))
    · rw [gridPoly_zero, eval_one]
    · exact gridPoly_one_center k
    · intro d hd
      have hd' : d + 1 ≤ 2 * k := by dsimp [k]; omega
      apply gridPoly_center_step
      rw [gridPoly_norm hd', gridPoly_norm (show d ≤ 2 * k by omega)]
      exact sqNorm_succ hd'
  have hx := CentralLozengeComplement.determinant_eq_projection k (gridPoly (2 * k))
    (sqNorm (2 * k)) (fun d _ ↦ (gridPoly_degree (2 * k) d).le)
    (fun i j ↦ by
      have h := gridPoly_orthogonal (j := j.val) (show i.val ≤ 2 * k by have := i.isLt; omega)
      simpa only [gridPair, Fin.val_inj] using h)
    (fun d hd ↦ (sqNorm_pos (show d ≤ 2 * k by omega)).ne')
  dsimp only at hx ⊢
  change 3 * _ = _
  rw [hx, hweights]
  ring

end

end CentralLozengeOrthogonal


/--
**The central lozenge lies in one third of the tilings.** Let $e_1 = (1, 0)$ and
$e_2 = (1/2, \sqrt{3}/2)$, write $p(i, j) = i e_1 + j e_2$, and call the triangles with vertices
$p(i, j), p(i + 1, j), p(i, j + 1)$ and $p(i + 1, j), p(i, j + 1), p(i + 1, j + 1)$ the upward and
the downward unit triangle $(i, j)$. For every integer $n \ge 1$, let $a = c = 2n - 1$ and
$b = 2n$, and consider the semiregular hexagon with side lengths $a, b, c, a, b, c$ and vertices
$0$, $a e_1$, $a e_1 + b e_2$, $(a - c) e_1 + (b + c) e_2$, $-c e_1 + (b + c) e_2$ and
$-c e_1 + c e_2$, and its dual honeycomb graph, whose vertices are the unit triangles inside the
hexagon and whose edges join triangles sharing an edge. Three times the number of perfect
matchings of this graph that contain the edge joining the upward unit triangle $(0, 2n - 1)$ and
the downward unit triangle $(-1, 2n - 1)$ equals the number of all its perfect matchings. These two
triangles are the innermost ones, so, since perfect matchings of the dual graph are lozenge
tilings, the central location of the hexagon is covered by a lozenge in exactly one third of its
lozenge tilings.

Resolved true by Ciucu and Krattenthaler and, independently, by Helfgott and Gessel.

Source: J. Propp, Twenty open problems in enumeration of matchings (1998),
arXiv:math/9801060, Problem 1; resolution: M. Ciucu and C. Krattenthaler, The number of centered
lozenge tilings of a symmetric hexagon, J. Combin. Theory Ser. A 86 (1999), 103-126; H. Helfgott and
I. M. Gessel, Enumeration of tilings of diamonds and hexagons with defects, Electron. J. Combin. 6
(1999), R16; as recorded by J. Propp, Enumeration of matchings: problems and progress, in New
Perspectives in Algebraic Combinatorics, MSRI Publ. 38 (1999), arXiv:math/9904150, Propp's progress
note on Problem 1: 'Two independent and very different solutions of this problem have been found;
one by Mihai Ciucu and Christian Krattenthaler and the other by Harald Helfgott and Ira Gessel';
Ciucu-Krattenthaler count the rhombus tilings of the hexagon with sides a, a, b, a, a, b containing
the central unit rhombus (a, b of opposite parity), and 'the special case a = 2n - 1, b = 2n solves
Problem 1', https://arxiv.org/abs/math/9904150.
-/
public theorem centralLozengeOneThird_holds : centralLozengeOneThird := by
  intro n hn
  let k : ℕ := 2 * n - 1
  have hk : 0 < k := by dsimp [k]; omega
  have hk₀ : (k : ℤ) = 2 * (n : ℤ) - 1 := by dsimp [k]; omega
  have hk₁ : (k : ℤ) + 1 = 2 * (n : ℤ) := by omega
  let count (a b : ℤ) : Prop :=
    3 * Nat.card {M : (hexagonGraph a b a).Subgraph // M.IsPerfectMatching ∧
      ∀ s t, s.val = (0, a, false) → t.val = (-1, a, true) → M.Adj s t} =
        Nat.card {M : (hexagonGraph a b a).Subgraph // M.IsPerfectMatching}
  change count (2 * (n : ℤ) - 1) (2 * (n : ℤ))
  rw [← hk₀, ← hk₁]
  change 3 * Nat.card (CentralLozengeGram.MarkedPerfect k) = Nat.card (Perfect (k : ℤ))
  have hrat := CentralLozengeOrthogonal.central_row_determinant n hn
  change 3 * (((CentralLozengeGram.halfPaths k)ᵀ * CentralLozengeGram.halfPaths k) -
    Matrix.vecMulVec (CentralLozengeGram.halfPaths k (CentralLozengeGram.middle k))
      (CentralLozengeGram.halfPaths k (CentralLozengeGram.middle k))).det =
        ((CentralLozengeGram.halfPaths k)ᵀ * CentralLozengeGram.halfPaths k).det at hrat
  rw [← CentralLozengeGram.card_perfect_eq_det hk,
    ← CentralLozengeGram.card_marked_eq_det hk] at hrat
  exact_mod_cast hrat

end MathlibExt.Combinatorics.CentralLozengeOneThirdAMR122Problem0001Wanted
