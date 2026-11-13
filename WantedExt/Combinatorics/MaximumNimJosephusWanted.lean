/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.JosephusFunction
public import MathlibExt.GameTheory.SpragueGrundy
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic


namespace MetaMathlibExt

@[expose] public section

/-- **Minimum excludant of a finite set.** For a finite set $s$ of natural numbers,
$\operatorname{mex}(s)$ is the least natural number that does not belong to $s$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 2. -/
public def maximumNimMex (s : Finset ℕ) : ℕ :=
  Nat.find (show ∃ m, m ∉ s by
    let M := (insert 0 s).max' (by simp)
    refine ⟨M + 1, ?_⟩
    intro h
    have hle : M + 1 ≤ M := Finset.le_max' (insert 0 s) (M + 1) (by simp [h])
    omega)

/-- **Characterization of the minimum excludant.** Let $s$ be a finite set of natural numbers and
$m$ a natural number. Then $\operatorname{mex}(s)$, the least natural number not in $s$, equals $m$
if and only if $m \notin s$ and every natural number $n < m$ lies in $s$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 2. -/
public theorem maximumNimMex_eq_iff (s : Finset ℕ) (m : ℕ) :
    maximumNimMex s = m ↔ m ∉ s ∧ ∀ n < m, n ∈ s := by
  unfold maximumNimMex
  rw [Nat.find_eq_iff]
  simp

/-- **Grundy numbers of Maximum Nim.** For a rule function $f : \mathbb{N} \to \mathbb{N}$, the
Grundy number $G_f(x)$ of a pile of $x$ stones in Maximum Nim is defined by recursion on $x$ as the
mex (least natural number not in the set) of $\{G_f(x - u) : 1 \le u \le \min(f(x), x)\}$, the
Grundy numbers of the positions reachable from $x$ by removing $u$ stones.

Taking $\min(f(x), x)$ makes the definition total; under the source's hypotheses on $f$, which
include $f(0) = 0$, it does not change the legal moves.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 2. -/
public def maximumNimGrundy (f : ℕ → ℕ) (x : ℕ) : ℕ :=
  maximumNimMex <|
    (Finset.Icc 1 (min (f x) x)).attach.image fun u =>
      maximumNimGrundy f (x - u.1)
termination_by x
decreasing_by
  have hu := u.property
  simp only [Finset.mem_Icc] at hu
  omega

/-- **Recursive formula for Maximum Nim Grundy numbers.** For every rule function
$f : \mathbb{N} \to \mathbb{N}$ and every pile size $x \in \mathbb{N}$, the Grundy number $G_f(x)$
of a pile of $x$ stones in Maximum Nim with rule function $f$ equals the mex (least natural number
not in the set) of $\{G_f(x - u) : 1 \le u \le \min(f(x), x)\}$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 2. -/
public theorem maximumNimGrundy_eq (f : ℕ → ℕ) (x : ℕ) :
    maximumNimGrundy f x =
      maximumNimMex ((Finset.Icc 1 (min (f x) x)).attach.image fun u =>
        maximumNimGrundy f (x - u.1)) := by
  rw [maximumNimGrundy]

/-- The `k=2` Grundy calculation starts with `G(0)=0`; this private computation
supports the requested examples and introduces no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (characteristic values). -/
private theorem maximumNimGrundy_div_two_zero : maximumNimGrundy (· / 2) 0 = 0 := by
  rw [maximumNimGrundy, maximumNimMex_eq_iff]
  norm_num

/-- For the `k=2` rule, `G(1)=0`; this private computation supports the requested
examples and introduces no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (characteristic values). -/
private theorem maximumNimGrundy_div_two_one : maximumNimGrundy (· / 2) 1 = 0 := by
  rw [maximumNimGrundy, maximumNimMex_eq_iff]
  norm_num

/-- For the `k=2` rule, `G(2)=1`; this private computation supports the requested
examples and introduces no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (characteristic values). -/
private theorem maximumNimGrundy_div_two_two : maximumNimGrundy (· / 2) 2 = 1 := by
  rw [maximumNimGrundy, maximumNimMex_eq_iff]
  norm_num [maximumNimGrundy_div_two_one]

/-- For the `k=2` rule, `G(3)=0`; this private computation supports the requested
examples and introduces no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (characteristic values). -/
private theorem maximumNimGrundy_div_two_three_aux :
    maximumNimGrundy (· / 2) 3 = 0 := by
  rw [maximumNimGrundy, maximumNimMex_eq_iff]
  norm_num [maximumNimGrundy_div_two_two]

/-- For the `k=2` rule, `G(4)=2`; this private computation supports the requested
examples and introduces no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (characteristic values). -/
private theorem maximumNimGrundy_div_two_four_aux :
    maximumNimGrundy (· / 2) 4 = 2 := by
  rw [maximumNimGrundy, maximumNimMex_eq_iff]
  norm_num
  constructor
  · intro x hx₁ hx₂
    interval_cases x <;>
      norm_num [maximumNimGrundy_div_two_three_aux, maximumNimGrundy_div_two_two]
  · intro n hn
    interval_cases n
    · exact ⟨1, by norm_num, maximumNimGrundy_div_two_three_aux⟩
    · exact ⟨2, by norm_num, maximumNimGrundy_div_two_two⟩

/-- For the `k=2` rule, `G(5)=1`; this private computation supports the requested
examples and introduces no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (characteristic values). -/
private theorem maximumNimGrundy_div_two_five_aux :
    maximumNimGrundy (· / 2) 5 = 1 := by
  rw [maximumNimGrundy, maximumNimMex_eq_iff]
  norm_num
  constructor
  · intro x hx₁ hx₂
    interval_cases x <;>
      norm_num [maximumNimGrundy_div_two_four_aux, maximumNimGrundy_div_two_three_aux]
  · exact ⟨2, by norm_num, maximumNimGrundy_div_two_three_aux⟩

/-- **Grundy number of a pile of five in halving Maximum Nim.** In Maximum Nim with rule
function $f(x) = \lfloor x/2 \rfloor$, a pile of $5$ stones has Grundy number $1$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (characteristic values). -/
public theorem maximumNimGrundy_div_two_five : maximumNimGrundy (· / 2) 5 = 1 := by
  exact maximumNimGrundy_div_two_five_aux

/-- **Grundy number of a pile of four in halving Maximum Nim.** In Maximum Nim with rule
function $f(x) = \lfloor x/2 \rfloor$, a pile of $4$ stones has Grundy number $2$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (characteristic values). -/
public theorem maximumNimGrundy_div_two_four : maximumNimGrundy (· / 2) 4 = 2 := by
  exact maximumNimGrundy_div_two_four_aux

/-- **Grundy number of a pile of three in halving Maximum Nim.** In Maximum Nim with rule
function $f(x) = \lfloor x/2 \rfloor$, a pile of $3$ stones has Grundy number $0$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (characteristic values). -/
public theorem maximumNimGrundy_div_two_three : maximumNimGrundy (· / 2) 3 = 0 := by
  exact maximumNimGrundy_div_two_three_aux

/-- **The Maximum Nim game.** For a rule function $f : \mathbb{N} \to \mathbb{N}$, the Maximum Nim
game with rule $f$ is the impartial game whose positions are the pile sizes $x \in \mathbb{N}$, in
which the moves from $x$ go to $x - u$ for each $u$ with $1 \le u \le \min(f(x), x)$. The rank of
a position is the pile size itself, and the starting position is the empty pile $0$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 2. -/
public def maximumNimGame (f : ℕ → ℕ) : SpragueGrundy.ImpartialGame where
  Pos := ℕ
  eqDec := inferInstance
  moves := fun x => (Finset.Icc 1 (min (f x) x)).image (fun u => x - u)
  rank := id
  rank_lt := by
    intro x y h
    simp only [Finset.mem_image, Finset.mem_Icc] at h
    obtain ⟨u, ⟨h1, h2⟩, rfl⟩ := h
    simp only [id_eq]
    omega
  start := 0

/-- **P-positions of Maximum Nim.** Let $f : \mathbb{N} \to \mathbb{N}$ be a rule function and let
$x$ be a pile size. The position $x$ of the Maximum Nim game with rule $f$ is a P-position
if and only if, for every $u$ with $1 \le u \le \min(f(x), x)$, the position $x - u$ is not
a P-position.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 2. -/
public theorem maximumNimGame_isP_iff (f : ℕ → ℕ) (x : ℕ) :
    SpragueGrundy.IsP (maximumNimGame f) x ↔
      ∀ u, 1 ≤ u → u ≤ min (f x) x → ¬SpragueGrundy.IsP (maximumNimGame f) (x - u) := by
  refine (SpragueGrundy.isP_iff (maximumNimGame f) x).trans ?_
  change (∀ q : ℕ, q ∈ (Finset.Icc 1 (min (f x) x)).image (fun u => x - u) →
      ¬SpragueGrundy.IsP (maximumNimGame f) q) ↔ _
  constructor
  · intro h u h1 h2
    exact h (x - u) (Finset.mem_image.mpr ⟨u, Finset.mem_Icc.mpr ⟨h1, h2⟩, rfl⟩)
  · intro h q hq
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hq
    exact h u (Finset.mem_Icc.mp hu).1 (Finset.mem_Icc.mp hu).2

/-- **The Maximum Nim map $h_k$.** For natural numbers $k$ and $x$, let
$h_k(x) = x + \lfloor x/(k-1) \rfloor + 1$. The paper takes $k \ge 2$; for $k \le 1$ the definition
gives $h_k(x) = x + 1$, because $k - 1$ is truncated to $0$ and $\lfloor x/0 \rfloor$ is taken to
be $0$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Definition 3.1. -/
public def maximumNimH (k x : ℕ) : ℕ := x + x / (k - 1) + 1

/-- **The value $h_3(0) = 1$ of the Maximum Nim map.** For the map
$h_k(x) = x + \lfloor x/(k-1) \rfloor + 1$ on the natural numbers, we have $h_3(0) = 1$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Definition 3.1. -/
public theorem maximumNimH_three_zero : maximumNimH 3 0 = 1 := by
  decide

/-- **The value $h_3(2) = 4$ of the Maximum Nim map.** For the map
$h_k(x) = x + \lfloor x/(k-1) \rfloor + 1$ on the natural numbers, we have $h_3(2) = 4$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Definition 3.1. -/
public theorem maximumNimH_three_two : maximumNimH 3 2 = 4 := by
  decide

/-- **Fuel-bounded Josephus simulation.** For natural numbers $k$ and $s$ (the starting
position), a fuel $f$ and a list $c$ of natural numbers (the current circle), the simulation
returns the empty list when $f = 0$ or $c$ is empty. Otherwise, with $L$ the length of $c$ and
$i = (s + k - 1) \bmod L$, where the subtraction is truncated at $0$, it returns the entry of
$c$ at zero-based position $i$ followed by the result of the simulation with the same $k$,
starting position $i$ and fuel $f - 1$ on the list obtained from $c$ by deleting the entry at
position $i$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (Josephus problem). -/
public def josephusEliminationOrderAux (k start : ℕ) : ℕ → List ℕ → List ℕ
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, circle =>
      let i := (start + k - 1) % circle.length
      circle.getD i 0 :: josephusEliminationOrderAux k i fuel (circle.eraseIdx i)

/-- **Josephus elimination order.** For natural numbers $k$ and $n$, place $1, \dots, n$ in
order on a circle and repeatedly remove one entry. When $L$ entries remain and the current
position is $s$ (zero-based, initially $s = 0$), the entry at zero-based position
$i = (s + k - 1) \bmod L$ is removed, where the subtraction is truncated at $0$, and $i$ becomes
the current position, so the next count starts at the entry after the removed one. The
Josephus elimination order with step $k$ on the circle $1, \dots, n$ is the list of all $n$
entries in the order of their removal.

For $k \ge 1$ this is the classical process that removes every $k$-th remaining entry; the last
entry of the list is the survivor.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (Josephus problem). -/
public def josephusEliminationOrder (k n : ℕ) : List ℕ :=
  josephusEliminationOrderAux k 0 n (List.range' 1 n)

/-- **Josephus elimination order for ten people and step three.** The Josephus elimination order
with step $3$ on the circle $1, \dots, 10$ is $3, 6, 9, 2, 7, 1, 8, 5, 10, 4$: the entries are
removed in the order $3, 6, 9, 2, 7, 1, 8, 5, 10$, and the survivor $4$ comes last.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (Josephus problem example). -/
public theorem josephusEliminationOrder_three_ten :
    josephusEliminationOrder 3 10 = [3, 6, 9, 2, 7, 1, 8, 5, 10, 4] := by
  decide

/-- **Josephus elimination order for three people and step two.** The Josephus elimination
order with step $2$ on the circle $1, 2, 3$ is $2, 1, 3$: the entry $2$ is removed first, then
the entry $1$, and the survivor $3$ comes last.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (characteristic values). -/
public theorem josephusEliminationOrder_two_three :
    josephusEliminationOrder 2 3 = [2, 1, 3] := by
  decide

/-- One step of the simulation on a nonempty circle: it records the entry at zero-based
index `(start + k - 1) % circle.length`, erases it, and restarts from that index. This
private unfolding lemma introduces no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (Josephus problem). -/
private theorem josephusEliminationOrderAux_succ (k s fuel : ℕ) (c : List ℕ) (hc : c ≠ []) :
    josephusEliminationOrderAux k s (fuel + 1) c = c.getD ((s + k - 1) % c.length) 0 ::
      josephusEliminationOrderAux k ((s + k - 1) % c.length) fuel
        (c.eraseIdx ((s + k - 1) % c.length)) := by
  cases c with
  | nil => exact absurd rfl hc
  | cons x xs => rfl

/-- With at least one unit of fuel per entry, the simulation from any start lists each
entry of the circle exactly once: its length is the circle's length and it is a
permutation of the circle. This private generalization introduces no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (Josephus problem). -/
private theorem josephusEliminationOrderAux_length_perm (k : ℕ) :
    ∀ fuel s (c : List ℕ), c.length ≤ fuel →
      (josephusEliminationOrderAux k s fuel c).length = c.length ∧
        List.Perm (josephusEliminationOrderAux k s fuel c) c := by
  intro fuel
  induction fuel with
  | zero =>
    intro s c hc
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hc)]
    exact ⟨rfl, List.Perm.refl _⟩
  | succ fuel ih =>
    intro s c hc
    by_cases hne : c = []
    · subst hne
      exact ⟨rfl, List.Perm.refl _⟩
    · rw [josephusEliminationOrderAux_succ k s fuel _ hne]
      have hi : (s + k - 1) % c.length < c.length :=
        Nat.mod_lt _ (List.length_pos_of_ne_nil hne)
      have hlen : (c.eraseIdx ((s + k - 1) % c.length)).length = c.length - 1 := by
        rw [List.length_eraseIdx]
        split <;> omega
      obtain ⟨h1, h2⟩ := ih ((s + k - 1) % c.length) (c.eraseIdx ((s + k - 1) % c.length))
        (by omega)
      refine ⟨by rw [List.length_cons, h1, hlen]; omega, ?_⟩
      rw [← List.getElem_eq_getD (h := hi) 0]
      exact (h2.cons _).trans (List.getElem_cons_eraseIdx_perm hi)

/-- For every `k`, the one-based survivor of a positive circle `1, ..., M+1` lies in
`[1, M+1]`; unlike `josephus_range` this needs no `2 ≤ k`. Private, with no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (Josephus problem). -/
private theorem josephus_succ_pos_le (k M : ℕ) :
    1 ≤ josephus k (M + 1) ∧ josephus k (M + 1) ≤ M + 1 := by
  have h : (josephus k M + k - 1) % (M + 1) < M + 1 := Nat.mod_lt _ (by omega)
  simp only [josephus]
  omega

/-- For `k ≥ 1`, the last entry recorded by the simulation on a circle `c` of length
`M+1`, started at index `s`, is the entry at zero-based index
`(s + josephus k (M+1) - 1) % (M+1)`. The inductive step uses that erasing index `i`
shifts every later index down by one. Private generalization, no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (Josephus problem). -/
private theorem josephusEliminationOrderAux_getLast? (k : ℕ) (hk : 1 ≤ k) :
    ∀ M s (c : List ℕ), c.length = M + 1 →
      (josephusEliminationOrderAux k s (M + 1) c).getLast? =
        c[(s + josephus k (M + 1) - 1) % (M + 1)]? := by
  intro M
  induction M with
  | zero =>
    intro s c hc
    match c, hc with
    | [x], _ => simp [josephusEliminationOrderAux, Nat.mod_one]
  | succ M ih =>
    intro s c hc
    have hne : c ≠ [] := by
      rintro rfl
      simp at hc
    rw [josephusEliminationOrderAux_succ k s (M + 1) c hne, List.getLast?_cons, hc]
    have hi : (s + k - 1) % (M + 2) < M + 2 := Nat.mod_lt _ (by omega)
    have hlen : (c.eraseIdx ((s + k - 1) % (M + 2))).length = M + 1 := by
      rw [List.length_eraseIdx]
      split <;> omega
    rw [ih _ _ hlen, List.getElem?_eraseIdx]
    obtain ⟨ha1, ha2⟩ := josephus_succ_pos_le k M
    have hjos : josephus k (M + 1 + 1) = (josephus k (M + 1) + k - 1) % (M + 2) + 1 := rfl
    rw [hjos]
    generalize josephus k (M + 1) = a at ha1 ha2
    generalize hi_def : (s + k - 1) % (M + 2) = i at hi
    have ht : (s + ((a + k - 1) % (M + 2) + 1) - 1) % (M + 2) = (i + a) % (M + 2) := by
      rw [show s + ((a + k - 1) % (M + 2) + 1) - 1 = s + (a + k - 1) % (M + 2) by omega,
        Nat.add_mod_mod, show s + (a + k - 1) = (s + k - 1) + a by omega, Nat.add_mod,
        hi_def, Nat.add_mod_mod]
    rw [ht]
    have hidx : (if (i + a - 1) % (M + 1) < i then (i + a - 1) % (M + 1)
        else (i + a - 1) % (M + 1) + 1) = (i + a) % (M + 2) := by
      by_cases hsmall : i + a ≤ M + 1
      · rw [Nat.mod_eq_of_lt (show i + a - 1 < M + 1 by omega),
          Nat.mod_eq_of_lt (show i + a < M + 2 by omega)]
        split <;> omega
      · rw [Nat.mod_eq_sub_mod (show M + 1 ≤ i + a - 1 by omega),
          Nat.mod_eq_of_lt (show i + a - 1 - (M + 1) < M + 1 by omega),
          Nat.mod_eq_sub_mod (show M + 2 ≤ i + a by omega),
          Nat.mod_eq_of_lt (show i + a - (M + 2) < M + 2 by omega)]
        split <;> omega
    have hsel : (if (i + a - 1) % (M + 1) < i then c[(i + a - 1) % (M + 1)]?
        else c[(i + a - 1) % (M + 1) + 1]?) = c[(i + a) % (M + 2)]? := by
      rw [← hidx]
      split_ifs <;> rfl
    rw [hsel, List.getElem?_eq_getElem (by rw [hc]; exact Nat.mod_lt _ (by omega))]
    rfl

/-- **Length of the Josephus elimination order.** For all natural numbers $k$ and $n$, the
Josephus elimination order with step $k$ on the circle $1, \dots, n$ has exactly $n$ entries.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (Josephus problem). -/
public theorem josephusEliminationOrder_length (k n : ℕ) :
    (josephusEliminationOrder k n).length = n := by
  simpa [josephusEliminationOrder] using
    (josephusEliminationOrderAux_length_perm k n 0 (List.range' 1 n) (by simp)).1

/-- **The Josephus elimination order is a permutation of the circle.** For all natural numbers
$k$ and $n$, the Josephus elimination order with step $k$ on the circle $1, \dots, n$ is a
permutation of the list $1, 2, \dots, n$; in particular, each of $1, \dots, n$ occurs in it
exactly once.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (Josephus problem). -/
public theorem josephusEliminationOrder_perm (k n : ℕ) :
    List.Perm (josephusEliminationOrder k n) (List.range' 1 n) :=
  (josephusEliminationOrderAux_length_perm k n 0 (List.range' 1 n) (by simp)).2

/-- **The survivor is the last entry of the Josephus elimination order.** For natural numbers
$k \ge 1$ and $n \ge 1$, the Josephus elimination order with step $k$ on the circle
$1, \dots, n$ is nonempty and its last entry is $J_k(n)$, the value at $n$ of the Josephus
function for elimination step $k$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (Josephus problem). -/
public theorem josephusEliminationOrder_getLast? (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    (josephusEliminationOrder k n).getLast? = some (josephus k n) := by
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 1 := ⟨n - 1, by omega⟩
  obtain ⟨ha1, ha2⟩ := josephus_succ_pos_le k M
  unfold josephusEliminationOrder
  rw [josephusEliminationOrderAux_getLast? k hk M 0 _ List.length_range', Nat.zero_add,
    Nat.mod_eq_of_lt (by omega), List.getElem?_range' (by omega)]
  congr 1
  omega

/-- **Grundy value zero characterizes P-positions in Maximum Nim.** Let $f : \mathbb{N} \to
\mathbb{N}$ satisfy $f(0) = 0$ and $f(m-1) \le f(m) \le f(m-1) + 1$ for every $m \ge 1$. Then for
every pile size $x \in \mathbb{N}$, the Grundy number of $x$ in Maximum Nim with rule function $f$
is $0$ if and only if $x$ is a P-position (a previous-player win under normal play) of that game.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Theorem 1 (`integers-2024-G5-thm-1`). -/
public theorem_wanted maximumNimGrundy_eq_zero_iff_isP (f : ℕ → ℕ) (hf0 : f 0 = 0)
    (hf : ∀ m, 1 ≤ m → f (m - 1) ≤ f m ∧ f m ≤ f (m - 1) + 1) (x : ℕ) :
    maximumNimGrundy f x = 0 ↔ SpragueGrundy.IsP (maximumNimGame f) x

/-- **Grundy number where the rule function increases.** Let $f : \mathbb{N} \to \mathbb{N}$
satisfy $f(0) = 0$ and $f(m-1) \le f(m) \le f(m-1) + 1$ for every $m \ge 1$, and let $G$ be the
Grundy number of Maximum Nim with rule function $f$. If $x \ge 1$ and $f(x-1) < f(x)$, then
$G(x) = f(x)$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 1(i) (`integers-2024-G5-lem-1`). -/
public theorem_wanted maximumNimGrundy_eq_rule_of_lt (f : ℕ → ℕ) (hf0 : f 0 = 0)
    (hf : ∀ m, 1 ≤ m → f (m - 1) ≤ f m ∧ f m ≤ f (m - 1) + 1)
    (x : ℕ) (hx : 1 ≤ x) (hfx : f (x - 1) < f x) :
    maximumNimGrundy f x = f x

/-- **Grundy number where the rule function is flat.** Let $f : \mathbb{N} \to \mathbb{N}$
satisfy $f(0) = 0$ and $f(m-1) \le f(m) \le f(m-1) + 1$ for every $m \ge 1$, and let $G$ be the
Grundy number of Maximum Nim with rule function $f$. If $x \ge 1$ and $f(x) = f(x-1)$, then
$G(x) = G(x - f(x) - 1)$.

Here $x - f(x) - 1 \ge 0$, since the hypotheses give $f(x) = f(x-1) \le x - 1$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 1(ii) (`integers-2024-G5-lem-1`). -/
public theorem_wanted maximumNimGrundy_eq_sub_rule_succ (f : ℕ → ℕ) (hf0 : f 0 = 0)
    (hf : ∀ m, 1 ≤ m → f (m - 1) ≤ f m ∧ f m ≤ f (m - 1) + 1)
    (x : ℕ) (hx : 1 ≤ x) (hfx : f x = f (x - 1)) :
    maximumNimGrundy f x = maximumNimGrundy f (x - f x - 1)

/-- **Floor identity for non-multiples in Maximum Nim.** Let $k \ge 2$ and $x$ be natural numbers
such that $x$ is not a multiple of $k$. Then
$x - \lfloor x/k \rfloor - 1 = \lfloor (k-1)x/k \rfloor$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 2 (`integers-2024-G5-lem-2`). -/
public theorem_wanted maximumNim_sub_div_sub_one_eq (k x : ℕ) (hk : 2 ≤ k)
    (hxk : ¬k ∣ x) :
    x - x / k - 1 = (k - 1) * x / k

/-- **Maximum Nim Grundy numbers at multiples of the divisor.** Let $k \ge 2$ and let $G$ be
the Grundy number of Maximum Nim with rule function $f(y) = \lfloor y/k \rfloor$. Every positive
multiple $x$ of $k$ satisfies $G(x) = x/k$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 3(i) (`integers-2024-G5-lem-3`). -/
public theorem_wanted maximumNimGrundy_div_eq_of_dvd (k x : ℕ) (hk : 2 ≤ k)
    (hx : 1 ≤ x) (hkx : k ∣ x) :
    maximumNimGrundy (· / k) x = x / k

/-- **Maximum Nim Grundy numbers at non-multiples of the divisor.** Let $k \ge 2$ and let $G$
be the Grundy number of Maximum Nim with rule function $f(y) = \lfloor y/k \rfloor$. If $x$ is a
natural number not divisible by $k$, then $G(x) = G(\lfloor (k-1)x/k \rfloor)$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 3(ii) (`integers-2024-G5-lem-3`). -/
public theorem_wanted maximumNimGrundy_eq_F_of_not_dvd (k x : ℕ) (hk : 2 ≤ k)
     (hkx : ¬k ∣ x) :
    maximumNimGrundy (· / k) x = maximumNimGrundy (· / k) ((k - 1) * x / k)

/-- **Floor-rule Maximum Nim: positions below k have Grundy number zero.** For every natural
number $k \ge 2$ and every natural number $j$ with $1 \le j \le k$, a pile of $k - j$ stones has
Grundy number $0$ in Maximum Nim with rule function $f(y) = \lfloor y/k \rfloor$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 3(iii) (`integers-2024-G5-lem-3`). -/
public theorem_wanted maximumNimGrundy_sub_eq_zero (k j : ℕ) (hk : 2 ≤ k)
    (hj : 1 ≤ j) (hjk : j ≤ k) :
    maximumNimGrundy (· / k) (k - j) = 0

/-- **A Maximum Nim non-divisibility lemma for $s < t$.** Let $k, n, t, h, s, i$ be natural
numbers with $h \ge 1$, $k = nt + h$, $h \le n$ and $s < t$. If $1 \le i \le n$, then $k$ does
not divide $n(k - s) - i$.

The hypotheses force $n \ge 1$, $s < k$ and $i \le n(k - s)$, so both subtractions are ordinary
differences of natural numbers.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 4(i) (`integers-2024-G5-lem-4`). -/
public theorem_wanted maximumNim_not_dvd_mul_sub_of_lt (k n t h s i : ℕ)
    (hh : 1 ≤ h)
    (hdecomp : k = n * t + h) (hhn : h ≤ n) (hst : s < t)
    (hi : 1 ≤ i) (hin : i ≤ n) :
    ¬k ∣ n * (k - s) - i

/-- **A Maximum Nim non-divisibility lemma for $i \ne h$.** Let $k, n, t, h, i$ be natural numbers
with $t \ge 1$, $h \ge 1$, $k = nt + h$ and $h \le n$. If $1 \le i \le n$ and $i \ne h$, then $k$
does not divide $n(k - t) - i$.

The hypotheses force $n \ge 1$, $t \le k$ and $i \le n(k - t)$, so both subtractions are ordinary
differences of natural numbers.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 4(ii) (`integers-2024-G5-lem-4`). -/
public theorem_wanted maximumNim_not_dvd_mul_sub_of_ne (k n t h i : ℕ)
    (ht : 1 ≤ t) (hh : 1 ≤ h)
    (hdecomp : k = n * t + h) (hhn : h ≤ n)
    (hi : 1 ≤ i) (hin : i ≤ n) (hih : i ≠ h) :
    ¬k ∣ n * (k - t) - i

/-- **Floor-rule Maximum Nim: Grundy reduction when $n = kt + u$.** Let $k$, $t$, $u$ and $n$ be
natural numbers with $k \ge 2$, $t \ge 1$, $u \le k - 1$ and $n = kt + u$. Write $G(x)$ for the
Grundy number of a pile of $x$ stones in Maximum Nim with rule function
$f(y) = \lfloor y/k \rfloor$. Then for every natural number $i$ with $1 \le i \le n$ that is not
divisible by $k$,
$$G(nk - i) = G\bigl((n - t)k - (u + i - \lfloor i/k \rfloor)\bigr).$$

The hypotheses force $i \le nk$ and $u + i - \lfloor i/k \rfloor \le (n - t)k$, so all
subtractions are ordinary differences of natural numbers. The right side is read with the
parentheses shown; read without them, as in the extracted statement, the equality is false.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 5(i) (`integers-2024-G5-lem-5`). -/
public theorem_wanted maximumNimGrundy_mul_sub_eq_decomposition (k n t u i : ℕ)
    (hk : 2 ≤ k) (ht : 1 ≤ t)
    (hdecomp : n = k * t + u) (huk : u ≤ k - 1)
    (hi : 1 ≤ i) (hin : i ≤ n) (hki : ¬k ∣ i) :
    maximumNimGrundy (· / k) (n * k - i) =
      maximumNimGrundy (· / k) ((n - t) * k - (u + i - i / k))

/-- **Floor-rule Maximum Nim: one-step Grundy reduction when k = nt + h.** Let $n$, $t$, $h$ be
natural numbers with $t \ge 1$ and $1 \le h \le n$, and let $k = nt + h$. Write $G(x)$ for the
Grundy number of a pile of $x$ stones in Maximum Nim with rule function
$f(y) = \lfloor y/k \rfloor$, and let $F(x) = \lfloor (k-1)x/k \rfloor$. Then for every natural
number $i$ with $1 \le i \le n$,
$$G(nk - i) = G(F(nk - i)) = G(n(k - 1) - i).$$

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 5(ii.1) (`integers-2024-G5-lem-5`). -/
public theorem_wanted maximumNimGrundy_mul_sub_eq_F_eq_pred (k n t h i : ℕ)
    (ht : 1 ≤ t) (hh : 1 ≤ h)
    (hdecomp : k = n * t + h) (hhn : h ≤ n) (hi : 1 ≤ i) (hin : i ≤ n) :
    maximumNimGrundy (· / k) (n * k - i) =
        maximumNimGrundy (· / k) ((k - 1) * (n * k - i) / k) ∧
      maximumNimGrundy (· / k) ((k - 1) * (n * k - i) / k) =
        maximumNimGrundy (· / k) (n * (k - 1) - i)

/-- **Floor-rule Maximum Nim: t-step Grundy reduction when k = nt + h.** Let $n$, $t$, $h$ be
natural numbers with $t \ge 1$ and $1 \le h \le n$, and let $k = nt + h$. Write $G(x)$ for the
Grundy number of a pile of $x$ stones in Maximum Nim with rule function
$f(y) = \lfloor y/k \rfloor$, let $F(x) = \lfloor (k-1)x/k \rfloor$, and let $F^t$ be the $t$-fold
iterate of $F$. Then for every natural number $i$ with $1 \le i \le n$,
$$G(nk - i) = G(F^t(nk - i)) = G(n(k - t) - i).$$

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 5(ii.2) (`integers-2024-G5-lem-5`). -/
public theorem_wanted maximumNimGrundy_mul_sub_eq_iterate_F (k n t h i : ℕ)
    (ht : 1 ≤ t) (hh : 1 ≤ h)
    (hdecomp : k = n * t + h) (hhn : h ≤ n) (hi : 1 ≤ i) (hin : i ≤ n) :
    let F := fun x => (k - 1) * x / k
    maximumNimGrundy (· / k) (n * k - i) =
        maximumNimGrundy (· / k) (Nat.iterate F t (n * k - i)) ∧
      maximumNimGrundy (· / k) (Nat.iterate F t (n * k - i)) =
        maximumNimGrundy (· / k) (n * (k - t) - i)

/-- **Floor-rule Maximum Nim: (t+1)-step Grundy reduction when k = nt + h.** Let $n$, $t$, $h$ be
natural numbers with $t \ge 1$ and $1 \le h \le n$, and let $k = nt + h$. Write $G(x)$ for the
Grundy number of a pile of $x$ stones in Maximum Nim with rule function
$f(y) = \lfloor y/k \rfloor$, let $F(x) = \lfloor (k-1)x/k \rfloor$, and let $F^{t+1}$ be the
$(t+1)$-fold iterate of $F$. Then for every natural number $i$ with $1 \le i \le h - 1$,
$$G(nk - i) = G(F^{t+1}(nk - i)) = G((n - 1)k - (n - h + i)).$$

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 5(ii.3) (`integers-2024-G5-lem-5`). -/
public theorem_wanted maximumNimGrundy_mul_sub_eq_succ_iterate_F (k n t h i : ℕ)
    (ht : 1 ≤ t) (hh : 1 ≤ h)
    (hdecomp : k = n * t + h) (hhn : h ≤ n) (hi : 1 ≤ i) (hih : i ≤ h - 1) :
    let F := fun x => (k - 1) * x / k
    maximumNimGrundy (· / k) (n * k - i) =
        maximumNimGrundy (· / k) (Nat.iterate F (t + 1) (n * k - i)) ∧
      maximumNimGrundy (· / k) (Nat.iterate F (t + 1) (n * k - i)) =
        maximumNimGrundy (· / k) ((n - 1) * k - (n - h + i))

/-- **The Maximum Nim map $h_k$ is strictly increasing.** Let $k \ge 2$ be a natural number and
let $h_k$ be the map $x \mapsto x + \lfloor x/(k-1) \rfloor + 1$ on the natural numbers. For all
natural numbers $x$ and $x'$ with $x < x'$, we have $h_k(x) < h_k(x')$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 6(i) (`integers-2024-G5-lem-6`). -/
public theorem_wanted maximumNimH_strictMono (k x x' : ℕ) (hk : 2 ≤ k) (hxx' : x < x') :
    maximumNimH k x < maximumNimH k x'

/-- **The Maximum Nim map $h_k$ exceeds its argument.** Let $k \ge 2$ be a natural number and let
$h_k$ be the map $x \mapsto x + \lfloor x/(k-1) \rfloor + 1$ on the natural numbers. Every natural
number $x$ satisfies $x < x + 1 \le h_k(x)$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 6(ii) (`integers-2024-G5-lem-6`). -/
public theorem_wanted maximumNimH_succ_le (k x : ℕ) (hk : 2 ≤ k) :
    x < x + 1 ∧ x + 1 ≤ maximumNimH k x

/-- **Iterates of the Maximum Nim map $h_k$ tend to infinity.** Let $k \ge 2$ be a natural
number and let $h_k$ be the map $x \mapsto x + \lfloor x/(k-1) \rfloor + 1$ on the natural numbers.
For every natural number $x_0$, the iterates $h_k^p(x_0)$ tend to infinity as $p \to \infty$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 6(iii) (`integers-2024-G5-lem-6`). -/
public theorem_wanted maximumNimH_iterate_tendsto_atTop (k x₀ : ℕ) (hk : 2 ≤ k) :
    Filter.Tendsto (fun p => Nat.iterate (maximumNimH k) p x₀)
      Filter.atTop Filter.atTop

/-- **Linear bounds on h_k and their iterates.** Let $k \ge 2$ be a natural number, let
$h_k(x) = x + \lfloor x/(k-1) \rfloor + 1$ on natural numbers, and define the real maps
$h_k^-(x) = x + \frac{x}{k-1}$ and $h_k^+(x) = x + \frac{x}{k-1} + 1$. Writing $g^p$ for the
$p$-fold iterate of a map $g$, for all natural numbers $p$ and $x$: (i)
$(h_k^-)^p(x) = \left(\frac{k}{k-1}\right)^p x$, (ii)
$(h_k^+)^p(x) = \left(\frac{k}{k-1}\right)^p (x + k - 1) - (k - 1)$, and (iii)
$h_k^-(x) \le h_k(x) \le h_k^+(x)$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 7 (`integers-2024-G5-lem-7`). -/
public theorem_wanted maximumNimH_iterate_bounds (k : ℕ) (hk : 2 ≤ k) :
    let hMinus : ℝ → ℝ := fun x => x + x / ((k : ℝ) - 1)
    let hPlus : ℝ → ℝ := fun x => x + x / ((k : ℝ) - 1) + 1
    (∀ (p x : ℕ), Nat.iterate hMinus p x = ((k : ℝ) / (k - 1)) ^ p * x) ∧
    (∀ (p x : ℕ), Nat.iterate hPlus p x = ((k : ℝ) / (k - 1)) ^ p * (x + k - 1) - (k - 1)) ∧
    (∀ x : ℕ, hMinus x ≤ maximumNimH k x ∧ (maximumNimH k x : ℝ) ≤ hPlus x)

/-- **Josephus elimination positions as Maximum Nim Grundy numbers.** Let $k \ge 2$ and
$1 \le m \le n$. Write $o_n(m)$ for the position, counting from $1$, at which $m$ appears in the
Josephus elimination order of the circle $1, \dots, n$ in which every $k$-th person is removed
and the survivor is listed last, and write $G$ for the Grundy number of Maximum Nim with rule
function $f(y) = \lfloor y/k \rfloor$. Then $n - o_n(m) = G(nk - m)$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Theorem 2 (`integers-2024-G5-thm-2`). -/
public theorem_wanted josephus_position_complement_eq_maximumNimGrundy (k n m : ℕ)
    (hk : 2 ≤ k) (hm : 1 ≤ m) (hmn : m ≤ n) :
    n - ((josephusEliminationOrder k n).idxOf m + 1) =
      maximumNimGrundy (· / k) (n * k - m)

/-- **Josephus survivor via iteration from zero.** Let $k \ge 2$ and $n \ge 1$ be natural
numbers, let $h_k(x) = x + \lfloor x/(k-1) \rfloor + 1$ for natural numbers $x$, and write
$h_k^p$ for the $p$-th iterate of $h_k$. Then there is a natural number $p \ge 1$ with
$h_k^{p-1}(0) < n(k-1) \le h_k^p(0)$ and $J_k(n) = nk - h_k^p(0)$, where $J_k$ is the Josephus
function for elimination step $k$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Theorem 3 (`integers-2024-G5-thm-3`). -/
public theorem_wanted josephus_eq_mul_sub_iterate_maximumNimH_zero (k n : ℕ)
    (hk : 2 ≤ k) (hn : 1 ≤ n) :
    ∃ p, 1 ≤ p ∧
      Nat.iterate (maximumNimH k) (p - 1) 0 < n * (k - 1) ∧
      n * (k - 1) ≤ Nat.iterate (maximumNimH k) p 0 ∧
      josephus k n = n * k - Nat.iterate (maximumNimH k) p 0

/-- **Josephus survivor via the shifted iteration.** Let $k \ge 2$ and $n \ge 2$ be natural
numbers, let $h_k(x) = x + \lfloor x/(k-1) \rfloor + 1$ for natural numbers $x$, and write
$h_k^p$ for the $p$-th iterate of $h_k$. Then there is a natural number $p \ge 1$ with
$h_k^{p-1}(k-1) < n(k-1) \le h_k^p(k-1)$ and $J_k(n) = nk - h_k^p(k-1)$, where $J_k$ is the
Josephus function for elimination step $k$.

The hypothesis $n \ge 2$ is needed: for $n = 1$ every $p \ge 1$ has
$h_k^{p-1}(k-1) \ge k - 1 = n(k-1)$, so no such $p$ exists.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Corollary 1 (`integers-2024-G5-cor-1`). -/
public theorem_wanted josephus_eq_mul_sub_iterate_maximumNimH_pred (k n : ℕ)
    (hk : 2 ≤ k) (hn : 2 ≤ n) :
    ∃ p, 1 ≤ p ∧
      Nat.iterate (maximumNimH k) (p - 1) (k - 1) < n * (k - 1) ∧
      n * (k - 1) ≤ Nat.iterate (maximumNimH k) p (k - 1) ∧
      josephus k n = n * k - Nat.iterate (maximumNimH k) p (k - 1)

/-- **Logarithmic bounds on the iterates of h_k.** Let $k \ge 2$ and $n \ge 1$ be natural numbers,
let $h_k(x) = x + \lfloor x/(k-1) \rfloor + 1$ on natural numbers, write $h_k^p$ for its $p$-fold
iterate, and let
$$v = \frac{\log n}{\log k - \log(k-1)}, \qquad w = \frac{\log(n+1) - \log 2}{\log k - \log(k-1)},$$
where $\log$ is the natural logarithm. Then
$$h_k^{\lfloor w \rfloor}(k-1) \le n(k-1) \le h_k^{\lceil v \rceil}(k-1).$$

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 8 (`integers-2024-G5-lem-8`). -/
public theorem_wanted maximumNimH_iterate_floor_le_mul_le_iterate_ceil (k n : ℕ)
    (hk : 2 ≤ k) (hn : 1 ≤ n) :
    let v : ℝ := Real.log n / (Real.log k - Real.log (k - 1))
    let w : ℝ := (Real.log (n + 1) - Real.log 2) / (Real.log k - Real.log (k - 1))
    Nat.iterate (maximumNimH k) (Nat.floor w) (k - 1) ≤ n * (k - 1) ∧
      n * (k - 1) ≤ Nat.iterate (maximumNimH k) (Nat.ceil v) (k - 1)

/-- **Logarithmic bounds for the Josephus iteration count.** Let $k \ge 2$ and $n \ge 2$ be
natural numbers, let $h_k(x) = x + \lfloor x/(k-1) \rfloor + 1$ for natural numbers $x$, write
$h_k^p$ for the $p$-th iterate of $h_k$, and define the real numbers
$v = \log n / (\log k - \log(k-1))$ and $w = (\log(n+1) - \log 2) / (\log k - \log(k-1))$,
where $\log$ is the natural logarithm. Then there is a natural number $p \ge 1$ with
$\lfloor w \rfloor \le p \le \lceil v \rceil$ and $J_k(n) = nk - h_k^p(k-1)$, where $J_k$ is the
Josephus function for elimination step $k$.

The hypothesis $n \ge 2$ is needed: for $n = 1$ we have $v = 0$, so $\lceil v \rceil = 0$ and no
$p \ge 1$ satisfies $p \le \lceil v \rceil$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Theorem 4 (`integers-2024-G5-thm-4`). -/
public theorem_wanted josephus_eq_mul_sub_iterate_maximumNimH_between_log_bounds
    (k n : ℕ) (hk : 2 ≤ k) (hn : 2 ≤ n) :
    let v : ℝ := Real.log n / (Real.log k - Real.log (k - 1))
    let w : ℝ := (Real.log (n + 1) - Real.log 2) / (Real.log k - Real.log (k - 1))
    ∃ p, 1 ≤ p ∧ Nat.floor w ≤ p ∧ p ≤ Nat.ceil v ∧
      josephus k n = n * k - Nat.iterate (maximumNimH k) p (k - 1)

end

end MetaMathlibExt
