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

/-- The least natural number outside a finite set, used to express the paper's mex.
The witness passed to `Nat.find` is one larger than the maximum of the set with zero
adjoined; this is an implementation detail and not a mathematical deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 2. -/
public def maximumNimMex (s : Finset ℕ) : ℕ :=
  Nat.find (show ∃ m, m ∉ s by
    let M := (insert 0 s).max' (by simp)
    refine ⟨M + 1, ?_⟩
    intro h
    have hle : M + 1 ≤ M := Finset.le_max' (insert 0 s) (M + 1) (by simp [h])
    omega)

/-- The finite mex is `m` exactly when `m` is absent and every smaller natural is
present. This is the characteristic property of the paper's mex, with no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 2. -/
public theorem maximumNimMex_eq_iff (s : Finset ℕ) (m : ℕ) :
    maximumNimMex s = m ↔ m ∉ s ∧ ∀ n < m, n ∈ s := by
  unfold maximumNimMex
  rw [Nat.find_eq_iff]
  simp

/-- The Grundy number of a Maximum Nim pile with rule function `f`. For a pile `x`,
`Finset.Icc 1 (min (f x) x)` is the set of legal removal counts, and the recursive
values at `x - u` form the finite set whose mex is taken. The `min` makes the function
total; under the paper's hypotheses and `f 0 = 0` it does not alter legal play.
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

/-- Unfolding `maximumNimGrundy f x` gives the mex of the Grundy numbers at exactly
the positions `x - u` for `1 ≤ u ≤ min (f x) x`; `attach` only carries the proof that
each removal count is legal, so there is no mathematical deviation.
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

/-- For the Section 3 rule `f(x) = ⌊x/2⌋`, a pile of five has Grundy number one.
This is the paper's `k = 2`, `G(5) = 1` check, with natural division representing
the floor; there is no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (characteristic values). -/
public theorem maximumNimGrundy_div_two_five : maximumNimGrundy (· / 2) 5 = 1 := by
  exact maximumNimGrundy_div_two_five_aux

/-- For the Section 3 rule `f(x) = ⌊x/2⌋`, a pile of four has Grundy number two.
This is the paper's `k = 2`, `G(4) = 2` check, with natural division representing
the floor; there is no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (characteristic values). -/
public theorem maximumNimGrundy_div_two_four : maximumNimGrundy (· / 2) 4 = 2 := by
  exact maximumNimGrundy_div_two_four_aux

/-- For the Section 3 rule `f(x) = ⌊x/2⌋`, a pile of three has Grundy number zero.
This is the paper's `k = 2`, `G(3) = 0` check, with natural division representing
the floor; there is no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (characteristic values). -/
public theorem maximumNimGrundy_div_two_three : maximumNimGrundy (· / 2) 3 = 0 := by
  exact maximumNimGrundy_div_two_three_aux

/-- Maximum Nim with rule function `f` as an impartial game in the repository's
Sprague-Grundy API: positions are pile sizes, and from `x` one may move to `x - u` for
`1 ≤ u ≤ min (f x) x`; the rank is the pile size and the start is the empty pile. The `min`
is the same totality convention as for `maximumNimGrundy`, and is the only representational
deviation.
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

/-- A pile `x` is a P-position of `maximumNimGame f` exactly when no legal successor
`x - u`, for `1 ≤ u ≤ min (f x) x`, is a P-position. This is the normal-play recursion,
derived from `SpragueGrundy.isP_iff`; the totalizing `min` is the only representational
deviation.
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

/-- The map `h_k(x) = x + ⌊x/(k-1)⌋ + 1`; natural division implements the floor
on nonnegative integers exactly, so there is no deviation from the paper.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Definition 3.1. -/
public def maximumNimH (k x : ℕ) : ℕ := x + x / (k - 1) + 1

/-- At `k = 3`, Definition 3.1 gives `h_3(0) = 1`; the Lean equality is the direct
natural-number calculation and has no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Definition 3.1. -/
public theorem maximumNimH_three_zero : maximumNimH 3 0 = 1 := by
  decide

/-- At `k = 3`, Definition 3.1 gives `h_3(2) = 4`; the Lean equality is the direct
natural-number calculation and has no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Definition 3.1. -/
public theorem maximumNimH_three_two : maximumNimH 3 2 = 4 := by
  decide

/-- A fuel-bounded Josephus simulation on a current circle. The removed zero-based
index is `(start + k - 1) % circle.length`, and that index is the next starting index;
the public definition supplies exactly one unit of fuel per initial entry. The default
zero is unreachable there and only totalizes `getD`, so it is not a paper deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (Josephus problem). -/
public def josephusEliminationOrderAux (k start : ℕ) : ℕ → List ℕ → List ℕ
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, circle =>
      let i := (start + k - 1) % circle.length
      circle.getD i 0 :: josephusEliminationOrderAux k i fuel (circle.eraseIdx i)

/-- The complete Josephus elimination order on the one-based circle `1, ..., n`,
with every `k`-th entry removed and the survivor placed last. `List.range' 1 n`
formalizes that circle and fuel `n` records all `n` eliminations; there is no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (Josephus problem). -/
public def josephusEliminationOrder (k n : ℕ) : List ℕ :=
  josephusEliminationOrderAux k 0 n (List.range' 1 n)

/-- For `n = 10` and `k = 3`, the simulator removes
`3, 6, 9, 2, 7, 1, 8, 5, 10` and records survivor `4` last, exactly as in the paper;
there is no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (Josephus problem example). -/
public theorem josephusEliminationOrder_three_ten :
    josephusEliminationOrder 3 10 = [3, 6, 9, 2, 7, 1, 8, 5, 10, 4] := by
  decide

/-- For `n = 3` and `k = 2`, the order is `2, 1, 3`, with survivor `3` last;
this is the check used to relate elimination positions to Grundy values, with no deviation.
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

/-- The Josephus elimination order on `n` people has exactly `n` entries: every person
is eliminated once, with the survivor recorded last. This holds for every `k`, with no
deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (Josephus problem). -/
public theorem josephusEliminationOrder_length (k n : ℕ) :
    (josephusEliminationOrder k n).length = n := by
  simpa [josephusEliminationOrder] using
    (josephusEliminationOrderAux_length_perm k n 0 (List.range' 1 n) (by simp)).1

/-- The Josephus elimination order on `n` people is a permutation of the circle
`1, ..., n`, so each person appears exactly once. This holds for every `k`, with no
deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (Josephus problem). -/
public theorem josephusEliminationOrder_perm (k n : ℕ) :
    List.Perm (josephusEliminationOrder k n) (List.range' 1 n) :=
  (josephusEliminationOrderAux_length_perm k n 0 (List.range' 1 n) (by simp)).2

/-- For `k ≥ 1` and `n ≥ 1`, the last entry of the elimination order (the survivor) is
the one-based Josephus number `josephus k n`, connecting the simulation to the
recurrence `J(n+1) = ((J(n) + k - 1) mod (n+1)) + 1`. The paper's range `k ≥ 2` is
relaxed to `k ≥ 1`; there is no other deviation.
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

/-- Theorem 1: under `f 0 = 0` and the unit-step monotonicity condition expressed by
`f (m-1) ≤ f m ≤ f (m-1)+1` for positive `m`, a position has Grundy number zero
exactly when it is a P-position (previous-player win) of `maximumNimGame f`. There is no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Theorem 1 (`integers-2024-G5-thm-1`). -/
public theorem_wanted maximumNimGrundy_eq_zero_iff_isP (f : ℕ → ℕ) (hf0 : f 0 = 0)
    (hf : ∀ m, 1 ≤ m → f (m - 1) ≤ f m ∧ f m ≤ f (m - 1) + 1) (x : ℕ) :
    maximumNimGrundy f x = 0 ↔ SpragueGrundy.IsP (maximumNimGame f) x

/-- Lemma 1(i): for a positive `x`, if an admissible rule function increases from
`x-1` to `x`, then `G(x) = f(x)`. The hypotheses `hf0` and `hf` formalize the same
rule-function assumptions as Theorem 1; there is no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 1(i) (`integers-2024-G5-lem-1`). -/
public theorem_wanted maximumNimGrundy_eq_rule_of_lt (f : ℕ → ℕ) (hf0 : f 0 = 0)
    (hf : ∀ m, 1 ≤ m → f (m - 1) ≤ f m ∧ f m ≤ f (m - 1) + 1)
    (x : ℕ) (hx : 1 ≤ x) (hfx : f (x - 1) < f x) :
    maximumNimGrundy f x = f x

/-- Lemma 1(ii): for positive `x`, if an admissible rule function is unchanged from
`x-1` to `x`, then `G(x) = G(x-f(x)-1)`. Natural subtraction matches the paper under
the stated rule-function hypotheses, so there is no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 1(ii) (`integers-2024-G5-lem-1`). -/
public theorem_wanted maximumNimGrundy_eq_sub_rule_succ (f : ℕ → ℕ) (hf0 : f 0 = 0)
    (hf : ∀ m, 1 ≤ m → f (m - 1) ≤ f m ∧ f m ≤ f (m - 1) + 1)
    (x : ℕ) (hx : 1 ≤ x) (hfx : f x = f (x - 1)) :
    maximumNimGrundy f x = maximumNimGrundy f (x - f x - 1)

/-- Lemma 2: when `k ≥ 2`, positive `x` is not divisible by `k`, subtracting
`⌊x/k⌋` and one from `x` equals `⌊(k-1)x/k⌋`. Natural division is the indicated
floor and `¬ k ∣ x` is “not a multiple”; there is no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 2 (`integers-2024-G5-lem-2`). -/
public theorem_wanted maximumNim_sub_div_sub_one_eq (k x : ℕ) (hk : 2 ≤ k)
    (hxk : ¬k ∣ x) :
    x - x / k - 1 = (k - 1) * x / k

/-- Lemma 3(i): for `k ≥ 2`, every positive multiple `x` of `k` has Grundy number
`x/k` under the rule `f(y)=⌊y/k⌋`. Divisibility formalizes “multiple” and natural
division the floors; there is no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 3(i) (`integers-2024-G5-lem-3`). -/
public theorem_wanted maximumNimGrundy_div_eq_of_dvd (k x : ℕ) (hk : 2 ≤ k)
    (hx : 1 ≤ x) (hkx : k ∣ x) :
    maximumNimGrundy (· / k) x = x / k

/-- Lemma 3(ii): for `k ≥ 2`, every positive nonmultiple `x` has the same Grundy
number as `F(x)=⌊(k-1)x/k⌋`. The expression `(k-1)*x/k` is `F`; there is no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 3(ii) (`integers-2024-G5-lem-3`). -/
public theorem_wanted maximumNimGrundy_eq_F_of_not_dvd (k x : ℕ) (hk : 2 ≤ k)
     (hkx : ¬k ∣ x) :
    maximumNimGrundy (· / k) x = maximumNimGrundy (· / k) ((k - 1) * x / k)

/-- Lemma 3(iii): for `k ≥ 2` and each `j` from one through `k`, the position
`k-j` has Grundy number zero for rule `f(y)=⌊y/k⌋`. The bounded hypotheses encode
`j=1,...,k`; there is no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 3(iii) (`integers-2024-G5-lem-3`). -/
public theorem_wanted maximumNimGrundy_sub_eq_zero (k j : ℕ) (hk : 2 ≤ k)
    (hj : 1 ≤ j) (hjk : j ≤ k) :
    maximumNimGrundy (· / k) (k - j) = 0

/-- Lemma 4(i): if positive `n,t,h` satisfy `k = n*t+h`, `h ≤ n`, and `s<t`,
then for every `1 ≤ i ≤ n`, `n*(k-s)-i` is not divisible by `k`. Naturals already
encode `s ≥ 0`; there is no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 4(i) (`integers-2024-G5-lem-4`). -/
public theorem_wanted maximumNim_not_dvd_mul_sub_of_lt (k n t h s i : ℕ)
    (hh : 1 ≤ h)
    (hdecomp : k = n * t + h) (hhn : h ≤ n) (hst : s < t)
    (hi : 1 ≤ i) (hin : i ≤ n) :
    ¬k ∣ n * (k - s) - i

/-- Lemma 4(ii): if positive `n,t,h` satisfy `k = n*t+h` and `h ≤ n`, then for
`1 ≤ i ≤ n` with `i ≠ h`, `n*(k-t)-i` is not divisible by `k`. The hypotheses map
the paper's positive-integer clauses directly; there is no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 4(ii) (`integers-2024-G5-lem-4`). -/
public theorem_wanted maximumNim_not_dvd_mul_sub_of_ne (k n t h i : ℕ)
    (ht : 1 ≤ t) (hh : 1 ≤ h)
    (hdecomp : k = n * t + h) (hhn : h ≤ n)
    (hi : 1 ≤ i) (hin : i ≤ n) (hih : i ≠ h) :
    ¬k ∣ n * (k - t) - i

/-- Lemma 5(i): if positive `n,k,t` and nonnegative `u` satisfy `n=k*t+u` and
`u ≤ k-1`, then each positive `i ≤ n` not divisible by `k` gives the displayed
Grundy equality. We use the intended parenthesized right side
`(n-t)k-(u+i-⌊i/k⌋)`; the extraction's unparenthesized literal reading is false.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 5(i) (`integers-2024-G5-lem-5`). -/
public theorem_wanted maximumNimGrundy_mul_sub_eq_decomposition (k n t u i : ℕ)
    (hk : 2 ≤ k) (ht : 1 ≤ t)
    (hdecomp : n = k * t + u) (huk : u ≤ k - 1)
    (hi : 1 ≤ i) (hin : i ≤ n) (hki : ¬k ∣ i) :
    maximumNimGrundy (· / k) (n * k - i) =
      maximumNimGrundy (· / k) ((n - t) * k - (u + i - i / k))

/-- Lemma 5(ii.1): under `k=n*t+h` for positive `n,t,h` with `h ≤ n`, every
`1 ≤ i ≤ n` gives `G(nk-i)=G(F(nk-i))=G(n(k-1)-i)`, where `F(x)=(k-1)x/k`.
The conjunction spells out the paper's two equalities; there is no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 5(ii.1) (`integers-2024-G5-lem-5`). -/
public theorem_wanted maximumNimGrundy_mul_sub_eq_F_eq_pred (k n t h i : ℕ)
    (ht : 1 ≤ t) (hh : 1 ≤ h)
    (hdecomp : k = n * t + h) (hhn : h ≤ n) (hi : 1 ≤ i) (hin : i ≤ n) :
    maximumNimGrundy (· / k) (n * k - i) =
        maximumNimGrundy (· / k) ((k - 1) * (n * k - i) / k) ∧
      maximumNimGrundy (· / k) ((k - 1) * (n * k - i) / k) =
        maximumNimGrundy (· / k) (n * (k - 1) - i)

/-- Lemma 5(ii.2): with `k=n*t+h` for positive `n,t,h`, `h ≤ n`, and
`1 ≤ i ≤ n`, `G(nk-i)` equals `G(F^t(nk-i))`, which equals `G(n(k-t)-i)`.
`Nat.iterate` is the paper's superscript iteration; there is no deviation.
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

/-- Lemma 5(ii.3): with `k=n*t+h` for positive `n,t,h`, `h ≤ n`, and positive
`i ≤ h-1`, `G(nk-i)` equals `G(F^(t+1)(nk-i))`, which equals
`G((n-1)k-(n-h+i))`. The hypotheses encode `i ∈ N`; there is no deviation.
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

/-- Lemma 6(i): for `k ≥ 2`, `h_k` is strictly increasing: `x<x'` implies
`h_k(x)<h_k(x')`. The function is `maximumNimH`; there is no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 6(i) (`integers-2024-G5-lem-6`). -/
public theorem_wanted maximumNimH_strictMono (k x x' : ℕ) (hk : 2 ≤ k) (hxx' : x < x') :
    maximumNimH k x < maximumNimH k x'

/-- Lemma 6(ii): for `k ≥ 2`, every `x` satisfies `x < x+1 ≤ h_k(x)`.
The two inequalities are represented as a conjunction; there is no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 6(ii) (`integers-2024-G5-lem-6`). -/
public theorem_wanted maximumNimH_succ_le (k x : ℕ) (hk : 2 ≤ k) :
    x < x + 1 ∧ x + 1 ≤ maximumNimH k x

/-- Lemma 6(iii): for `k ≥ 2`, the iterates `h_k^p(x₀)` tend to infinity as
`p` tends to infinity. `Filter.Tendsto ... Filter.atTop Filter.atTop` is precisely
that divergence statement and `Nat.iterate` is superscript iteration; no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 6(iii) (`integers-2024-G5-lem-6`). -/
public theorem_wanted maximumNimH_iterate_tendsto_atTop (k x₀ : ℕ) (hk : 2 ≤ k) :
    Filter.Tendsto (fun p => Nat.iterate (maximumNimH k) p x₀)
      Filter.atTop Filter.atTop

/-- Lemma 7: for `k ≥ 2` and the maps `h_k⁻(x) = x + x/(k-1)` and `h_k⁺(x) = x + x/(k-1) + 1`
of Definition 3.2, (i) `(h_k⁻)^p(x) = (k/(k-1))^p x`, (ii)
`(h_k⁺)^p(x) = (k/(k-1))^p (x + k - 1) - (k - 1)`, and (iii) `h_k⁻(x) ≤ h_k(x) ≤ h_k⁺(x)` for
every nonnegative integer `x`.

`h_k⁻` and `h_k⁺` are real-valued (their iterates leave the integers), `h_k` is `maximumNimH`
cast to `ℝ`, and `Nat.iterate` is the functional power; there is no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 7 (`integers-2024-G5-lem-7`). -/
public theorem_wanted maximumNimH_iterate_bounds (k : ℕ) (hk : 2 ≤ k) :
    let hMinus : ℝ → ℝ := fun x => x + x / ((k : ℝ) - 1)
    let hPlus : ℝ → ℝ := fun x => x + x / ((k : ℝ) - 1) + 1
    (∀ (p x : ℕ), Nat.iterate hMinus p x = ((k : ℝ) / (k - 1)) ^ p * x) ∧
    (∀ (p x : ℕ), Nat.iterate hPlus p x = ((k : ℝ) / (k - 1)) ^ p * (x + k - 1) - (k - 1)) ∧
    (∀ x : ℕ, hMinus x ≤ maximumNimH k x ∧ (maximumNimH k x : ℝ) ≤ hPlus x)

/-- Theorem 2: for `k ≥ 2` and positive `m ≤ n`, `n-o_n(m)` equals `G(nk-m)`.
Here `o_n(m)` is formalized exactly as the zero-based `idxOf m` in the full
Josephus order plus one, including the survivor last; there is no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Theorem 2 (`integers-2024-G5-thm-2`). -/
public theorem_wanted josephus_position_complement_eq_maximumNimGrundy (k n m : ℕ)
    (hk : 2 ≤ k) (hm : 1 ≤ m) (hmn : m ≤ n) :
    n - ((josephusEliminationOrder k n).idxOf m + 1) =
      maximumNimGrundy (· / k) (n * k - m)

/-- Theorem 3: for `k ≥ 2` and positive `n`, some positive `p` brackets
`n(k-1)` strictly above `h_k^(p-1)(0)` and weakly below `h_k^p(0)`, and the
one-based survivor `josephus k n` is `nk-h_k^p(0)`. There is no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Theorem 3 (`integers-2024-G5-thm-3`). -/
public theorem_wanted josephus_eq_mul_sub_iterate_maximumNimH_zero (k n : ℕ)
    (hk : 2 ≤ k) (hn : 1 ≤ n) :
    ∃ p, 1 ≤ p ∧
      Nat.iterate (maximumNimH k) (p - 1) 0 < n * (k - 1) ∧
      n * (k - 1) ≤ Nat.iterate (maximumNimH k) p 0 ∧
      josephus k n = n * k - Nat.iterate (maximumNimH k) p 0

/-- Corollary 1: for `k ≥ 2` and `n ≥ 2`, a positive `p` brackets `n(k-1)`
between consecutive iterates starting at `k-1`, and `josephus k n` is the stated
difference. We require `n ≥ 2`: the printed claim is false at `n=1`, since every
positive `p` has `h_k^(p-1)(k-1) ≥ k-1 = n(k-1)`.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Corollary 1 (`integers-2024-G5-cor-1`). -/
public theorem_wanted josephus_eq_mul_sub_iterate_maximumNimH_pred (k n : ℕ)
    (hk : 2 ≤ k) (hn : 2 ≤ n) :
    ∃ p, 1 ≤ p ∧
      Nat.iterate (maximumNimH k) (p - 1) (k - 1) < n * (k - 1) ∧
      n * (k - 1) ≤ Nat.iterate (maximumNimH k) p (k - 1) ∧
      josephus k n = n * k - Nat.iterate (maximumNimH k) p (k - 1)

/-- Lemma 8: for positive `n` and `k ≥ 2`, let the real numbers `v` and `w` be
the two displayed logarithmic quotients. Iterating from `k-1` by the natural floor
of `w` and natural ceiling of `v` gives the lower and upper bounds on `n(k-1)`.
`Nat.floor` and `Nat.ceil` encode the indicated integer bounds; there is no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 8 (`integers-2024-G5-lem-8`). -/
public theorem_wanted maximumNimH_iterate_floor_le_mul_le_iterate_ceil (k n : ℕ)
    (hk : 2 ≤ k) (hn : 1 ≤ n) :
    let v : ℝ := Real.log n / (Real.log k - Real.log (k - 1))
    let w : ℝ := (Real.log (n + 1) - Real.log 2) / (Real.log k - Real.log (k - 1))
    Nat.iterate (maximumNimH k) (Nat.floor w) (k - 1) ≤ n * (k - 1) ∧
      n * (k - 1) ≤ Nat.iterate (maximumNimH k) (Nat.ceil v) (k - 1)

/-- Theorem 4: with the real `v,w` of Lemma 8, for `k ≥ 2` and `n ≥ 2` there is
a positive natural `p` between `⌊w⌋` and `⌈v⌉` for which `nk-h_k^p(k-1)` is the
one-based Josephus survivor. We require `n ≥ 2`: at `n=1`, `⌈v⌉=0`, contradicting
the required `p ≥ 1`.
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
