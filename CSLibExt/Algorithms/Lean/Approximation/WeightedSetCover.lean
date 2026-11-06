/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Approximation.SetCover

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Weighted greedy set cover and the harmonic bound

The weighted set-covering problem: each set `S` of the family `F` has a cost `w S ≥ 0`, and a
cover of `U` should have small total cost. The greedy algorithm (V. Chvátal, *A greedy heuristic
for the set-covering problem*, Math. Oper. Res. 4(3), 1979; Vazirani, *Approximation
Algorithms*, Section 2.1) repeatedly takes a set minimizing the cost per newly covered element,
`w S / |S ∩ U|`, among the sets that meet the uncovered set `U`. With unit costs it is CLRS's
`GREEDY-SET-COVER` (`SetCover.lean`).

`weightedGreedySetCover w F U` returns the chosen sets, ties going to the first minimizing set in
list order. Results: the chosen sets are drawn from `F` (`weightedGreedySetCover_mem`) and cover
`U` when `F` does (`weightedGreedySetCover_covers`); for every cover `C*` of `U` drawn from `F`,
the greedy cost is at most `∑_{S ∈ C*} w S · H(|S ∩ U|)`
(`weightedGreedySetCover_cost_le_sum_harmonic`), hence at most `H(d)` times the cost of `C*` when
every set has at most `d` elements (`weightedGreedySetCover_approx`), where `H` is Mathlib's
`harmonic`.

The proof is the unweighted potential argument of `SetCover.lean` with costs: taking `S₁` with
ratio `r = w S₁ / k`, `k = |S₁ ∩ U|`, lowers each term `w S · H(|S ∩ U|)` of the potential by at
least `w S · |S ∩ S₁ ∩ U| / |S ∩ U| ≥ r · |S ∩ S₁ ∩ U|` (greedy guarantees
`r ≤ w S / |S ∩ U|`), and these drops add up to at least `r · k = w S₁` because `C*` covers the
`k` new elements. It reuses `div_le_harmonic_sub`, `harmonic_le_harmonic`,
`card_le_sum_card_inter` and `card_sdiff_lt` from `SetCover.lean`.

## Cost model

As in `SetCover.lean`: every search for a best set, including the final one that finds nothing,
costs `|F| + ∑_{S ∈ F} |S|` (one unit per set visited, one per element scanned to compute
`|S ∩ U|`); arithmetic on costs, removing the chosen set from `U` and building the result are
free. There are at most `|U| + 1` searches (`weightedGreedySetCover_time_le`).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

universe u

variable {α : Type u} [DecidableEq α]

/-- **Set with the least cost per new element.** Given a list $F$ of finite sets, a finite set $U$
and a rational cost $w(S)$ for each finite set $S$, this is the first set $S$ in $F$ with
$S \cap U \ne \emptyset$ that minimizes the ratio $w(S) / |S \cap U|$ among the sets of $F$ meeting
$U$, or nothing when no set of $F$ meets $U$. -/
def bestRatioSet (w : Finset α → ℚ) (F : List (Finset α)) (U : Finset α) : Option (Finset α) :=
  (F.filter fun S => (S ∩ U).card ≠ 0).argmax fun S => -(w S / (S ∩ U).card)

theorem bestRatioSet_spec {w : Finset α → ℚ} {F : List (Finset α)} {U S : Finset α}
    (h : bestRatioSet w F U = some S) :
    S ∈ F ∧ (S ∩ U).card ≠ 0 ∧
      ∀ T ∈ F, (T ∩ U).card ≠ 0 → w S / (S ∩ U).card ≤ w T / (T ∩ U).card := by
  have hmem := List.argmax_mem (Option.mem_def.2 h)
  simp only [List.mem_filter, decide_eq_true_eq] at hmem
  refine ⟨hmem.1, hmem.2, fun T hT hTU => ?_⟩
  have := List.le_of_mem_argmax (f := fun S => -(w S / (S ∩ U).card))
    (List.mem_filter.2 ⟨hT, by simpa using hTU⟩) (Option.mem_def.2 h)
  simpa using this

theorem bestRatioSet_eq_none {w : Finset α → ℚ} {F : List (Finset α)} {U : Finset α}
    (h : bestRatioSet w F U = none) : ∀ T ∈ F, (T ∩ U).card = 0 := by
  intro T hT
  by_contra hTU
  have := List.argmax_eq_none.1 h
  have hmem : T ∈ F.filter fun S => (S ∩ U).card ≠ 0 :=
    List.mem_filter.2 ⟨hT, by simpa using hTU⟩
  rw [this] at hmem
  simp at hmem

/-- **Weighted greedy set cover.** Let $F = [S_1, \dots, S_n]$ be a list of finite sets, $U$ a
finite set and $w$ a function giving each finite set $S$ a rational cost $w(S)$. The weighted
greedy set cover of $U$ from $F$ with costs $w$ is computed as follows. If no $S_i$ meets $U$,
the result is the empty list. Otherwise let $T$ be the first $S_i$ in the list with
$S_i \cap U \ne \emptyset$ that minimizes $w(S_i) / |S_i \cap U|$ among the sets of $F$ meeting
$U$; the result is $T$ followed by the weighted greedy set cover of $U \setminus T$ from $F$ with
costs $w$. Each step, including the last one, costs $n + |S_1| + \dots + |S_n|$. -/
def weightedGreedySetCover (w : Finset α → ℚ) (F : List (Finset α)) (U : Finset α) :
    TimeM ℕ (List (Finset α)) := do
  ✓[F.length + (F.map Finset.card).sum]
  match _h : bestRatioSet w F U with
  | none => pure []
  | some S => do
      let C ← weightedGreedySetCover w F (U \ S)
      pure (S :: C)
termination_by U.card
decreasing_by exact card_sdiff_lt (bestRatioSet_spec _h).2.1

/-! ## The result is a cover from the family -/

/-- **The weighted greedy set cover uses sets of the family.** For every list $F$ of finite sets,
finite set $U$ and rational cost function $w$ on finite sets, every set chosen by the weighted
greedy set cover of $U$ from $F$ with costs $w$ belongs to $F$. -/
theorem weightedGreedySetCover_mem (w : Finset α → ℚ) (F : List (Finset α)) (U : Finset α) :
    ∀ S ∈ (weightedGreedySetCover w F U).ret, S ∈ F := by
  induction h : U.card using Nat.strong_induction_on generalizing U with
  | _ n ih =>
    rw [weightedGreedySetCover]
    cases hb : bestRatioSet w F U with
    | none => simp
    | some S₁ =>
        simp only [ret_bind, ret_pure, List.mem_cons]
        rintro T (rfl | hT)
        · exact (bestRatioSet_spec hb).1
        · exact ih _ (h ▸ card_sdiff_lt (bestRatioSet_spec hb).2.1) _ rfl T hT

/-- **The weighted greedy set cover is a cover.** Let $F$ be a list of finite sets, $U$ a finite
set and $w$ any rational cost function on finite sets. If every element of $U$ lies in some set of
$F$, then every element of $U$ lies in some set chosen by the weighted greedy set cover of $U$ from
$F$ with costs $w$. -/
theorem weightedGreedySetCover_covers (w : Finset α → ℚ) (F : List (Finset α)) (U : Finset α)
    (hU : ∀ x ∈ U, ∃ S ∈ F, x ∈ S) :
    ∀ x ∈ U, ∃ S ∈ (weightedGreedySetCover w F U).ret, x ∈ S := by
  induction h : U.card using Nat.strong_induction_on generalizing U with
  | _ n ih =>
    intro x hx
    rw [weightedGreedySetCover]
    obtain ⟨T, hT, hxT⟩ := hU x hx
    cases hb : bestRatioSet w F U with
    | none =>
        have := bestRatioSet_eq_none hb T hT
        rw [Finset.card_eq_zero] at this
        exact absurd (Finset.mem_inter.2 ⟨hxT, hx⟩) (this ▸ Finset.notMem_empty x)
    | some S₁ =>
        simp only [ret_bind, ret_pure, List.mem_cons, exists_eq_or_imp]
        by_cases hxS : x ∈ S₁
        · exact Or.inl hxS
        · refine Or.inr (ih _ (h ▸ card_sdiff_lt (bestRatioSet_spec hb).2.1) (U \ S₁)
            (fun y hy => hU y (Finset.mem_sdiff.1 hy).1) rfl x (Finset.mem_sdiff.2 ⟨hx, hxS⟩))

/-! ## Cost of the search -/

/-- **Running time of weighted greedy set cover.** Let $F = [S_1, \dots, S_m]$ be a list of finite
sets, $U$ a finite set and $w$ a rational cost function on finite sets. The weighted greedy set
cover of $U$ from $F$ with costs $w$ runs in time at most
$(|U| + 1)\,(m + |S_1| + \dots + |S_m|)$: at most $|U| + 1$ searches for a best set, each costing
$m$ plus the total size of the sets of $F$. -/
theorem weightedGreedySetCover_time_le (w : Finset α → ℚ) (F : List (Finset α)) (U : Finset α) :
    (weightedGreedySetCover w F U).time ≤
      (U.card + 1) * (F.length + (F.map Finset.card).sum) := by
  induction h : U.card using Nat.strong_induction_on generalizing U with
  | _ n ih =>
    rw [weightedGreedySetCover]
    cases hb : bestRatioSet w F U with
    | none =>
        simp only [time_bind, time_tick, time_pure, Nat.add_zero]
        exact Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
    | some S₁ =>
        simp only [time_bind, time_tick, time_pure, Nat.add_zero]
        have hlt := card_sdiff_lt (bestRatioSet_spec hb).2.1
        have := ih _ (h ▸ hlt) _ rfl
        have hmono : ((U \ S₁).card + 1) * (F.length + (F.map Finset.card).sum) ≤
            n * (F.length + (F.map Finset.card).sum) :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul]
        omega

/-! ## The harmonic bound -/

/-- **Total cost of a list of sets.** For a function $w$ assigning a rational cost to each finite
set, the total cost of a list $C = [S_1, \dots, S_m]$ of finite sets is
$w(S_1) + \dots + w(S_m)$, a set that occurs several times in $C$ being counted each time. -/
def totalCost (w : Finset α → ℚ) (C : List (Finset α)) : ℚ := (C.map w).sum

/-- **Potential bound for weighted greedy set cover.** Let $F$ be a list of finite sets, $U$ a
finite set and $w$ a rational cost function on finite sets with $w(S) \ge 0$ for every $S$ in $F$.
If $C^*$ is a list of sets from $F$ whose union contains $U$, then the weighted greedy set cover of
$U$ from $F$ with costs $w$ has total cost at most $\sum_{S \in C^*} w(S)\, H(|S \cap U|)$, the sum
running over the entries of $C^*$ with repetition, where
$H(n) = 1 + \frac{1}{2} + \dots + \frac{1}{n}$ is the $n$-th harmonic number. -/
theorem weightedGreedySetCover_cost_le_sum_harmonic (w : Finset α → ℚ) (F : List (Finset α))
    (U : Finset α) (hw : ∀ S ∈ F, 0 ≤ w S) (Cstar : List (Finset α))
    (hsub : ∀ S ∈ Cstar, S ∈ F) (hcov : ∀ x ∈ U, ∃ S ∈ Cstar, x ∈ S) :
    totalCost w (weightedGreedySetCover w F U).ret ≤
      (Cstar.map fun S => w S * harmonic (S ∩ U).card).sum := by
  induction h : U.card using Nat.strong_induction_on generalizing U with
  | _ n ih =>
    rw [weightedGreedySetCover]
    cases hb : bestRatioSet w F U with
    | none =>
        simp only [ret_bind, ret_pure, totalCost, List.map_nil, List.sum_nil]
        exact List.sum_nonneg fun q hq => by
          obtain ⟨S, hS, rfl⟩ := List.mem_map.1 hq
          exact mul_nonneg (hw S (hsub S hS)) (Finset.sum_nonneg fun _ _ => by positivity)
    | some S₁ =>
        simp only [ret_bind, ret_pure, totalCost, List.map_cons, List.sum_cons]
        obtain ⟨hS₁F, hS₁U, hmin⟩ := bestRatioSet_spec hb
        set k := (S₁ ∩ U).card
        have hIH := ih _ (h ▸ card_sdiff_lt hS₁U) (U \ S₁)
          (fun x hx => hcov x (Finset.mem_sdiff.1 hx).1) rfl
        simp only [totalCost] at hIH
        have hkpos : (0 : ℚ) < k := by exact_mod_cast Nat.pos_of_ne_zero hS₁U
        set r : ℚ := w S₁ / k with hr
        have hr0 : 0 ≤ r := div_nonneg (hw S₁ hS₁F) hkpos.le
        -- splitting `S ∩ U` along `S₁`
        have hsplit : ∀ S : Finset α,
            (S ∩ (U \ S₁)).card + (S ∩ (S₁ ∩ U)).card = (S ∩ U).card := by
          intro S
          have := Finset.card_sdiff_add_card_inter (S ∩ U) S₁
          rw [Finset.inter_sdiff_assoc] at this
          convert this using 3
          ext y
          simp only [Finset.mem_inter]
          tauto
        -- each term of the potential drops by at least `r · |S ∩ S₁ ∩ U|`
        have hdrop : ∀ S ∈ Cstar, w S * harmonic (S ∩ (U \ S₁)).card +
            r * (S ∩ (S₁ ∩ U)).card ≤ w S * harmonic (S ∩ U).card := by
          intro S hS
          have hwS := hw S (hsub S hS)
          set a := (S ∩ U).card
          set d := (S ∩ (S₁ ∩ U)).card
          have hda : d ≤ a := by have := hsplit S; omega
          have h2 : a - d = (S ∩ (U \ S₁)).card := by have := hsplit S; omega
          rcases Nat.eq_zero_or_pos a with ha | ha
          · have hd0 : d = 0 := by omega
            have h3 : (S ∩ (U \ S₁)).card = a := by omega
            rw [h3, hd0]
            simp
          · have h1 := div_le_harmonic_sub (a := a) (d := d) (k := a) hda le_rfl
            rw [h2] at h1
            have hapos : (0 : ℚ) < a := by exact_mod_cast ha
            have hratio : r ≤ w S / a := hmin S (hsub S hS) (by omega)
            -- `r · d ≤ (w S / a) · d = w S · (d / a) ≤ w S · (H a - H (a - d))`
            have : r * d ≤ w S * (harmonic a - harmonic (S ∩ (U \ S₁)).card) := by
              calc r * d ≤ w S / a * d := mul_le_mul_of_nonneg_right hratio (by positivity)
                _ = w S * (d / a) := by ring
                _ ≤ _ := mul_le_mul_of_nonneg_left h1 hwS
            linarith
        have hcount : (k : ℚ) ≤ (Cstar.map fun S => ((S ∩ (S₁ ∩ U)).card : ℚ)).sum := by
          have := card_le_sum_card_inter Cstar (S₁ ∩ U)
            (fun x hx => hcov x (Finset.mem_inter.1 hx).2)
          have := (Nat.cast_le (α := ℚ)).2 this
          simpa [Nat.cast_list_sum, List.map_map, Function.comp_def] using this
        have hone : w S₁ ≤ (Cstar.map fun S => r * ((S ∩ (S₁ ∩ U)).card : ℚ)).sum := by
          rw [List.sum_map_mul_left]
          calc w S₁ = r * k := by rw [hr]; field_simp
            _ ≤ _ := mul_le_mul_of_nonneg_left hcount hr0
        have hsum := List.sum_le_sum hdrop
        rw [List.sum_map_add] at hsum
        linarith

/-- **Chvátal's bound.** Let $F$ be a list of finite sets, $U$ a finite set, $w$ a rational cost
function on finite sets with $w(S) \ge 0$ for every $S$ in $F$, and $d$ a natural number such that
every set in $F$ has at most $d$ elements. If $C^*$ is a list of sets from $F$ whose union contains
$U$, then the weighted greedy set cover of $U$ from $F$ with costs $w$ has total cost at most
$H(d)$ times the total cost of $C^*$, where $H(d) = 1 + \frac{1}{2} + \dots + \frac{1}{d}$ is the
$d$-th harmonic number. -/
theorem weightedGreedySetCover_approx (w : Finset α → ℚ) (F : List (Finset α)) (U : Finset α)
    (hw : ∀ S ∈ F, 0 ≤ w S) {d : ℕ} (hd : ∀ S ∈ F, S.card ≤ d) (Cstar : List (Finset α))
    (hsub : ∀ S ∈ Cstar, S ∈ F) (hcov : ∀ x ∈ U, ∃ S ∈ Cstar, x ∈ S) :
    totalCost w (weightedGreedySetCover w F U).ret ≤ harmonic d * totalCost w Cstar := by
  refine (weightedGreedySetCover_cost_le_sum_harmonic w F U hw Cstar hsub hcov).trans ?_
  have : ∀ S ∈ Cstar, w S * harmonic (S ∩ U).card ≤ harmonic d * w S := fun S hS => by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (harmonic_le_harmonic
      ((Finset.card_le_card Finset.inter_subset_left).trans (hd S (hsub S hS))))
      (hw S (hsub S hS))
  have := List.sum_le_sum this
  rw [totalCost, ← List.sum_map_mul_left]
  exact this

end Cslib.Algorithms.Lean.TimeM
