/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Rat.Star
import Mathlib.GroupTheory.Finiteness
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace MetaMathlibExt

private noncomputable def dilcherRHS (m n : ℕ) : ℚ :=
  ∑ js ∈ Finset.univ.filter
    (fun js : Fin m → Fin n => Monotone (fun i => (js i).val)),
    (∏ i, ((js i).val + 1 : ℚ))⁻¹

private noncomputable def dilcherLHS (m n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 n, ((n.choose k : ℚ) * (-1 : ℚ) ^ (k - 1)) / (k : ℚ) ^ m

private lemma dilcherLHS_range (m n : ℕ) :
    dilcherLHS m n =
      ∑ j ∈ Finset.range n, (((n.choose (j + 1) : ℚ) * (-1 : ℚ) ^ j) / ((j : ℚ) + 1) ^ m) := by
  unfold dilcherLHS
  have hI : Finset.Icc 1 n = (Finset.range n).image (· + 1) := by
    ext k
    constructor
    · intro h
      rw [Finset.mem_Icc] at h
      refine Finset.mem_image.mpr ⟨k - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro h
      rw [Finset.mem_image] at h
      obtain ⟨x, hx, rfl⟩ := h
      rw [Finset.mem_range] at hx
      rw [Finset.mem_Icc]
      omega
  rw [hI]
  rw [Finset.sum_image (fun x _ y _ h => by simpa using h)]
  apply Finset.sum_congr rfl
  intro j _
  have h1 : j + 1 - 1 = j := Nat.add_sub_cancel j 1
  have h2 : ((j + 1 : ℕ) : ℚ) = (j : ℚ) + 1 := by push_cast; ring
  rw [h1, h2]

private lemma choose_mul_succ_cast (N j : ℕ) :
    ((N + 1).choose (j + 1) : ℚ) * ((j : ℚ) + 1) = ((N : ℚ) + 1) * (N.choose j : ℚ) := by
  have h := Nat.choose_mul (Nat.succ_le_succ (Nat.zero_le j)) (n := N + 1) (k := j + 1) (s := 1)
  rw [Nat.choose_one_right] at h
  rw [Nat.choose_one_right] at h
  have hN : N + 1 - 1 = N := Nat.add_sub_cancel N 1
  have hj : j + 1 - 1 = j := Nat.add_sub_cancel j 1
  rw [hN, hj] at h
  have h2 : (((N + 1).choose (j + 1) * (j + 1) : ℕ) : ℚ) = (((N + 1) * N.choose j : ℕ) : ℚ) := by
    rw [h]
  push_cast at h2
  linarith [h2]

private lemma dilcherLHS_succ (r N : ℕ) :
    dilcherLHS (r + 1) (N + 1)
      = dilcherLHS (r + 1) N + ((N : ℚ) + 1)⁻¹ * dilcherLHS r (N + 1) := by
  rw [dilcherLHS_range, dilcherLHS_range, dilcherLHS_range]
  have hsplit : ∀ j ∈ Finset.range (N + 1),
      (((N + 1).choose (j + 1) : ℚ) * (-1 : ℚ) ^ j) / ((j : ℚ) + 1) ^ (r + 1)
      = ((((N.choose j : ℚ) * (-1 : ℚ) ^ j) / ((j : ℚ) + 1) ^ (r + 1))
        + (((N.choose (j + 1) : ℚ) * (-1 : ℚ) ^ j) / ((j : ℚ) + 1) ^ (r + 1))) := by
    intro j _
    have hcc : ((N + 1).choose (j + 1) : ℚ) = (N.choose j : ℚ) + (N.choose (j + 1) : ℚ) := by
      have h := Nat.choose_succ_succ N j
      exact_mod_cast h
    rw [hcc, add_mul, add_div]
  have htail : (∑ j ∈ Finset.range (N + 1),
        (((N.choose (j + 1) : ℚ) * (-1 : ℚ) ^ j) / ((j : ℚ) + 1) ^ (r + 1)))
      = ∑ j ∈ Finset.range N,
        (((N.choose (j + 1) : ℚ) * (-1 : ℚ) ^ j) / ((j : ℚ) + 1) ^ (r + 1)) := by
    rw [Finset.sum_range_succ]
    have h0 : (N.choose (N + 1) : ℚ) = 0 := by
      exact_mod_cast Nat.choose_eq_zero_of_lt (Nat.lt_succ_self N)
    rw [h0, zero_mul, zero_div, add_zero]
  have hfirst : (∑ j ∈ Finset.range (N + 1),
        (((N.choose j : ℚ) * (-1 : ℚ) ^ j) / ((j : ℚ) + 1) ^ (r + 1)))
      = ((N : ℚ) + 1)⁻¹ * (∑ j ∈ Finset.range (N + 1),
        (((N + 1).choose (j + 1) : ℚ) * (-1 : ℚ) ^ j) / ((j : ℚ) + 1) ^ r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hcm := choose_mul_succ_cast N j
    have hu : ((j : ℚ) + 1) ≠ 0 := ne_of_gt (by positivity)
    have hv : ((N : ℚ) + 1) ≠ 0 := ne_of_gt (by positivity)
    have key : (N.choose j : ℚ) * (((j : ℚ) + 1))⁻¹
        = ((N : ℚ) + 1)⁻¹ * ((N + 1).choose (j + 1) : ℚ) := by
      rw [← div_eq_mul_inv (N.choose j : ℚ) ((j : ℚ) + 1),
        mul_comm ((N : ℚ) + 1)⁻¹ _, ← div_eq_mul_inv _ ((N : ℚ) + 1),
        div_eq_div_iff hu hv]
      linear_combination -hcm
    have step1 : ((N.choose j : ℚ) * (-1 : ℚ) ^ j) / ((j : ℚ) + 1) ^ (r + 1)
        = ((N.choose j : ℚ) * (((j : ℚ) + 1))⁻¹)
          * (((-1 : ℚ) ^ j) * ((((j : ℚ) + 1)) ^ r)⁻¹) := by
      rw [pow_succ, div_eq_mul_inv, mul_inv]
      ring
    rw [step1, key]
    rw [div_eq_mul_inv]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, htail, hfirst, add_comm]

private lemma dilcherRHS_cast (r N : ℕ) :
    dilcherRHS (r + 1) N =
    (∑ js ∈ (Finset.univ.filter
        (fun js : Fin (r + 1) → Fin (N + 1) => Monotone (fun i => (js i).val))).filter
        (fun js => ¬ js (Fin.last r) = Fin.last N),
      (∏ i, ((js i).val + 1 : ℚ))⁻¹) := by
  unfold dilcherRHS
  refine Finset.sum_bij
    (fun (f : Fin (r + 1) → Fin N) _ (i : Fin (r + 1)) => Fin.castSucc (f i)) ?_ ?_ ?_ ?_
  · intro f hf
    obtain ⟨_, hfmono⟩ := Finset.mem_filter.mp hf
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro a b hab
      exact hfmono hab
    · intro hcon
      have h1 : (f (Fin.last r)).val = N := by
        have h2 := congrArg Fin.val hcon
        rwa [Fin.val_last] at h2
      have h3 := (f (Fin.last r)).isLt
      omega
  · intro f1 _ f2 _ h
    funext i
    have h2 := congrFun h i
    exact Fin.castSucc_inj.mp h2
  · intro js hjs
    obtain ⟨hbmem, hne⟩ := Finset.mem_filter.mp hjs
    obtain ⟨_, hmono⟩ := Finset.mem_filter.mp hbmem
    refine ⟨fun i => (⟨(js i).val, ?_⟩ : Fin N), ?_, ?_⟩
    · have hle : (js i).val ≤ (js (Fin.last r)).val := hmono (Fin.le_last i)
      have hlt : (js (Fin.last r)).val < N + 1 := (js (Fin.last r)).isLt
      have hne' : (js (Fin.last r)).val ≠ N := by
        intro hc
        apply hne
        rw [Fin.ext_iff, Fin.val_last]
        exact hc
      omega
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro a b hab
      exact hmono hab
    · funext i
      apply Fin.ext_iff.mpr
      rfl
  · intro f _
    congr 1

private lemma dilcherRHS_snoc (r N : ℕ) :
    (∑ js ∈ (Finset.univ.filter
        (fun js : Fin (r + 1) → Fin (N + 1) => Monotone (fun i => (js i).val))).filter
        (fun js => js (Fin.last r) = Fin.last N),
      (∏ i, ((js i).val + 1 : ℚ))⁻¹)
    = ((N : ℚ) + 1)⁻¹ * dilcherRHS r (N + 1) := by
  unfold dilcherRHS
  rw [Finset.mul_sum]
  refine Finset.sum_bij
    (fun (js : Fin (r + 1) → Fin (N + 1)) _ (i : Fin r) => js i.castSucc) ?_ ?_ ?_ ?_
  · intro js hjs
    obtain ⟨hbmem, _⟩ := Finset.mem_filter.mp hjs
    obtain ⟨_, hmono⟩ := Finset.mem_filter.mp hbmem
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro a b hab
    exact hmono (Fin.castSucc_le_castSucc_iff.mpr hab)
  · intro js1 h1 js2 h2 h
    funext i
    by_cases hi : i = Fin.last r
    · subst hi
      have e1 : js1 (Fin.last r) = Fin.last N := (Finset.mem_filter.mp h1).2
      have e2 : js2 (Fin.last r) = Fin.last N := (Finset.mem_filter.mp h2).2
      rw [e1, e2]
    · obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      have h2 := congrFun h i'
      exact h2
  · intro f hf
    obtain ⟨_, hfmono⟩ := Finset.mem_filter.mp hf
    refine ⟨Fin.snoc (α := fun _ => Fin (N + 1)) f (Fin.last N), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro a b hab
        change ((Fin.snoc (α := fun _ => Fin (N + 1)) f (Fin.last N) a).val)
          ≤ ((Fin.snoc (α := fun _ => Fin (N + 1)) f (Fin.last N) b).val)
        by_cases hb : b = Fin.last r
        · subst hb
          rw [Fin.snoc_last, Fin.val_last]
          have h := (Fin.snoc (α := fun _ => Fin (N + 1)) f (Fin.last N) a).isLt
          omega
        · obtain ⟨b', rfl⟩ := Fin.eq_castSucc_of_ne_last hb
          show ((Fin.snoc (α := fun _ => Fin (N + 1)) f (Fin.last N) a).val)
            ≤ ((Fin.snoc (α := fun _ => Fin (N + 1)) f (Fin.last N) b'.castSucc).val)
          rw [Fin.snoc_castSucc]
          by_cases ha : a = Fin.last r
          · subst ha
            exfalso
            exact hb (le_antisymm hab (Fin.le_last _)).symm
          · obtain ⟨a', rfl⟩ := Fin.eq_castSucc_of_ne_last ha
            show ((Fin.snoc (α := fun _ => Fin (N + 1)) f (Fin.last N) a'.castSucc).val)
              ≤ ((f b').val)
            rw [Fin.snoc_castSucc]
            exact hfmono (Fin.castSucc_le_castSucc_iff.mp hab)
      · exact Fin.snoc_last _ _
    · funext i
      exact Fin.snoc_castSucc _ _ i
  · intro js hjs
    obtain ⟨hbmem, hlast⟩ := Finset.mem_filter.mp hjs
    obtain ⟨_, hmono⟩ := Finset.mem_filter.mp hbmem
    change (∏ i : Fin (r + 1), ((js i).val + 1 : ℚ))⁻¹
      = ((N : ℚ) + 1)⁻¹ * (∏ i : Fin r, ((js i.castSucc).val + 1 : ℚ))⁻¹
    have hprod : (∏ i : Fin (r + 1), ((js i).val + 1 : ℚ))
        = (∏ i : Fin r, ((js i.castSucc).val + 1 : ℚ)) * (((js (Fin.last r)).val + 1 : ℚ)) :=
      Fin.prod_univ_castSucc _
    have hlastF : ((js (Fin.last r)).val + 1 : ℚ) = (N : ℚ) + 1 := by
      rw [hlast, Fin.val_last]
    rw [hprod, hlastF, mul_inv_rev]

private lemma dilcherLHS_zero_succ (N : ℕ) : dilcherLHS 0 (N + 1) = 1 := by
  have hAlt : (∑ m ∈ Finset.range (N + 1 + 1), (-1 : ℚ) ^ m * ((N + 1).choose m : ℚ)) = 0 := by
    have h := Int.alternating_sum_range_choose_of_ne (n := N + 1) (by omega)
    exact_mod_cast h
  rw [Finset.sum_range_succ' (fun m => (-1 : ℚ) ^ m * ((N + 1).choose m : ℚ)) (N + 1)] at hAlt
  simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one] at hAlt
  have hneg : (∑ k ∈ Finset.range (N + 1), (-1 : ℚ) ^ (k + 1) * ((N + 1).choose (k + 1) : ℚ))
      = -(∑ k ∈ Finset.range (N + 1), ((N + 1).choose (k + 1) : ℚ) * (-1 : ℚ) ^ k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ]
    ring
  rw [hneg] at hAlt
  have hsum : (∑ k ∈ Finset.range (N + 1), ((N + 1).choose (k + 1) : ℚ) * (-1 : ℚ) ^ k) = 1 := by
    linarith [hAlt]
  rw [dilcherLHS_range]
  have hterm : ∀ k ∈ Finset.range (N + 1),
      (((N + 1).choose (k + 1) : ℚ) * (-1 : ℚ) ^ k) / ((k : ℚ) + 1) ^ 0
        = ((N + 1).choose (k + 1) : ℚ) * (-1 : ℚ) ^ k := by
    intro k _
    rw [pow_zero, div_one]
  rw [Finset.sum_congr rfl hterm]
  exact hsum

private lemma dilcherRHS_succ (r N : ℕ) :
    dilcherRHS (r + 1) (N + 1)
      = dilcherRHS (r + 1) N + ((N : ℚ) + 1)⁻¹ * dilcherRHS r (N + 1) := by
  have hbase : dilcherRHS (r + 1) (N + 1)
      = (∑ js ∈ (Finset.univ.filter
          (fun js : Fin (r + 1) → Fin (N + 1) => Monotone (fun i => (js i).val))).filter
          (fun js => js (Fin.last r) = Fin.last N),
        (∏ i, ((js i).val + 1 : ℚ))⁻¹)
      + (∑ js ∈ (Finset.univ.filter
          (fun js : Fin (r + 1) → Fin (N + 1) => Monotone (fun i => (js i).val))).filter
          (fun js => ¬ js (Fin.last r) = Fin.last N),
        (∏ i, ((js i).val + 1 : ℚ))⁻¹) := by
    unfold dilcherRHS
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hA := dilcherRHS_cast r N
  have hB := dilcherRHS_snoc r N
  rw [hbase, hB, hA, add_comm]

private lemma dilcherLHS_succ_zero (r : ℕ) : dilcherLHS (r + 1) 0 = 0 := by
  simp [dilcherLHS]

private lemma dilcherRHS_succ_zero (r : ℕ) : dilcherRHS (r + 1) 0 = 0 := by
  unfold dilcherRHS
  have : (Finset.univ : Finset (Fin (r + 1) → Fin 0)) = ∅ := Finset.univ_eq_empty
  rw [this, Finset.filter_empty, Finset.sum_empty]

private lemma dilcherRHS_zero (N : ℕ) : dilcherRHS 0 (N + 1) = 1 := by
  unfold dilcherRHS
  have hmono : ∀ js : Fin 0 → Fin (N + 1), Monotone (fun i => (js i).val) := by
    intro js a b _
    exact a.elim0
  rw [Finset.filter_true_of_mem (fun js _ => hmono js)]
  have h1 : ∀ js : Fin 0 → Fin (N + 1), (∏ i, ((js i).val + 1 : ℚ))⁻¹ = 1 := by
    intro js
    have hprod : (∏ i, ((js i).val + 1 : ℚ)) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      exact i.elim0
    rw [hprod, inv_one]
  have hU : Unique (Fin 0 → Fin (N + 1)) := Pi.uniqueOfIsEmpty _
  rw [@Finset.univ_unique _ _ hU, Finset.sum_singleton]
  exact h1 _

private lemma dilcher_main (N : ℕ) : ∀ (m : ℕ), dilcherLHS m (N + 1) = dilcherRHS m (N + 1) := by
  induction N with
  | zero =>
    intro m
    induction m with
    | zero =>
      rw [dilcherLHS_zero_succ, dilcherRHS_zero]
    | succ r ihr =>
      rw [dilcherLHS_succ, dilcherRHS_succ, dilcherLHS_succ_zero, dilcherRHS_succ_zero, ihr]
  | succ K ihK =>
    intro m
    induction m with
    | zero =>
      rw [dilcherLHS_zero_succ, dilcherRHS_zero]
    | succ r ihr =>
      rw [dilcherLHS_succ, dilcherRHS_succ, ihK, ihr]

/-- **Dilcher's finite multiple harmonic identity for every exponent.** For every natural number
$m$ (including $m = 0$) and every positive integer $n$,
$$
\sum_{k=1}^{n} \frac{(-1)^{k-1} \binom{n}{k}}{k^m}
= \sum_{1 \le j_1 \le \cdots \le j_m \le n} \frac{1}{j_1 \cdots j_m},
$$
where the right side sums over all weakly increasing tuples $(j_1, \ldots, j_m)$ of integers
between $1$ and $n$; for $m = 0$ there is only the empty tuple, whose term is $1$. -/
theorem dilcher_finite_multiple_harmonic_identity_general (m n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.Icc 1 n,
      ((n.choose k : ℚ) * (-1 : ℚ) ^ (k - 1)) / (k : ℚ) ^ m) =
    ∑ js ∈ Finset.univ.filter
      (fun js : Fin m → Fin n => Monotone (fun i => (js i).val)),
      (∏ i, ((js i).val + 1 : ℚ))⁻¹ := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact dilcher_main N m

set_option linter.unusedVariables false in
/-- **Dilcher's finite multiple harmonic identity.** For all positive integers $m$ and $n$,
$$
\sum_{k=1}^{n} \frac{(-1)^{k-1} \binom{n}{k}}{k^m}
= \sum_{1 \le j_1 \le \cdots \le j_m \le n} \frac{1}{j_1 \cdots j_m},
$$
where the right side sums over all weakly increasing tuples $(j_1, \ldots, j_m)$ of integers
between $1$ and $n$.

Source: Khristo N. Boyadzhiev, "Harmonic Number Identities Via Euler's Transform",
Journal of Integer Sequences 12 (2009), Article 09.6.1,
`https://cs.uwaterloo.ca/journals/JIS/VOL12/Boyadzhiev/boyadzhiev3.tex`,
controlling statement equation (26), lines 323–331. Boyadzhiev attributes the
identity to Karl Dilcher, "Some q-series identities related to divisor functions",
Discrete Mathematics 145 (1995), 83–93, DOI 10.1016/0012-365X(95)00092-B
(the JIS bibliography prints "divisor factors").
-/
theorem dilcher_finite_multiple_harmonic_identity (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) :
    (∑ k ∈ Finset.Icc 1 n,
      ((n.choose k : ℚ) * (-1 : ℚ) ^ (k - 1)) / (k : ℚ) ^ m) =
    ∑ js ∈ Finset.univ.filter
      (fun js : Fin m → Fin n => Monotone (fun i => (js i).val)),
      (∏ i, ((js i).val + 1 : ℚ))⁻¹ := by
  exact dilcher_finite_multiple_harmonic_identity_general m n hn

end MetaMathlibExt
