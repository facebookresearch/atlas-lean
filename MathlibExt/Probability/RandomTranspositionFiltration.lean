/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Basic.Real.Basic

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-!
# The elementary symmetriser filtration for random transpositions

Functions `f : Equiv.Perm α → M` on the permutations of a finite type are acted on by
transpositions on the right: `σ ↦ σ * Equiv.swap i j` swaps the values of `σ` at the positions
`i` and `j`.  For finite sets `D R : Finset α` we use the two unnormalised operators

* `transSum D f σ = ∑ i ∈ D, ∑ j ∈ D, f (σ * Equiv.swap i j)` (ordered pairs, diagonal included,
  so `transSum D = #D • 1 + 2 • ∑_{i < j ∈ D} (i j)`);
* `symSum R f σ = ∑ π, f (σ * π)`, the sum over the permutations `π` fixing every point outside
  `R`; equivalently (`symSum_eq_sum_agree`) the sum of `f τ` over all `τ` that agree with `σ`
  outside `R`.

## Main statements

* `transSum_symSum_comm`: `transSum D` commutes with `symSum R` when `R ⊆ D`;
* `symSum_mul_swap`: `symSum R f` is invariant under swaps inside `R`;
* `symSum_insert`: the coset decomposition
  `symSum (insert a R) f σ = symSum R f σ + ∑ i ∈ R, symSum R f (σ * swap i a)`;
* `transSum_sdiff_eigen`: if `transSum D f = μ • f` and `symSum (insert a R) f = 0` for all
  `a ∈ D \ R`, then `symSum R f` is an eigenfunction of `transSum (D \ R)` with eigenvalue
  `μ - #R ^ 2 + 2 * #(D \ R)`;
* `eigenvalue_le_card_mul`: an eigenvalue whose eigenfunction is killed by every `symSum B`,
  `B ⊆ D`, `t < #B`, is at most `#D * t`;
* `level_bounds`, `exists_level_bounds`, `exists_level_bounds_univ`: the two caps
  `μ ≤ #D * s` and `μ ≤ s ^ 2 + j ^ 2 - 2 * j` at the exact symmetriser level `s = #R`,
  `j = #D - s`.
-/

@[expose] public section

open Finset

namespace MathlibExt.Probability.RandomTranspositionFiltration

variable {α : Type*} [Fintype α] [DecidableEq α] {M : Type*}

section Definitions

variable [AddCommMonoid M]

/-- The unnormalised transposition sum over ordered pairs of positions in `D`, acting on the
right: `transSum D f σ = ∑ i ∈ D, ∑ j ∈ D, f (σ * Equiv.swap i j)`.  The diagonal terms `i = j`
contribute `#D • f σ`. -/
def transSum (D : Finset α) (f : Equiv.Perm α → M) (σ : Equiv.Perm α) : M :=
  ∑ i ∈ D, ∑ j ∈ D, f (σ * Equiv.swap i j)

/-- The unnormalised symmetriser over the permutations supported in `R`, acting on the right:
`symSum R f σ = ∑ π, f (σ * π)` over all `π` fixing every point outside `R`. -/
def symSum (R : Finset α) (f : Equiv.Perm α → M) (σ : Equiv.Perm α) : M :=
  ∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm α => ∀ i ∉ R, π i = i), f (σ * π)

private def permsOn (R : Finset α) : Finset (Equiv.Perm α) :=
  univ.filter (fun π : Equiv.Perm α => ∀ i ∉ R, π i = i)

private theorem mem_permsOn {R : Finset α} {π : Equiv.Perm α} :
    π ∈ permsOn R ↔ ∀ i ∉ R, π i = i := by simp [permsOn]

private theorem maps_permsOn {R : Finset α} {π : Equiv.Perm α} (hπ : π ∈ permsOn R)
    {i : α} (hi : i ∈ R) : π i ∈ R := by
  by_contra h
  have hfix : π i = i := π.injective (mem_permsOn.mp hπ (π i) h)
  exact h (hfix.symm ▸ hi)

/-- A symmetriser is the sum on the fibre determined by all exterior positions. -/
theorem symSum_eq_sum_agree (R : Finset α) (f : Equiv.Perm α → M) (σ : Equiv.Perm α) :
    symSum R f σ = ∑ τ ∈ univ.filter (fun τ : Equiv.Perm α => ∀ x ∉ R, τ x = σ x), f τ := by
  classical
  unfold symSum
  apply sum_nbij' (σ * ·) (σ⁻¹ * ·)
  · intro π hπ
    apply mem_filter.mpr ⟨mem_univ _, ?_⟩
    intro x hx
    simp [Equiv.Perm.mul_apply, (mem_filter.mp hπ).2 x hx]
  · intro τ hτ
    apply mem_filter.mpr ⟨mem_univ _, ?_⟩
    intro x hx
    simp [Equiv.Perm.mul_apply, (mem_filter.mp hτ).2 x hx]
  · simp
  · simp
  · simp

/-- The symmetriser depends only on the exterior positions. -/
theorem symSum_congr_of_agree (R : Finset α) (f : Equiv.Perm α → M) {σ τ : Equiv.Perm α}
    (h : ∀ x ∉ R, σ x = τ x) : symSum R f σ = symSum R f τ := by
  simp_rw [symSum_eq_sum_agree]
  congr 1
  ext π
  simp only [mem_filter, mem_univ, true_and]
  exact forall_congr' fun x => forall_congr' fun hx => by rw [h x hx]

/-- Swapping two interior positions does not change a symmetrised function. -/
theorem symSum_mul_swap {R : Finset α} (f : Equiv.Perm α → M) (σ : Equiv.Perm α)
    {i j : α} (hi : i ∈ R) (hj : j ∈ R) :
    symSum R f (σ * Equiv.swap i j) = symSum R f σ := by
  apply symSum_congr_of_agree
  intro x hx
  simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne
    (ne_of_mem_of_not_mem hi hx).symm (ne_of_mem_of_not_mem hj hx).symm]

/-- Inserting a position splits the larger subgroup into one coset per possible image. -/
theorem symSum_insert {R : Finset α} (f : Equiv.Perm α → M) (σ : Equiv.Perm α)
    {a : α} (ha : a ∉ R) :
    symSum (insert a R) f σ = symSum R f σ + ∑ i ∈ R, symSum R f (σ * Equiv.swap i a) := by
  classical
  let S := insert a R
  have haS : a ∈ S := mem_insert_self _ _
  have fibre (i : α) (hi : i ∈ S) :
      ∑ π ∈ (permsOn S).filter (fun π => π a = i), f (σ * π) =
        symSum R f (σ * Equiv.swap i a) := by
    change _ = ∑ ρ ∈ permsOn R, f ((σ * Equiv.swap i a) * ρ)
    apply sum_nbij' (Equiv.swap i a * ·) (Equiv.swap i a * ·)
    · intro π hπ
      obtain ⟨hS, hia⟩ := mem_filter.mp hπ
      apply mem_permsOn.mpr
      intro x hx
      by_cases hxa : x = a
      · subst x; simp [Equiv.Perm.mul_apply, hia]
      · have hxS : x ∉ S := by simp [S, hxa, hx]
        simp [Equiv.Perm.mul_apply, mem_permsOn.mp hS x hxS,
          Equiv.swap_apply_of_ne_of_ne (ne_of_mem_of_not_mem hi hxS).symm hxa]
    · intro ρ hρ
      apply mem_filter.mpr
      refine ⟨mem_permsOn.mpr fun x hx => ?_, ?_⟩
      · have hxR : x ∉ R := fun hh => hx (mem_insert_of_mem hh)
        simp [Equiv.Perm.mul_apply, mem_permsOn.mp hρ x hxR, Equiv.swap_apply_of_ne_of_ne
          (ne_of_mem_of_not_mem hi hx).symm (ne_of_mem_of_not_mem haS hx).symm]
      · simp [Equiv.Perm.mul_apply, mem_permsOn.mp hρ a ha]
    · intro π _; simp [← mul_assoc]
    · intro ρ _; simp [← mul_assoc]
    · intro π _; simp [mul_assoc, ← mul_assoc (Equiv.swap i a)]
  change (∑ π ∈ permsOn S, _) = _
  rw [← sum_fiberwise_of_maps_to (fun π hπ => maps_permsOn hπ haS) (fun π => f (σ * π)),
    sum_congr rfl fibre]
  simp [S, ha, show Equiv.refl α = (1 : Equiv.Perm α) from rfl]

/-- A symmetriser on `R ⊆ D` commutes with the transposition sum on `D`. -/
theorem transSum_symSum_comm {R D : Finset α} (hRD : R ⊆ D) (f : Equiv.Perm α → M) :
    transSum D (symSum R f) = symSum R (transSum D f) := by
  classical
  funext σ
  change (∑ i ∈ D, ∑ j ∈ D, ∑ π ∈ permsOn R, f (σ * Equiv.swap i j * π)) =
    ∑ π ∈ permsOn R, ∑ i ∈ D, ∑ j ∈ D, f (σ * π * Equiv.swap i j)
  simp_rw [sum_comm (s := D) (t := permsOn R)]
  apply sum_congr rfl
  intro π hπ
  have hD : {a | π a ≠ a} ⊆ (D : Set α) := by
    intro x hx
    by_contra h
    exact hx (mem_permsOn.mp hπ x (fun hr => h (hRD hr)))
  simp_rw [mul_assoc, Equiv.mul_swap_eq_swap_mul π]
  have hinner (i : α) :
      (∑ j ∈ D, f (σ * (Equiv.swap i (π j) * π))) =
        ∑ j ∈ D, f (σ * (Equiv.swap i j * π)) :=
    π.sum_comp D (fun j => f (σ * (Equiv.swap i j * π))) hD
  simp_rw [hinner]
  exact (π.sum_comp D (fun i => ∑ j ∈ D, f (σ * (Equiv.swap i j * π))) hD).symm

/-- Symmetrisers on disjoint sets of positions commute. -/
theorem symSum_comm_of_disjoint {B R : Finset α} (h : Disjoint B R) (f : Equiv.Perm α → M) :
    symSum B (symSum R f) = symSum R (symSum B f) := by
  funext σ
  change (∑ π ∈ permsOn B, ∑ ρ ∈ permsOn R, f (σ * π * ρ)) =
    ∑ ρ ∈ permsOn R, ∑ π ∈ permsOn B, f (σ * ρ * π)
  rw [sum_comm]
  apply sum_congr rfl; intro ρ hρ
  apply sum_congr rfl; intro π hπ
  have hd : π.Disjoint ρ := by
    intro x
    by_cases hx : x ∈ B
    · exact Or.inr (mem_permsOn.mp hρ x (disjoint_left.mp h hx))
    · exact Or.inl (mem_permsOn.mp hπ x hx)
  rw [mul_assoc, hd.commute.eq, ← mul_assoc]

/-- Symmetrising on no letters leaves a function unchanged. -/
@[simp] theorem symSum_empty (f : Equiv.Perm α → M) : symSum ∅ f = f := by
  funext σ
  rw [symSum_eq_sum_agree]
  have hh : univ.filter (fun τ : Equiv.Perm α => ∀ x ∉ (∅ : Finset α), τ x = σ x) = {σ} := by
    ext τ
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun he => Equiv.ext fun x => he x (notMem_empty x), fun h _ _ => h ▸ rfl⟩
  rw [hh, sum_singleton]

/-- A singleton also has trivial permutation group. -/
@[simp] theorem symSum_singleton (a : α) (f : Equiv.Perm α → M) : symSum {a} f = f := by
  funext σ
  simpa using symSum_insert (R := ∅) f σ (notMem_empty a)

end Definitions

section Eigenvalues

variable {D R : Finset α} {f : Equiv.Perm α → ℝ} {μ : ℝ}

/-- Deleting a maximally symmetrised block gives an exact smaller eigenproblem. -/
theorem transSum_sdiff_eigen (hRD : R ⊆ D) (he : transSum D f = μ • f)
    (h0 : ∀ a ∈ D \ R, symSum (insert a R) f = 0) :
    transSum (D \ R) (symSum R f) =
      (μ - (R.card : ℝ) ^ 2 + 2 * ((D \ R).card : ℝ)) • symSum R f := by
  classical
  funext σ
  let g := symSum R f
  let J := D \ R
  have he' : transSum D g σ = μ * g σ := by
    rw [show g = symSum R f from rfl, transSum_symSum_comm hRD, he]
    simp [symSum, Pi.smul_apply, ← mul_sum]
  have hcross (a : α) (ha : a ∈ J) : (∑ i ∈ R, g (σ * Equiv.swap i a)) = -g σ := by
    have h := symSum_insert f σ (mem_sdiff.mp ha).2
    rw [h0 a ha, Pi.zero_apply] at h
    change 0 = g σ + _ at h
    linarith
  have hJJ : ∑ a ∈ J, ∑ i ∈ R, g (σ * Equiv.swap a i) = -(J.card : ℝ) * g σ := by
    calc _ = ∑ a ∈ J, -g σ := by
                apply sum_congr rfl; intro a ha
                simpa only [Equiv.swap_comm a] using hcross a ha
         _ = _ := by simp [nsmul_eq_mul]
  have hRJ : ∑ i ∈ R, ∑ a ∈ J, g (σ * Equiv.swap i a) = -(J.card : ℝ) * g σ := by
    rw [sum_comm]
    calc _ = ∑ a ∈ J, -g σ := sum_congr rfl hcross
         _ = _ := by simp [nsmul_eq_mul]
  have hRR : ∑ i ∈ R, ∑ j ∈ R, g (σ * Equiv.swap i j) = (R.card : ℝ)^2 * g σ := by
    calc _ = ∑ i ∈ R, ∑ j ∈ R, g σ := by
                apply sum_congr rfl; intro i hi; apply sum_congr rfl; intro j hj
                exact symSum_mul_swap f σ hi hj
         _ = _ := by simp [nsmul_eq_mul, sq, mul_assoc]
  have hsplit (v : α → ℝ) : (∑ i ∈ D, v i) = (∑ i ∈ J, v i) + ∑ i ∈ R, v i :=
    (sum_sdiff hRD).symm
  unfold transSum at he'
  rw [hsplit] at he'
  simp_rw [hsplit (fun j => g (σ * Equiv.swap _ j))] at he'
  simp only [sum_add_distrib, hJJ, hRJ, hRR] at he'
  change (∑ i ∈ J, ∑ j ∈ J, g (σ * Equiv.swap i j)) = (μ - _ ^ 2 + 2 * _) * g σ
  linarith

private theorem exists_max_sym (D : Finset α) {f : Equiv.Perm α → ℝ} (hf : f ≠ 0) :
    ∃ R ⊆ D, symSum R f ≠ 0 ∧ ∀ B ⊆ D, symSum B f ≠ 0 → B.card ≤ R.card := by
  classical
  let S := D.powerset.filter fun R => symSum R f ≠ 0
  have hS : (∅ : Finset α) ∈ S := by simp [S, hf]
  obtain ⟨R, hR, h⟩ := exists_max_image S card ⟨∅, hS⟩
  simp only [S, mem_filter, mem_powerset] at hR h
  exact ⟨R, hR.1, hR.2, fun B hBD hB => h B ⟨hBD, hB⟩⟩

/-- A cap on surviving symmetrisers bounds the transposition eigenvalue. -/
theorem eigenvalue_le_card_mul (D : Finset α) {f : Equiv.Perm α → ℝ} {μ : ℝ} (t : ℕ)
    (hf : f ≠ 0) (he : transSum D f = μ • f)
    (hcap : ∀ B ⊆ D, t < B.card → symSum B f = 0) : μ ≤ (D.card : ℝ) * t := by
  classical
  induction D using strongInductionOn generalizing f μ t with
  | _ D ih =>
    obtain hd | hd := D.eq_empty_or_nonempty
    · subst D
      have hz : μ • f = 0 := by rw [← he]; funext σ; simp [transSum]
      have hμ : μ = 0 := by
        by_contra hμ
        apply hf
        funext σ
        exact (mul_eq_zero.mp (congrFun hz σ : μ * f σ = 0)).resolve_left hμ
      simp [hμ]
    obtain ⟨R, hRD, hg, hmax⟩ := exists_max_sym D hf
    obtain ⟨a, ha⟩ := hd
    have hRa : 0 < R.card := by
      have hp := hmax {a} (singleton_subset_iff.mpr ha) (by simpa using hf)
      rw [card_singleton] at hp
      omega
    have hzero (b : α) (hb : b ∈ D \ R) : symSum (insert b R) f = 0 := by
      by_contra hz
      have h := hmax (insert b R) (insert_subset (mem_sdiff.mp hb).1 hRD) hz
      rw [card_insert_of_notMem (mem_sdiff.mp hb).2] at h
      omega
    have hb := ih (D \ R) (sdiff_ssubset hRD (card_pos.mp hRa)) R.card hg
      (transSum_sdiff_eigen hRD he hzero) (fun B hB hcard => by
        rw [symSum_comm_of_disjoint (Finset.sdiff_disjoint.mono_left hB)]
        have hBF : symSum B f = 0 := by
          by_contra hh
          exact (Nat.not_le_of_gt hcard) (hmax B (hB.trans sdiff_subset) hh)
        rw [hBF]; funext σ; simp [symSum])
    have ht : R.card ≤ t := le_of_not_gt fun h => hg (hcap R hRD h)
    have hc : ((D \ R).card : ℝ) + R.card = D.card := by
      exact_mod_cast card_sdiff_add_card_eq_card hRD
    calc μ ≤ (D.card : ℝ) * R.card := by
           rw [← hc]; nlinarith [show (0 : ℝ) ≤ (D \ R).card by positivity]
         _ ≤ _ := by gcongr

/-- Both estimates at a fixed maximal surviving block. -/
theorem level_bounds (hRD : R ⊆ D) (he : transSum D f = μ • f) (hg : symSum R f ≠ 0)
    (hmax : ∀ B ⊆ D, symSum B f ≠ 0 → B.card ≤ R.card) :
    μ ≤ (D.card : ℝ) * R.card ∧
      μ ≤ (R.card : ℝ)^2 + ((D.card : ℝ) - R.card)^2 - 2 * ((D.card : ℝ) - R.card) := by
  classical
  have h0 (B : Finset α) (hBD : B ⊆ D) (hlt : R.card < B.card) : symSum B f = 0 := by
    by_contra h
    exact (Nat.not_le_of_gt hlt) (hmax B hBD h)
  have hf : f ≠ 0 := by
    rintro rfl
    apply hg
    funext σ; simp [symSum]
  refine ⟨eigenvalue_le_card_mul D R.card hf he h0, ?_⟩
  have hi (a : α) (ha : a ∈ D \ R) : symSum (insert a R) f = 0 := by
    apply h0 _ (insert_subset (mem_sdiff.mp ha).1 hRD)
    simp [card_insert_of_notMem (mem_sdiff.mp ha).2]
  have hb := eigenvalue_le_card_mul (D \ R) (D \ R).card hg (transSum_sdiff_eigen hRD he hi)
    (fun B hB hlt => ((Nat.not_lt_of_ge (card_le_card hB)) hlt).elim)
  have hc : ((D \ R).card : ℝ) + R.card = D.card := by
    exact_mod_cast card_sdiff_add_card_eq_card hRD
  rw [← hc]
  nlinarith

/-- Every eigenfunction has a common surviving block witnessing both bounds. -/
theorem exists_level_bounds (D : Finset α) {f : Equiv.Perm α → ℝ} {μ : ℝ} (hf : f ≠ 0)
    (he : transSum D f = μ • f) :
    ∃ R ⊆ D, symSum R f ≠ 0 ∧ μ ≤ (D.card : ℝ) * R.card ∧
      μ ≤ (R.card : ℝ)^2 + ((D.card : ℝ) - R.card)^2 - 2 * ((D.card : ℝ) - R.card) := by
  obtain ⟨R, hRD, hg, hmax⟩ := exists_max_sym D hf
  exact ⟨R, hRD, hg, level_bounds hRD he hg hmax⟩

/-- The level bounds for the full, unnormalised random transposition operator. -/
theorem exists_level_bounds_univ {f : Equiv.Perm α → ℝ} {μ : ℝ} (hf : f ≠ 0)
    (he : transSum univ f = μ • f) :
    ∃ R ⊆ (univ : Finset α), symSum R f ≠ 0 ∧ μ ≤ (Fintype.card α : ℝ) * R.card ∧
      μ ≤ (R.card : ℝ)^2 + ((Fintype.card α : ℝ) - R.card)^2 -
        2 * ((Fintype.card α : ℝ) - R.card) := by
  simpa only [card_univ] using exists_level_bounds univ hf he

end Eigenvalues

end MathlibExt.Probability.RandomTranspositionFiltration
