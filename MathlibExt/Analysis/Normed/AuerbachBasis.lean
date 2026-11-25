/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Normed.Operator.Basic

@[expose] public section

namespace MathlibExt.Analysis.Normed.AuerbachBasis

/-!
# Auerbach bases

Let 𝕜 be a real or complex RCLike field and E a nontrivial finite-dimensional
normed 𝕜-space. There are a basis indexed by Fin(finrank 𝕜 E) and
biorthogonal continuous linear functionals such that every basis vector
and every functional has norm one.

Source: H. Auerbach, doctoral thesis, University of Lwów (1930).
-/

/-- Let 𝕜 be an RCLike field and E a nontrivial finite-dimensional normed
𝕜-vector space. There exist a basis b indexed by Fin(finrank 𝕜 E) and
continuous 𝕜-linear functionals φ_i : E → 𝕜 with ‖b_i‖ = ‖φ_i‖ = 1
for every i and φ_i(b_j) = 1 when i = j, and 0 otherwise. -/
theorem auerbachBasis
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [Nontrivial E] :
    ∃ (b : Module.Basis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
      (φ : Fin (Module.finrank 𝕜 E) → E →L[𝕜] 𝕜),
      (∀ i, ‖b i‖ = 1) ∧
        (∀ i, ‖φ i‖ = 1) ∧
          (∀ i j, φ i (b j) = if i = j then 1 else 0) := by
  classical
  set n : ℕ := Module.finrank 𝕜 E with hn
  set b₀ : Module.Basis (Fin n) 𝕜 E := Module.finBasis 𝕜 E with hb₀
  have hpos_of_ne : ∀ x : E, x ≠ 0 → 0 < ‖x‖ := fun x hx =>
    lt_of_le_of_ne (norm_nonneg _) (fun h0 => hx (norm_eq_zero.mp h0.symm))
  have hofReal_inv : ∀ r : ℝ, 0 ≤ r → ‖((r⁻¹ : ℝ) : 𝕜)‖ = r⁻¹ := fun r hr => by
    rw [RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr hr)]
  have hscale : ∀ Y X : ℝ, 1 < Y → 0 < X → X < Y * X := fun Y X hY hX =>
    calc X = 1 * X := (one_mul _).symm
      _ < Y * X := mul_lt_mul_of_pos_right hY hX
  -- The determinant is continuous.
  have hdet : Continuous (fun m : Fin n → E => (b₀.toMatrix m).det) := by
    exact b₀.continuous_toMatrix.matrix_det
  set Φ : (Fin n → E) → ℝ := fun m => ‖(b₀.toMatrix m).det‖ with hΦ
  set S : Set (Fin n → E) := {x | ∀ i, x i ∈ Metric.closedBall (0 : E) 1} with hS
  have hΦcont : Continuous Φ := by
    change Continuous fun m => ‖(b₀.toMatrix m).det‖
    exact continuous_norm.comp hdet
  have hproper : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  have hScompact : IsCompact S := by
    change IsCompact {x : Fin n → E | ∀ i, x i ∈ Metric.closedBall (0 : E) 1}
    exact isCompact_pi_infinite (s := fun _ => Metric.closedBall (0 : E) 1)
      (fun i => @isCompact_closedBall _ _ hproper _ _)
  -- Normalizing scalars for the reference basis.
  have hb₀ne : ∀ j, b₀ j ≠ 0 := fun j => b₀.ne_zero j
  have hnorm_ne : ∀ j, ‖b₀ j‖ ≠ 0 := fun j => norm_ne_zero_iff.mpr (hb₀ne j)
  set c : Fin n → 𝕜 := fun j => ((‖b₀ j‖⁻¹ : ℝ) : 𝕜) with hc
  have hc_ne : ∀ j, c j ≠ 0 := fun j =>
    RCLike.ofReal_eq_zero.not.mpr (inv_ne_zero (hnorm_ne j))
  have hcj : ∀ j, ‖c j‖ = ‖b₀ j‖⁻¹ := fun j => hofReal_inv _ (norm_nonneg _)
  -- Witness: normalized reference basis, in the domain.
  set w : Fin n → E := fun j => c j • b₀ j with hw
  have hw_mem : w ∈ S := by
    intro j
    change c j • b₀ j ∈ Metric.closedBall (0 : E) 1
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hcj j,
      inv_mul_cancel₀ (hnorm_ne j)]
  -- Its coordinate matrix is diagonal with nonzero entries.
  have hMw : b₀.toMatrix w = Matrix.diagonal c := by
    funext a b'
    rw [Module.Basis.toMatrix_apply]
    change b₀.repr (c b' • b₀ b') a = Matrix.diagonal c a b'
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self_apply,
      Matrix.diagonal_apply]
    by_cases h : a = b'
    · subst h; simp
    · have h' : b' ≠ a := Ne.symm h
      simp [h, h']
  have hdetw : (b₀.toMatrix w).det ≠ 0 := by
    rw [hMw, Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    exact fun i _ => hc_ne i
  -- Maximizer of |det| over the compact domain.
  obtain ⟨mstar, hmstar_mem, hmax⟩ :=
    hScompact.exists_isMaxOn ⟨w, hw_mem⟩ hΦcont.continuousOn
  have hle : ∀ y ∈ S, Φ y ≤ Φ mstar := isMaxOn_iff.mp hmax
  have hΦw_pos : 0 < Φ w := norm_pos_iff.mpr hdetw
  have hdet_star : (b₀.toMatrix mstar).det ≠ 0 := by
    intro h0
    have hle0 : Φ mstar ≤ 0 := by
      change ‖(b₀.toMatrix mstar).det‖ ≤ 0
      rw [h0, norm_zero]
    exact not_lt_of_ge hle0 (lt_of_lt_of_le hΦw_pos (hle w hw_mem))
  have hmem_star : ∀ j, mstar j ∈ Metric.closedBall (0 : E) 1 := hmstar_mem
  have hnorm_le : ∀ j, ‖mstar j‖ ≤ 1 := by
    intro j
    have h := hmem_star j
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h
  have hm'_gen : ∀ (j : Fin n) (v : E),
      v ∈ Metric.closedBall (0 : E) 1 → Function.update mstar j v ∈ S := by
    intro j v hv i
    by_cases hi : i = j
    · subst hi
      rw [Function.update_self]
      exact hv
    · rw [Function.update_of_ne hi]
      exact hmem_star i
  -- Replacing column j by the new matrix's own column j recovers the matrix.
  have hupd_gen : ∀ (j : Fin n) (m' : Fin n → E) (v : E),
      m' = Function.update mstar j v →
      Matrix.updateCol (b₀.toMatrix mstar) j
        (fun k => b₀.toMatrix m' k j) = b₀.toMatrix m' := by
    intro j m' v hm'
    funext a b'
    rw [Matrix.updateCol_apply]
    by_cases hb : b' = j
    · subst hb
      rw [ite_eq_left rfl]
    · rw [ite_eq_right hb, Module.Basis.toMatrix_apply, Module.Basis.toMatrix_apply, hm',
        Function.update_of_ne hb]
  -- Every maximizer vector has norm exactly one, by a scale-up argument.
  have hnorm_eq : ∀ j, ‖mstar j‖ = 1 := by
    intro j
    by_contra hne
    have hlt : ‖mstar j‖ < 1 := lt_of_le_of_ne (hnorm_le j) hne
    have hjne : mstar j ≠ 0 := by
      intro h0
      apply hdet_star
      have hcol0 : (fun k => b₀.toMatrix mstar k j)
          = fun k => ∑ i, ((0 : Fin n → 𝕜) i) • b₀.toMatrix mstar k i := by
        funext k
        simp [h0, Module.Basis.toMatrix_apply]
      have hsum := Matrix.det_updateCol_sum (b₀.toMatrix mstar) j (0 : Fin n → 𝕜)
      rw [← hcol0] at hsum
      have hupd_self : mstar = Function.update mstar j (mstar j) := by
        funext i
        by_cases hi : i = j
        · subst hi; rw [Function.update_self]
        · rw [Function.update_of_ne hi]
      have hself : Matrix.updateCol (b₀.toMatrix mstar) j
          (fun k => b₀.toMatrix mstar k j) = b₀.toMatrix mstar :=
        hupd_gen j mstar (mstar j) hupd_self
      rw [hself] at hsum
      simpa using hsum
    have hr_pos : 0 < ‖mstar j‖ := hpos_of_ne _ hjne
    set s : 𝕜 := ((‖mstar j‖⁻¹ : ℝ) : 𝕜) with hs
    have hs_norm : ‖s‖ = ‖mstar j‖⁻¹ := hofReal_inv _ hr_pos.le
    have hs_gt : 1 < ‖s‖ := by
      rw [hs_norm]
      exact one_lt_inv_iff₀.mpr ⟨hr_pos, hlt⟩
    set y : E := s • mstar j with hy
    have hy_norm : ‖y‖ = 1 := by
      rw [hy, norm_smul, hs_norm, inv_mul_cancel₀ (ne_of_gt hr_pos)]
    set m' : Fin n → E := Function.update mstar j y with hm'
    have hm'_mem : m' ∈ S := hm'_gen j y (by
      rw [Metric.mem_closedBall, dist_zero_right, hy_norm])
    set c1 : Fin n → 𝕜 := fun i => if i = j then s else 0 with hc1
    have hcol1 : (fun k => b₀.toMatrix m' k j)
        = fun k => ∑ i, (c1 i) • b₀.toMatrix mstar k i := by
      funext k
      show b₀.toMatrix m' k j = ∑ i, (c1 i) • b₀.toMatrix mstar k i
      have hL : b₀.toMatrix m' k j = s • b₀.toMatrix mstar k j := by
        rw [Module.Basis.toMatrix_apply, hm', Function.update_self,
          Module.Basis.toMatrix_apply]
        change b₀.repr (s • mstar j) k = s • b₀.repr (mstar j) k
        rw [map_smul, Finsupp.smul_apply]
      rw [hL]
      have hsum1 : (∑ i, (c1 i) • b₀.toMatrix mstar k i)
          = s • b₀.toMatrix mstar k j := by
        rw [Finset.sum_eq_single j (fun b _ hb => by
            simp only [hc1, ite_eq_right hb, zero_smul]) (fun habs => by
            exact absurd (Finset.mem_univ j) habs)]
        simp only [hc1, ite_eq_left rfl]
      rw [hsum1]
    have hdet1 : (b₀.toMatrix m').det = s * (b₀.toMatrix mstar).det := by
      have hsum := Matrix.det_updateCol_sum (b₀.toMatrix mstar) j c1
      rw [show (fun k => ∑ i, (c1 i) • b₀.toMatrix mstar k i)
        = (fun k => b₀.toMatrix m' k j) from hcol1.symm] at hsum
      rw [hupd_gen j m' y hm'] at hsum
      simpa [hc1] using hsum
    have hle1 : Φ m' ≤ Φ mstar := hle m' hm'_mem
    have hgt1 : Φ mstar < Φ m' := by
      change ‖(b₀.toMatrix mstar).det‖ < ‖(b₀.toMatrix m').det‖
      rw [hdet1, norm_mul, hs_norm]
      have hpos : 0 < ‖(b₀.toMatrix mstar).det‖ := norm_pos_iff.mpr hdet_star
      exact hscale _ _ (by rw [← hs_norm]; exact hs_gt) hpos
    exact not_lt_of_ge hle1 hgt1
  -- The maximizer is linearly independent: transfer from its columns.
  have hLIcols : LinearIndependent 𝕜 (b₀.toMatrix mstar).col :=
    Matrix.linearIndependent_cols_of_det_ne_zero hdet_star
  have hcol_eq : (b₀.toMatrix mstar).col
      = b₀.equivFun.toLinearMap ∘ mstar := by
    funext j i
    change b₀.toMatrix mstar i j = b₀.equivFun (mstar j) i
    rw [Module.Basis.toMatrix_apply, Module.Basis.equivFun_apply]
  have hLI : LinearIndependent 𝕜 mstar := by
    rw [hcol_eq] at hLIcols
    exact LinearIndependent.of_comp _ hLIcols
  have hcard : Fintype.card (Fin n) = Module.finrank 𝕜 E := by
    rw [Fintype.card_fin]
  set b : Module.Basis (Fin n) 𝕜 E :=
    basisOfLinearIndependentOfCardEqFinrank' mstar hLI hcard with hb
  have hb_apply : ∀ j, b j = mstar j := by
    intro j
    simp [hb]
  -- Biorthogonal functionals: coordinates in the maximizer basis.
  set φ : Fin n → E →L[𝕜] 𝕜 := fun i =>
    ⟨(Finsupp.lapply i).comp b.repr.toLinearMap,
      LinearMap.continuous_of_finiteDimensional _⟩ with hφ
  have hφ_apply : ∀ i x, φ i x = (b.repr x) i := fun i x => rfl
  have hkron : ∀ i j, φ i (b j) = if i = j then 1 else 0 := by
    intro i j
    rw [hφ_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : i = j
    · subst h; rfl
    · have h' : j ≠ i := Ne.symm h
      rw [ite_eq_right h, ite_eq_right h']
  have hb_norm : ∀ i, ‖b i‖ = 1 := fun i => by rw [hb_apply i]; exact hnorm_eq i
  -- Dual norms are ≤ 1: else Cramer's rule gives a strictly better update.
  have hφ_le : ∀ j, ‖φ j‖ ≤ 1 := by
    intro j
    by_contra hgt
    push Not at hgt
    obtain ⟨x, hx_norm, hx_gt⟩ := (φ j).exists_lt_apply_of_lt_opNorm hgt
    have hx_mem : x ∈ Metric.closedBall (0 : E) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hx_norm.le
    set m' : Fin n → E := Function.update mstar j x with hm'
    have hm'_mem : m' ∈ S := hm'_gen j x hx_mem
    have hφx : (b.repr x) j = φ j x := (hφ_apply j x).symm
    have hcoord_gt : 1 < ‖(b.repr x) j‖ := by rw [hφx]; exact hx_gt
    set c2 : Fin n → 𝕜 := fun i => (b.repr x) i with hc2
    have hcol2 : (fun k => b₀.toMatrix m' k j)
        = fun k => ∑ i, (c2 i) • b₀.toMatrix mstar k i := by
      funext k
      show b₀.toMatrix m' k j = ∑ i, (c2 i) • b₀.toMatrix mstar k i
      have hexpand : x = Finsupp.linearCombination 𝕜 (⇑b) (b.repr x) :=
        (b.linearCombination_repr x).symm
      have hL : b₀.toMatrix m' k j = b₀.repr x k := by
        rw [Module.Basis.toMatrix_apply, hm', Function.update_self]
      rw [hL]
      conv_lhs => rw [hexpand, Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ (Finset.subset_univ _)
          (fun i a => a • b i) (fun i _ => zero_smul _ _), map_sum,
        Finsupp.finsetSum_apply]
      apply Finset.sum_congr rfl
      intro i _
      change b₀.repr (((b.repr x) i) • b i) k
        = (c2 i) • b₀.toMatrix mstar k i
      rw [map_smul, Finsupp.smul_apply, hb_apply, Module.Basis.toMatrix_apply]
    have hdet2 : (b₀.toMatrix m').det
        = (b.repr x) j * (b₀.toMatrix mstar).det := by
      have hsum := Matrix.det_updateCol_sum (b₀.toMatrix mstar) j c2
      rw [show (fun k => ∑ i, (c2 i) • b₀.toMatrix mstar k i)
        = (fun k => b₀.toMatrix m' k j) from hcol2.symm] at hsum
      rw [hupd_gen j m' x hm'] at hsum
      rw [smul_eq_mul] at hsum
      exact hsum
    have hle2 : Φ m' ≤ Φ mstar := hle m' hm'_mem
    have hgt2 : Φ mstar < Φ m' := by
      change ‖(b₀.toMatrix mstar).det‖ < ‖(b₀.toMatrix m').det‖
      rw [hdet2, norm_mul]
      have hpos : 0 < ‖(b₀.toMatrix mstar).det‖ := norm_pos_iff.mpr hdet_star
      exact hscale _ _ hcoord_gt hpos
    exact not_lt_of_ge hle2 hgt2
  have hφ_eq : ∀ i, ‖φ i‖ = 1 := by
    intro i
    apply le_antisymm (hφ_le i)
    have h1 : φ i (b i) = 1 := by rw [hkron i i, ite_eq_left rfl]
    have h2 : ‖φ i (b i)‖ ≤ ‖φ i‖ * ‖b i‖ := ContinuousLinearMap.le_opNorm _ _
    rw [h1, hb_norm i, mul_one, norm_one] at h2
    exact h2
  exact ⟨b, φ, hb_norm, hφ_eq, hkron⟩

end MathlibExt.Analysis.Normed.AuerbachBasis
