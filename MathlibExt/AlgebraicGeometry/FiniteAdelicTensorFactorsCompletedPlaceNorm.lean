/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FiniteAdelicTensorFactors

import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Completed place norm from isometric residue realizations

For a finite extension `E/K` and a factorization `D` of the tensor algebra over a field `F`,
the base-changed determinant norm equals the length-weighted product of local norms
(`tensorNorm`). When `F` is a complete normed field with isometric residue realizations, the norm
of the base-changed field norm equals the length-and-rank product of completion norms
(`completedPlaceNorm`).

Source: Yuan--Zhang, arXiv:2105.13587v9, Sections 3.4 and 5.3.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.FiniteAdelicTensorFactors

open MathlibExt.AlgebraicGeometry.FiniteAdelicTensorFactors
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private theorem det_smul_simple (F A M : Type) [Field F] [CommRing A] [IsLocalRing A]
    [Algebra F A] [AddCommGroup M] [Module A M] [Module F M] [IsScalarTower F A M]
    [IsSimpleModule A M] (a : A) :
    (Algebra.lsmul F F M a).det = Algebra.norm F (IsLocalRing.residue A a) := by
  obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
    (inferInstance : IsSimpleModule A M)
  obtain rfl := IsLocalRing.eq_maximalIdeal hm
  let eResid : M ≃ₗ[A] IsLocalRing.ResidueField A := e
  let eF := eResid.restrictScalars F
  have he : eF.toLinearMap ∘ₗ Algebra.lsmul F F M a ∘ₗ eF.symm.toLinearMap =
      Algebra.lmul F (IsLocalRing.ResidueField A) (IsLocalRing.residue A a) := by
    apply LinearMap.ext
    intro y
    change eResid (a • eResid.symm y) = IsLocalRing.residue A a * y
    rw [eResid.map_smul, eResid.apply_symm_apply]
    rfl
  rw [Algebra.norm_apply, ← he]
  exact (LinearMap.det_conj _ eF).symm

private theorem det_smul_step (F A M : Type) [Field F] [CommRing A] [IsLocalRing A]
    [Algebra F A] [AddCommGroup M] [Module A M] [Module F M] [IsScalarTower F A M]
    [FiniteDimensional F M] (a : A) (p q : Submodule A M) (h : p ⋖ q) :
    (Algebra.lsmul F F q a).det =
      (Algebra.lsmul F F p a).det * Algebra.norm F (IsLocalRing.residue A a) := by
  let f : p →ₗ[A] q := Submodule.inclusion h.le
  let W : Submodule F q := f.range.restrictScalars F
  have hsimple : IsSimpleModule A (q ⧸ f.range) := by
    rwa [Submodule.range_inclusion, ← covBy_iff_quot_is_simple h.le]
  let := hsimple
  have : FiniteDimensional F q := inferInstanceAs (FiniteDimensional F (q.restrictScalars F))
  let eP : p ≃ₗ[F] W :=
    (LinearEquiv.ofInjective f (Submodule.inclusion_injective _)).restrictScalars F
  have hs : W ≤ W.comap (Algebra.lsmul F F q a) := by
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    exact ⟨a • z, f.map_smul a z⟩
  have hp : eP.toLinearMap ∘ₗ Algebra.lsmul F F p a ∘ₗ eP.symm.toLinearMap =
      (Algebra.lsmul F F q a).restrict hs := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    change f (a • eP.symm y) = a • (y : q)
    rw [f.map_smul]
    congr 1
    exact congrArg Subtype.val (eP.apply_symm_apply y)
  rw [LinearMap.det_eq_det_mul_det W _ hs, ← hp, LinearMap.det_conj]
  congr 1
  have hq : W.mapQ W (Algebra.lsmul F F q a) hs = Algebra.lsmul F F (q ⧸ f.range) a := by
    apply LinearMap.ext
    intro y
    induction y using Submodule.Quotient.induction_on with
    | _ y => rfl
  rw [hq]
  exact det_smul_simple F A (q ⧸ f.range) a

private theorem local_norm (F A : Type) [Field F] [CommRing A] [IsLocalRing A]
    [IsArtinianRing A] [IsNoetherianRing A] [Algebra F A] [FiniteDimensional F A] (a : A) :
    Algebra.norm F a = Algebra.norm F (IsLocalRing.residue A a) ^
      (Module.length A A).toNat := by
  classical
  have hfinite : IsFiniteLength A A :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  obtain ⟨s, hbot, htop⟩ := isFiniteLength_iff_exists_compositionSeries.mp hfinite
  have h (k : Fin (s.length + 1)) :
      (Algebra.lsmul F F (s k) a).det = Algebra.norm F (IsLocalRing.residue A a) ^ (k : ℕ) := by
    induction k using Fin.induction with
    | zero =>
      change (Algebra.lsmul F F s.head a).det = _
      rw [hbot]
      simp only [LinearMap.det_eq_one_of_subsingleton, Fin.val_zero, pow_zero]
    | succ i hi =>
      simpa [hi, pow_succ] using
        det_smul_step F A A a (s i.castSucc) (s i.succ) (s.step i)
  have hlen : (Module.length A A).toNat = s.length := by
    rw [← Module.length_compositionSeries s hbot htop]
    rfl
  have ht := h (Fin.last s.length)
  change (Algebra.lsmul F F s.last a).det =
    Algebra.norm F (IsLocalRing.residue A a) ^ s.length at ht
  rw [htop] at ht
  let e := (Submodule.topEquiv : (⊤ : Submodule A A) ≃ₗ[A] A).restrictScalars F
  have he : e.toLinearMap ∘ₗ Algebra.lsmul F F (⊤ : Submodule A A) a ∘ₗ e.symm.toLinearMap =
      Algebra.lmul F A a := by
    ext y
    rfl
  rw [hlen, Algebra.norm_apply, ← he, LinearMap.det_conj]
  exact ht

private theorem det_pi_dependent (F : Type) [Field F] : ∀ {ι : Type} [Fintype ι]
    (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module F (M i)]
    [∀ i, FiniteDimensional F (M i)] (f : ∀ i, Module.End F (M i)),
    (LinearMap.pi fun i ↦ f i ∘ₗ LinearMap.proj i).det = ∏ i, (f i).det := by
  apply Fintype.induction_empty_option
  · intro α β _ e IH M _ _ _ f
    let : Fintype α := Fintype.ofEquiv β e.symm
    let eL := LinearEquiv.piCongrLeft' F M e.symm
    let g : ∀ i, Module.End F (M (e i)) := fun i ↦ f (e i)
    have he : eL.toLinearMap ∘ₗ (LinearMap.pi fun j ↦ f j ∘ₗ LinearMap.proj j) ∘ₗ
        eL.symm.toLinearMap = LinearMap.pi fun i ↦ g i ∘ₗ LinearMap.proj i := by
      ext x j
      change f (e j) ((eL (eL.symm x)) j) = f (e j) (x j)
      rw [eL.apply_symm_apply]
    rw [← LinearMap.det_conj _ eL, he, IH]
    exact Fintype.prod_equiv e _ _ (fun i ↦ rfl)
  · intro M _ _ _ f
    simp [LinearMap.det_eq_one_of_subsingleton]
  · intro ι _ IH M _ _ _ f
    let eL := LinearEquiv.piOptionEquivProd F (M := M)
    have he : eL.toLinearMap ∘ₗ (LinearMap.pi fun i ↦ f i ∘ₗ LinearMap.proj i) ∘ₗ
        eL.symm.toLinearMap = (f none).prodMap
          (LinearMap.pi fun i ↦ f (some i) ∘ₗ LinearMap.proj i) := by
      ext x i <;> rfl
    rw [← LinearMap.det_conj _ eL, he, LinearMap.det_prodMap, IH, Fintype.prod_option]

private theorem le_of_power_bound (u v C : ℝ) (hv : 0 ≤ v)
    (h : ∀ n : ℕ, u ^ n ≤ C * v ^ n) : u ≤ v := by
  by_contra! huv
  by_cases hv0 : v = 0
  · have h1 := h 1
    simp only [pow_one, hv0, mul_zero] at h1
    exact (not_lt_of_ge h1) (hv0 ▸ huv)
  have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
  have hratio : 1 < u / v := (one_lt_div hvpos).mpr huv
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hratio
  have hle : (u / v) ^ n ≤ C := by
    rw [div_pow, div_le_iff₀ (pow_pos hvpos n)]
    exact h n
  exact (not_lt_of_ge hle) hn

private theorem norm_bound (F L : Type) [NontriviallyNormedField F] [CompleteSpace F]
    [NormedField L] [NormedAlgebra F L] [FiniteDimensional F L] :
    ∃ C : ℝ, 0 < C ∧ ∀ x : L, ‖Algebra.norm F x‖ ≤ C * ‖x‖ ^ Module.finrank F L := by
  classical
  let b := Module.finBasis F L
  let e := b.equivFunL
  let C₀ := max 1 ‖e.toContinuousLinearMap‖
  let B₀ := max 1 (∑ j, ‖b j‖)
  have hC : 0 < C₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hB : 0 < B₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hb (j : Fin (Module.finrank F L)) : ‖b j‖ ≤ B₀ :=
    (Finset.single_le_sum (fun k _ ↦ norm_nonneg (b k)) (Finset.mem_univ j)).trans
      (le_max_right _ _)
  have hentry (x : L) (i j : Fin (Module.finrank F L)) :
      ‖Algebra.leftMulMatrix b x i j‖ ≤ C₀ * B₀ * ‖x‖ := by
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    change ‖e (x * b j) i‖ ≤ C₀ * B₀ * ‖x‖
    calc
      ‖e (x * b j) i‖ ≤ ‖e (x * b j)‖ := norm_le_pi_norm _ i
      _ ≤ ‖e.toContinuousLinearMap‖ * ‖x * b j‖ :=
        e.toContinuousLinearMap.le_opNorm _
      _ = ‖e.toContinuousLinearMap‖ * (‖x‖ * ‖b j‖) := by rw [norm_mul]
      _ ≤ C₀ * (‖x‖ * B₀) :=
        mul_le_mul (le_max_right _ _) (mul_le_mul_of_nonneg_left (hb j) (norm_nonneg x))
          (mul_nonneg (norm_nonneg x) (norm_nonneg _)) hC.le
      _ = C₀ * B₀ * ‖x‖ := by ring
  refine ⟨(Module.finrank F L).factorial * (C₀ * B₀) ^ Module.finrank F L,
    mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos (mul_pos hC hB) _), ?_⟩
  intro x
  rw [Algebra.norm_eq_matrix_det b]
  simpa only [NormedField.toAbsoluteValue_apply, Fintype.card_fin, nsmul_eq_mul, mul_pow,
    mul_assoc] using
    (Matrix.det_le (abv := NormedField.toAbsoluteValue F) (hentry x))

private theorem norm_extension_nontrivial (F L : Type) [NontriviallyNormedField F]
    [CompleteSpace F] [NormedField L] [NormedAlgebra F L] [FiniteDimensional F L] (x : L) :
    ‖Algebra.norm F x‖ = ‖x‖ ^ Module.finrank F L := by
  obtain ⟨C, _, hC⟩ := norm_bound F L
  have hle (y : L) : ‖Algebra.norm F y‖ ≤ ‖y‖ ^ Module.finrank F L := by
    apply le_of_power_bound _ _ C (pow_nonneg (norm_nonneg _) _)
    intro n
    simpa only [map_pow, norm_pow, ← pow_mul, mul_comm] using hC (y ^ n)
  apply le_antisymm (hle x)
  by_cases hx : x = 0
  · simp [hx, Module.finrank_pos.ne']
  have h := hle x⁻¹
  simp only [Algebra.norm_inv, norm_inv, inv_pow] at h
  exact (inv_le_inv₀ (norm_pos_iff.mpr (Algebra.norm_ne_zero_iff.mpr hx))
    (pow_pos (norm_pos_iff.mpr hx) _)).mp h

private theorem norm_extension_trivial (F L : Type) [NormedField F] [NormedField L]
    [Algebra F L] [FiniteDimensional F L]
    (hscalar : ∀ r : F, ‖algebraMap F L r‖ = ‖r‖)
    (hbase : ∀ r : F, r ≠ 0 → ‖r‖ = 1) (x : L) :
    ‖Algebra.norm F x‖ = ‖x‖ ^ Module.finrank F L := by
  let : NormedAlgebra F L :=
    { norm_smul_le := fun r y ↦ by
        rw [Algebra.smul_def, norm_mul, hscalar] }
  have hbase_le (r : F) : ‖r‖ ≤ 1 := by
    by_cases hr : r = 0
    · simp [hr]
    · exact (hbase r hr).le
  let : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one fun n ↦ by
      rw [← map_natCast (algebraMap F L), hscalar]
      exact hbase_le _
  have hvalue (p : Polynomial F) : spectralValue p ≤ 1 := by
    apply ciSup_le
    intro n
    unfold spectralValueTerms
    split_ifs with hn
    · exact Real.rpow_le_one (norm_nonneg _) (hbase_le _)
        (one_div_nonneg.mpr (sub_nonneg.mpr (Nat.cast_le.mpr hn.le)))
    · exact zero_le_one
  have hle (y : L) : ‖y‖ ≤ 1 := by
    let f := NormedAlgebra.toMulAlgebraNorm F L
    have h := norm_root_le_spectralValue (f := f.toAlgebraNorm) f.isPowMul
      IsUltrametricDist.isNonarchimedean_norm
      (minpoly.monic (Algebra.IsIntegral.isIntegral y)) (minpoly.aeval F y)
    exact h.trans (hvalue (minpoly F y))
  by_cases hx : x = 0
  · simp [hx, Module.finrank_pos.ne']
  have hnorm : ‖x‖ = 1 := by
    apply le_antisymm (hle x)
    have h := hle x⁻¹
    rw [norm_inv, inv_le_one₀ (norm_pos_iff.mpr hx)] at h
    exact h
  rw [hnorm, one_pow, hbase _ (Algebra.norm_ne_zero_iff.mpr hx)]

private theorem norm_extension (F L : Type) [NormedField F] [CompleteSpace F]
    [NormedField L] [Algebra F L] [FiniteDimensional F L]
    (hscalar : ∀ r : F, ‖algebraMap F L r‖ = ‖r‖) (x : L) :
    ‖Algebra.norm F x‖ = ‖x‖ ^ Module.finrank F L := by
  by_cases hnontrivial : ∃ r : F, r ≠ 0 ∧ ‖r‖ ≠ 1
  · let : NontriviallyNormedField F := NontriviallyNormedField.ofNormNeOne hnontrivial
    let : NormedAlgebra F L :=
      { norm_smul_le := fun r y ↦ by
          rw [Algebra.smul_def, norm_mul, hscalar] }
    exact norm_extension_nontrivial F L x
  · simp only [not_exists, not_and, not_not] at hnontrivial
    exact norm_extension_trivial F L hscalar hnontrivial x

private theorem norm_pi (F : Type) [Field F] {ι : Type} [Fintype ι]
    (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)]
    [∀ i, FiniteDimensional F (A i)] (x : ∀ i, A i) :
    Algebra.norm F x = ∏ i, Algebra.norm F (x i) := by
  have hmul : Algebra.lmul F (∀ i, A i) x =
      LinearMap.pi fun i ↦ Algebra.lmul F (A i) (x i) ∘ₗ LinearMap.proj i := by
    ext y i
    rfl
  rw [Algebra.norm_apply, hmul, det_pi_dependent]
  simp only [Algebra.norm_apply]

/-- Determinant norm base change includes every nonreduced local factor. -/
public theorem tensorNorm (K E F : Type) [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [FiniteDimensional K E]
    (D : Factorization K E F) (a : E) :
    algebraMap K F (Algebra.norm K a) = factorNorm D a := by
  have hmul : Algebra.lmul F (F ⊗[K] E) (1 ⊗ₜ[K] a) =
      (Algebra.lmul K E a).baseChange F := by
    ext x
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  let e := Algebra.TensorProduct.commRight K F E
  have hTensor : algebraMap K F (Algebra.norm K a) =
      Algebra.norm F ((Algebra.TensorProduct.includeLeft : E →ₐ[K] CompletedTensor K E F) a) := by
    calc
      algebraMap K F (Algebra.norm K a) = Algebra.norm F (1 ⊗ₜ[K] a : F ⊗[K] E) := by
        rw [Algebra.norm_apply, Algebra.norm_apply, hmul, LinearMap.det_baseChange]
      _ = Algebra.norm F
          ((Algebra.TensorProduct.includeLeft : E →ₐ[K] CompletedTensor K E F) a) :=
        (Algebra.norm_eq_of_algEquiv e (1 ⊗ₜ[K] a)).symm
  rw [hTensor, ← Algebra.norm_eq_of_algEquiv D.decomposition, norm_pi]
  unfold factorNorm
  apply Finset.prod_congr rfl
  intro i _
  exact local_norm F (D.factor i) (factorMap D i a)

/-- Norm of the field norm equals the completion norm to the local rank. -/
private theorem norm_extension_aux (K E F : Type) [Field K] [Field E]
    [NormedField F] [CompleteSpace F] [Algebra K E] [Algebra K F]
    [FiniteDimensional K E] (D : Factorization K E F) (C : CompletionData D)
    (i : D.index) (x : C.completion i) :
    ‖Algebra.norm F x‖ = ‖x‖ ^ completionRank D C i := by
  exact norm_extension F (C.completion i) (C.scalar_isometry i) x

/-- Complete isometric residue realizations give the length-and-rank norm formula. -/
public theorem completedPlaceNorm (K E F : Type) [Field K] [Field E]
    [NormedField F] [CompleteSpace F] [Algebra K E] [Algebra K F]
    [FiniteDimensional K E] (D : Factorization K E F) (C : CompletionData D) (a : E) :
    ‖algebraMap K F (Algebra.norm K a)‖ = completedNorm D C a := by
  have hTensor : algebraMap K F (Algebra.norm K a) = factorNorm D a :=
    tensorNorm K E F D a
  rw [hTensor]
  unfold factorNorm completedNorm completionWeight
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [norm_pow]
  have hInv : Algebra.norm F (completionMap D C i a) =
      Algebra.norm F (residueMap D i a) :=
    Algebra.norm_eq_of_algEquiv (C.comparison i) (residueMap D i a)
  rw [← hInv]
  rw [norm_extension_aux K E F D C i (completionMap D C i a)]
  rw [← pow_mul, mul_comm]

end WantedExt.AlgebraicGeometry.FiniteAdelicTensorFactors
