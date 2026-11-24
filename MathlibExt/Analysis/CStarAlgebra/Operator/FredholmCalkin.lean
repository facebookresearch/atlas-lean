/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Operator.Calkin
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic

import MathlibExt.Analysis.InnerProductSpace.CompactOperator
import Mathlib.Analysis.Normed.Operator.Fredholm.Open
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.IntermediateValue

/-!
# Fredholm operators and the Calkin algebra

This file develops the bridges relating Fredholm operators on a complex
Hilbert space to invertible classes in the Calkin algebra. Equality of Calkin
classes is identified with compactness of the corresponding operator
difference, and Atkinson's theorem identifies Fredholm operators exactly with
operators having invertible Calkin class. The resulting Fredholm index depends
only on the Calkin unit and defines a homomorphism to the additive integers.
-/

@[expose] public section

noncomputable section

open scoped LinearMap.FiniteRangeSetoid

namespace CalkinAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Two operators have the same Calkin class exactly when their difference is
compact. The difference orientation is fixed as `T - U`. -/
@[simp]
theorem classStarMap_eq_iff (T U : H →L[ℂ] H) :
    classStarMap (H := H) T = classStarMap (H := H) U ↔
      IsCompactOperator (T - U) := by
  rw [← classStarMap_eq_zero_iff, map_sub, sub_eq_zero]

private theorem isUnit_classStarMap_of_isFredholm {T : H →L[ℂ] H}
    (hT : T.IsFredholm) : IsUnit (classStarMap (H := H) T) := by
  obtain ⟨S, hS⟩ := hT.exists_isQuasiInverse
  have hSTfinite : (S * T - 1).toLinearMap.HasFiniteRange := by
    change (S.toLinearMap ∘ₗ T.toLinearMap - LinearMap.id).HasFiniteRange
    exact LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mp hS.1
  have hTSfinite : (T * S - 1).toLinearMap.HasFiniteRange := by
    change (T.toLinearMap ∘ₗ S.toLinearMap - LinearMap.id).HasFiniteRange
    exact LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mp hS.2
  have hSTcompact : IsCompactOperator ⇑(S * T - 1 : H →L[ℂ] H) :=
    hSTfinite.isCompactOperator
  have hTScompact : IsCompactOperator ⇑(T * S - 1 : H →L[ℂ] H) :=
    hTSfinite.isCompactOperator
  have hST :
      classStarMap (H := H) S * classStarMap (H := H) T = 1 := by
    have hz := (classStarMap_eq_zero_iff (H := H) (S * T - 1)).2 hSTcompact
    rw [map_sub, map_mul, map_one, sub_eq_zero] at hz
    exact hz
  have hTS :
      classStarMap (H := H) T * classStarMap (H := H) S = 1 := by
    have hz := (classStarMap_eq_zero_iff (H := H) (T * S - 1)).2 hTScompact
    rw [map_sub, map_mul, map_one, sub_eq_zero] at hz
    exact hz
  exact isUnit_iff_exists.mpr ⟨classStarMap (H := H) S, hTS, hST⟩

private theorem isFredholm_of_isUnit_classStarMap {T : H →L[ℂ] H}
    (hunit : IsUnit (classStarMap (H := H) T)) : T.IsFredholm := by
  obtain ⟨b, hTb, hbT⟩ := isUnit_iff_exists.mp hunit
  obtain ⟨S, hS⟩ := classStarMap_surjective (H := H) b
  let K_L : H →L[ℂ] H := S * T - 1
  let K_R : H →L[ℂ] H := T * S - 1
  have hKL : IsCompactOperator K_L :=
    (classStarMap_eq_zero_iff (H := H) K_L).mp (by
      change classStarMap (H := H) (S * T - 1) = 0
      rw [map_sub, map_mul, map_one, hS, hbT, sub_self])
  have hKR : IsCompactOperator K_R :=
    (classStarMap_eq_zero_iff (H := H) K_R).mp (by
      change classStarMap (H := H) (T * S - 1) = 0
      rw [map_sub, map_mul, map_one, hS, hTb, sub_self])
  obtain ⟨U_L, hUL, hLapprox⟩ :=
    hKL.exists_projectionFactor_hasFiniteRange_adjoint_norm_sub_lt
      (ε := 1) zero_lt_one
  let _ : FiniteDimensional ℂ U_L := hUL
  obtain ⟨F_L, _hFLfactor, hFLfinite, _hFLadj, hFLnorm⟩ := hLapprox
  let E_L : H →L[ℂ] H := K_L - F_L
  have hEL : ‖E_L‖ < 1 := by
    simpa [E_L] using hFLnorm
  let u_L : (H →L[ℂ] H)ˣ := Units.oneSub (-E_L) (by simpa using hEL)
  let L : H →L[ℂ] H := (↑(u_L⁻¹) : H →L[ℂ] H) * S
  have huLval : (u_L : H →L[ℂ] H) = 1 + E_L := by
    simp [u_L]
  have hST : S * T = (u_L : H →L[ℂ] H) + F_L := by
    rw [huLval]
    dsimp [E_L, K_L]
    noncomm_ring
  have hLdefect :
      L * T - 1 = (↑(u_L⁻¹) : H →L[ℂ] H) * F_L := by
    have huLinv :
        (↑(u_L⁻¹) : H →L[ℂ] H) * (u_L : H →L[ℂ] H) = 1 :=
      Units.inv_mul u_L
    dsimp [L]
    rw [mul_assoc, hST, mul_add, huLinv]
    noncomm_ring
  have hLfinite : (L * T - 1).toLinearMap.HasFiniteRange := by
    rw [hLdefect]
    change (((↑(u_L⁻¹) : H →L[ℂ] H).toLinearMap ∘ₗ
      F_L.toLinearMap).HasFiniteRange)
    exact hFLfinite.comp_left _
  obtain ⟨U_R, hUR, hRapprox⟩ :=
    hKR.exists_projectionFactor_hasFiniteRange_adjoint_norm_sub_lt
      (ε := 1) zero_lt_one
  let _ : FiniteDimensional ℂ U_R := hUR
  obtain ⟨F_R, _hFRfactor, hFRfinite, _hFRadj, hFRnorm⟩ := hRapprox
  let E_R : H →L[ℂ] H := K_R - F_R
  have hER : ‖E_R‖ < 1 := by
    simpa [E_R] using hFRnorm
  let u_R : (H →L[ℂ] H)ˣ := Units.oneSub (-E_R) (by simpa using hER)
  let R : H →L[ℂ] H := S * (↑(u_R⁻¹) : H →L[ℂ] H)
  have huRval : (u_R : H →L[ℂ] H) = 1 + E_R := by
    simp [u_R]
  have hTS : T * S = (u_R : H →L[ℂ] H) + F_R := by
    rw [huRval]
    dsimp [E_R, K_R]
    noncomm_ring
  have hRdefect :
      T * R - 1 = F_R * (↑(u_R⁻¹) : H →L[ℂ] H) := by
    have huRinv :
        (u_R : H →L[ℂ] H) * (↑(u_R⁻¹) : H →L[ℂ] H) = 1 :=
      Units.mul_inv u_R
    dsimp [R]
    rw [← mul_assoc, hTS, add_mul, huRinv]
    noncomm_ring
  have hRfinite : (T * R - 1).toLinearMap.HasFiniteRange := by
    rw [hRdefect]
    change ((F_R.toLinearMap ∘ₗ
      (↑(u_R⁻¹) : H →L[ℂ] H).toLinearMap).HasFiniteRange)
    exact hFRfinite.comp_right _
  have hLleft : L.toLinearMap.IsLeftQuasiInverse T.toLinearMap := by
    rw [LinearMap.IsLeftQuasiInverse,
      LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange]
    change (L * T - 1).toLinearMap.HasFiniteRange
    exact hLfinite
  have hRright : R.toLinearMap.IsRightQuasiInverse T.toLinearMap := by
    rw [LinearMap.IsRightQuasiInverse,
      LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange]
    change (T * R - 1).toLinearMap.HasFiniteRange
    exact hRfinite
  have hOneTRfinite : (1 - T * R).toLinearMap.HasFiniteRange := by
    have heq : 1 - T * R = -(T * R - 1) := by
      noncomm_ring
    rw [heq]
    simpa using hRfinite.neg
  have hTerm1 : (L * (1 - T * R)).toLinearMap.HasFiniteRange := by
    change (L.toLinearMap ∘ₗ (1 - T * R).toLinearMap).HasFiniteRange
    exact hOneTRfinite.comp_left L.toLinearMap
  have hTerm2 : ((L * T - 1) * R).toLinearMap.HasFiniteRange := by
    change ((L * T - 1).toLinearMap ∘ₗ R.toLinearMap).HasFiniteRange
    exact hLfinite.comp_right R.toLinearMap
  have hLRfinite : (L - R).toLinearMap.HasFiniteRange := by
    have hid : L - R = L * (1 - T * R) + (L * T - 1) * R := by
      noncomm_ring
    rw [hid]
    simpa using hTerm1.add hTerm2
  have hLR : L.toLinearMap ≈ R.toLinearMap := by
    rw [LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange]
    change (L - R).toLinearMap.HasFiniteRange
    exact hLRfinite
  have hLright : L.toLinearMap.IsRightQuasiInverse T.toLinearMap :=
    hRright.congr hLR (Setoid.refl _)
  exact ContinuousLinearMap.IsFredholm.of_isQuasiInverse ⟨hLleft, hLright⟩

/-- Atkinson's theorem: an operator on a complex Hilbert space is Fredholm
exactly when its Calkin class is invertible. -/
theorem isUnit_classStarMap_iff_isFredholm (T : H →L[ℂ] H) :
    IsUnit (classStarMap (H := H) T) ↔ T.IsFredholm :=
  ⟨isFredholm_of_isUnit_classStarMap,
    isUnit_classStarMap_of_isFredholm⟩

end CalkinAlgebra

namespace ContinuousLinearMap.IsFredholm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Fredholmness depends only on the Calkin class. -/
theorem of_classStarMap_eq {T U : H →L[ℂ] H} (hT : T.IsFredholm)
    (h : CalkinAlgebra.classStarMap (H := H) T =
      CalkinAlgebra.classStarMap (H := H) U) : U.IsFredholm := by
  apply (CalkinAlgebra.isUnit_classStarMap_iff_isFredholm U).mp
  rw [← h]
  exact (CalkinAlgebra.isUnit_classStarMap_iff_isFredholm T).mpr hT

/-- Equal Calkin classes of Fredholm operators have equal index. -/
theorem index_eq_of_classStarMap_eq {T U : H →L[ℂ] H} (hT : T.IsFredholm)
    (h : CalkinAlgebra.classStarMap (H := H) T =
      CalkinAlgebra.classStarMap (H := H) U) : T.index = U.index := by
  let P : ℝ → (H →L[ℂ] H) := fun t => T + (t : ℂ) • (U - T)
  have hUT : CalkinAlgebra.classStarMap (H := H) (U - T) = 0 := by
    rw [map_sub, h, sub_self]
  have hPclass (t : ℝ) :
      CalkinAlgebra.classStarMap (H := H) T =
        CalkinAlgebra.classStarMap (H := H) (P t) := by
    change CalkinAlgebra.classStarMap (H := H) T =
      CalkinAlgebra.classStarMap (H := H) (T + (t : ℂ) • (U - T))
    rw [map_add, map_smul, hUT, smul_zero, add_zero]
  have hP (t : ℝ) : (P t).IsFredholm :=
    hT.of_classStarMap_eq (hPclass t)
  have hPcontinuous : Continuous P := by
    dsimp [P]
    exact (continuous_const : Continuous (fun _ : ℝ => T)).add
      (Complex.continuous_ofReal.smul
        (continuous_const : Continuous (fun _ : ℝ => U - T)))
  have hindex : Continuous (fun t : ℝ => (P t).index) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hP t).index_continuousAt.comp hPcontinuous.continuousAt
  have h01 : (P (0 : ℝ)).index = (P (1 : ℝ)).index :=
    (inferInstance : PreconnectedSpace ℝ).constant hindex
  simpa [P] using h01

/-- Compact perturbations preserve Fredholmness. -/
theorem add_compact {T K : H →L[ℂ] H} (hT : T.IsFredholm)
    (hK : IsCompactOperator K) : (T + K).IsFredholm := by
  apply hT.of_classStarMap_eq
  rw [map_add,
    (CalkinAlgebra.classStarMap_eq_zero_iff (H := H) K).2 hK, add_zero]

/-- Compact perturbations preserve the Fredholm index. -/
theorem index_add_compact {T K : H →L[ℂ] H} (hT : T.IsFredholm)
    (hK : IsCompactOperator K) : (T + K).index = T.index := by
  symm
  apply hT.index_eq_of_classStarMap_eq
  rw [map_add,
    (CalkinAlgebra.classStarMap_eq_zero_iff (H := H) K).2 hK, add_zero]

/-- Subtracting a compact operator preserves Fredholmness. -/
theorem sub_compact {T K : H →L[ℂ] H} (hT : T.IsFredholm)
    (hK : IsCompactOperator K) : (T - K).IsFredholm := by
  rw [sub_eq_add_neg]
  exact hT.add_compact (by simpa using hK.neg)

/-- Subtracting a compact operator preserves the Fredholm index. -/
theorem index_sub_compact {T K : H →L[ℂ] H} (hT : T.IsFredholm)
    (hK : IsCompactOperator K) : (T - K).index = T.index := by
  rw [sub_eq_add_neg]
  exact hT.index_add_compact (by simpa using hK.neg)

end ContinuousLinearMap.IsFredholm

namespace CalkinAlgebra.Unit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The Fredholm index of a unit in the Calkin algebra. -/
noncomputable def index (x : (CalkinAlgebra ℂ H)ˣ) : ℤ :=
  (Classical.choose
    (classStarMap_surjective (H := H) (x : CalkinAlgebra ℂ H))).index

/-- The Calkin-unit index is computed by every operator lift. -/
theorem index_eq_lift (x : (CalkinAlgebra ℂ H)ˣ) (T : H →L[ℂ] H)
    (hT : classStarMap (H := H) T = (x : CalkinAlgebra ℂ H)) :
    index x = T.index := by
  let S : H →L[ℂ] H := Classical.choose
    (classStarMap_surjective (H := H) (x : CalkinAlgebra ℂ H))
  have hS : classStarMap (H := H) S = (x : CalkinAlgebra ℂ H) :=
    Classical.choose_spec
      (classStarMap_surjective (H := H) (x : CalkinAlgebra ℂ H))
  have hSFred : S.IsFredholm := by
    apply (isUnit_classStarMap_iff_isFredholm S).mp
    rw [hS]
    exact x.isUnit
  change S.index = T.index
  exact hSFred.index_eq_of_classStarMap_eq (hS.trans hT.symm)

/-- The identity Calkin unit has index zero. -/
@[simp]
theorem index_one : index (1 : (CalkinAlgebra ℂ H)ˣ) = 0 := by
  calc
    index (1 : (CalkinAlgebra ℂ H)ˣ) = (1 : H →L[ℂ] H).index :=
      index_eq_lift _ _ (classStarMap (H := H)).map_one
    _ = 0 := by
      change (LinearMap.id : H →ₗ[ℂ] H).index = 0
      exact LinearMap.index_id

/-- The index of a product of Calkin units is the sum of their indices. -/
@[simp]
theorem index_mul (x y : (CalkinAlgebra ℂ H)ˣ) :
    index (x * y) = index x + index y := by
  obtain ⟨T, hT⟩ :=
    classStarMap_surjective (H := H) (x : CalkinAlgebra ℂ H)
  obtain ⟨U, hU⟩ :=
    classStarMap_surjective (H := H) (y : CalkinAlgebra ℂ H)
  have hTFred : T.IsFredholm := by
    apply (isUnit_classStarMap_iff_isFredholm T).mp
    rw [hT]
    exact x.isUnit
  have hUFred : U.IsFredholm := by
    apply (isUnit_classStarMap_iff_isFredholm U).mp
    rw [hU]
    exact y.isUnit
  have hTU : classStarMap (H := H) (T * U) =
      ((x * y : (CalkinAlgebra ℂ H)ˣ) : CalkinAlgebra ℂ H) := by
    calc
      classStarMap (H := H) (T * U) =
          classStarMap (H := H) T * classStarMap (H := H) U :=
        (classStarMap (H := H)).map_mul T U
      _ = (x : CalkinAlgebra ℂ H) * (y : CalkinAlgebra ℂ H) :=
        congrArg₂ (· * ·) hT hU
      _ = ((x * y : (CalkinAlgebra ℂ H)ˣ) : CalkinAlgebra ℂ H) := rfl
  calc
    index (x * y) = (T * U).index := index_eq_lift _ _ hTU
    _ = T.index + U.index := by
      simpa only [ContinuousLinearMap.mul_def] using
        hTFred.index_comp hUFred
    _ = index x + index y := congrArg₂ (· + ·)
      (index_eq_lift x T hT).symm (index_eq_lift y U hU).symm

/-- Inversion negates the Calkin-unit index. -/
@[simp]
theorem index_inv (x : (CalkinAlgebra ℂ H)ˣ) :
    index x⁻¹ = -index x := by
  have h := index_mul x x⁻¹
  rw [mul_inv_cancel, index_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- The Calkin-unit index as a multiplicative-to-additive homomorphism. -/
noncomputable def indexHom :
    (CalkinAlgebra ℂ H)ˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (index x)
  map_one' := by
    change Multiplicative.ofAdd (index (1 : (CalkinAlgebra ℂ H)ˣ)) =
      Multiplicative.ofAdd 0
    rw [index_one]
  map_mul' x y := by
    change Multiplicative.ofAdd (index (x * y)) =
      Multiplicative.ofAdd (index x + index y)
    rw [index_mul]

/-- Evaluation of the Calkin-unit index homomorphism. -/
@[simp]
theorem indexHom_apply (x : (CalkinAlgebra ℂ H)ˣ) :
    (indexHom (H := H) x).toAdd = index x :=
  rfl

end CalkinAlgebra.Unit
