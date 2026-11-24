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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.StarRing
public import MathlibExt.MeasureTheory.Group.HaarWeightedInversion
public import Mathlib.Topology.ContinuousMap.CocompactMap
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Group.Integral

/-!
# The original left and right actions on the Haar twisted core

The compact-support functions and the measure/action-indexed carrier remain the
original ones. Coefficients act by left multiplication and by the action-valued
right coefficient. Group elements act by inverse left translation with the
coefficient action, and by right translation with the right-pushforward modular
factor. The identities here are the algebraic prerequisites of the canonical
coefficient and group multiplier maps on the actual completed crossed product.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter
open scoped CompactlySupported Pointwise NNReal CStarAlgebra

namespace HaarTwistedCore

noncomputable section

universe uG uA

section CoefficientCc

variable {G : Type uG} [TopologicalSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]

/-- A coefficient multiplies the original compact-support function on the left. -/
def coefficientLeftCc (a : A) : C_c(G, A) →ₗ[ℂ] C_c(G, A) where
  toFun f :=
    { toFun s := a * f s
      continuous_toFun := continuous_const.mul (map_continuous f)
      hasCompactSupport' := f.hasCompactSupport.mul_left }
  map_add' f h := by
    apply CompactlySupportedContinuousMap.ext
    intro s
    change a * (f s + h s) = a * f s + a * h s
    exact mul_add _ _ _
  map_smul' c f := by
    apply CompactlySupportedContinuousMap.ext
    intro s
    change a * (c • f s) = c • (a * f s)
    exact mul_smul_comm _ _ _

/-- The left coefficient action has the literal original pointwise value. -/
@[simp]
theorem coefficientLeftCc_apply (a : A) (f : C_c(G, A)) (s : G) :
    coefficientLeftCc a f s = a * f s := rfl

section Monoid

variable [Monoid G] (α : PointNormCStarAction G A)

/-- A coefficient multiplies on the right through the original point-norm action. -/
def coefficientRightCc (a : A) : C_c(G, A) →ₗ[ℂ] C_c(G, A) where
  toFun f :=
    { toFun s := f s * α s a
      continuous_toFun := (map_continuous f).mul
        (α.continuous_apply continuous_id continuous_const)
      hasCompactSupport' := f.hasCompactSupport.mul_right }
  map_add' f h := by
    apply CompactlySupportedContinuousMap.ext
    intro s
    change (f s + h s) * α s a = f s * α s a + h s * α s a
    exact add_mul _ _ _
  map_smul' c f := by
    apply CompactlySupportedContinuousMap.ext
    intro s
    change (c • f s) * α s a = c • (f s * α s a)
    exact smul_mul_assoc _ _ _

/-- The right coefficient action has the original action-valued coefficient. -/
@[simp]
theorem coefficientRightCc_apply (a : A) (f : C_c(G, A)) (s : G) :
    coefficientRightCc α a f s = f s * α s a := rfl

end Monoid
end CoefficientCc

section GroupCc

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]

/-- Inverse left translation and the original coefficient action on C_c. -/
def groupLeftCc (α : PointNormCStarAction G A) (g : G) : C_c(G, A) →ₗ[ℂ] C_c(G, A) where
  toFun f :=
    { toFun s := α g (f (g⁻¹ * s))
      continuous_toFun := α.continuous_apply continuous_const
        ((map_continuous f).comp (continuous_const.mul continuous_id))
      hasCompactSupport' :=
        (f.comp (Homeomorph.mulLeft g⁻¹).toCocompactMap).hasCompactSupport.comp_left
          (α.apply_zero g) }
  map_add' f h := by
    apply CompactlySupportedContinuousMap.ext
    intro s
    change α g (f (g⁻¹ * s) + h (g⁻¹ * s)) =
      α g (f (g⁻¹ * s)) + α g (h (g⁻¹ * s))
    exact α.apply_add _ _ _
  map_smul' c f := by
    apply CompactlySupportedContinuousMap.ext
    intro s
    change α g (c • f (g⁻¹ * s)) = c • α g (f (g⁻¹ * s))
    exact α.apply_smul _ _ _

omit [LocallyCompactSpace G] in
/-- The original left group action retains its inverse-translation formula. -/
@[simp]
theorem groupLeftCc_apply (α : PointNormCStarAction G A) (g : G) (f : C_c(G, A)) (s : G) :
    groupLeftCc α g f s = α g (f (g⁻¹ * s)) := rfl

/-- Right translation has precisely the adopted right-pushforward modular factor. -/
def groupRightCc (g : G) : C_c(G, A) →ₗ[ℂ] C_c(G, A) :=
  ((Measure.modularCharacter g : ℝ) : ℂ) •
    CompactlySupportedContinuousMap.compLinearMap (R := ℂ) (Homeomorph.mulRight g⁻¹).toCocompactMap

/-- The original right group action has the printed Haar factor. -/
@[simp]
theorem groupRightCc_apply (g : G) (f : C_c(G, A)) (s : G) :
    groupRightCc g f s = ((Measure.modularCharacter g : ℝ) : ℂ) • f (s * g⁻¹) := rfl

end GroupCc

section CoreCoefficient

variable {G : Type uG} [Group G] [TopologicalSpace G] [MeasurableSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) (α : PointNormCStarAction G A)

/-- The actual left coefficient map on the same original indexed carrier. -/
def coefficientLeft (a : A) : Carrier μ α →ₗ[ℂ] Carrier μ α where
  toFun f := fromCc μ α (coefficientLeftCc a (toCc μ α f))
  map_add' f h := by
    apply (equivCc μ α).injective
    change coefficientLeftCc a (toCc μ α (f + h)) =
      toCc μ α (fromCc μ α (coefficientLeftCc a (toCc μ α f)) +
        fromCc μ α (coefficientLeftCc a (toCc μ α h)))
    simp only [toCc_add, toCc_fromCc, map_add]
  map_smul' c f := by
    apply (equivCc μ α).injective
    change coefficientLeftCc a (toCc μ α (c • f)) =
      toCc μ α (c • fromCc μ α (coefficientLeftCc a (toCc μ α f)))
    simp only [toCc_smul, toCc_fromCc, map_smul]

/-- Left coefficient evaluation retains the same original function value. -/
@[simp]
theorem coefficientLeft_apply (a : A) (f : Carrier μ α) (s : G) :
    coefficientLeft μ α a f s = a * f s := rfl

/-- The actual right coefficient map on the same original indexed carrier. -/
def coefficientRight (a : A) : Carrier μ α →ₗ[ℂ] Carrier μ α where
  toFun f := fromCc μ α (coefficientRightCc α a (toCc μ α f))
  map_add' f h := by
    apply (equivCc μ α).injective
    change coefficientRightCc α a (toCc μ α (f + h)) =
      toCc μ α (fromCc μ α (coefficientRightCc α a (toCc μ α f)) +
        fromCc μ α (coefficientRightCc α a (toCc μ α h)))
    simp only [toCc_add, toCc_fromCc, map_add]
  map_smul' c f := by
    apply (equivCc μ α).injective
    change coefficientRightCc α a (toCc μ α (c • f)) =
      toCc μ α (c • fromCc μ α (coefficientRightCc α a (toCc μ α f)))
    simp only [toCc_smul, toCc_fromCc, map_smul]

/-- Right coefficient evaluation retains the original action-valued coefficient. -/
@[simp]
theorem coefficientRight_apply (a : A) (f : Carrier μ α) (s : G) :
    coefficientRight μ α a f s = f s * α s a := rfl

/-- Original left coefficients compose by their original product. -/
theorem coefficientLeft_mul (a b : A) :
    coefficientLeft μ α (a * b) = (coefficientLeft μ α a).comp (coefficientLeft μ α b) := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [LinearMap.comp_apply, coefficientLeft_apply, mul_assoc]

/-- Original right coefficients compose in the double-centralizer order. -/
theorem coefficientRight_mul (a b : A) :
    coefficientRight μ α (a * b) = (coefficientRight μ α b).comp (coefficientRight μ α a) := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [LinearMap.comp_apply, coefficientRight_apply, α.apply_mul_elem, mul_assoc]

/-- The original left coefficient parameter is additive. -/
theorem coefficientLeft_add (a b : A) :
    coefficientLeft μ α (a + b) = coefficientLeft μ α a + coefficientLeft μ α b := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [LinearMap.add_apply, coefficientLeft_apply, toCc_add,
    CompactlySupportedContinuousMap.add_apply, add_mul]

/-- The original right coefficient parameter is additive. -/
theorem coefficientRight_add (a b : A) :
    coefficientRight μ α (a + b) = coefficientRight μ α a + coefficientRight μ α b := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [LinearMap.add_apply, coefficientRight_apply, toCc_add,
    CompactlySupportedContinuousMap.add_apply, α.apply_add, mul_add]

/-- The original left coefficient parameter has its actual complex scaling. -/
theorem coefficientLeft_smul (c : ℂ) (a : A) :
    coefficientLeft μ α (c • a) = c • coefficientLeft μ α a := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [LinearMap.smul_apply, coefficientLeft_apply, toCc_smul,
    CompactlySupportedContinuousMap.smul_apply, smul_mul_assoc]

/-- The original right coefficient parameter has its actual complex scaling. -/
theorem coefficientRight_smul (c : ℂ) (a : A) :
    coefficientRight μ α (c • a) = c • coefficientRight μ α a := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [LinearMap.smul_apply, coefficientRight_apply, toCc_smul,
    CompactlySupportedContinuousMap.smul_apply, α.apply_smul, mul_smul_comm]

end CoreCoefficient

section CoreGroup

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) (α : PointNormCStarAction G A)

/-- The actual inverse left group action on the same indexed compact-support functions. -/
def groupLeft (g : G) : Carrier μ α →ₗ[ℂ] Carrier μ α where
  toFun f := fromCc μ α (groupLeftCc α g (toCc μ α f))
  map_add' f h := by
    apply (equivCc μ α).injective
    change groupLeftCc α g (toCc μ α (f + h)) =
      toCc μ α (fromCc μ α (groupLeftCc α g (toCc μ α f)) +
        fromCc μ α (groupLeftCc α g (toCc μ α h)))
    simp only [toCc_add, toCc_fromCc, map_add]
  map_smul' c f := by
    apply (equivCc μ α).injective
    change groupLeftCc α g (toCc μ α (c • f)) =
      toCc μ α (c • fromCc μ α (groupLeftCc α g (toCc μ α f)))
    simp only [toCc_smul, toCc_fromCc, map_smul]

omit [LocallyCompactSpace G] in
/-- The indexed left group action retains every original inverse-translation value. -/
@[simp]
theorem groupLeft_apply (g : G) (f : Carrier μ α) (s : G) :
    groupLeft μ α g f s = α g (f (g⁻¹ * s)) := rfl

/-- The actual modular right group action on the same indexed compact-support functions. -/
def groupRight (g : G) : Carrier μ α →ₗ[ℂ] Carrier μ α where
  toFun f := fromCc μ α (groupRightCc g (toCc μ α f))
  map_add' f h := by
    apply (equivCc μ α).injective
    change groupRightCc g (toCc μ α (f + h)) =
      toCc μ α (fromCc μ α (groupRightCc g (toCc μ α f)) +
        fromCc μ α (groupRightCc g (toCc μ α h)))
    simp only [toCc_add, toCc_fromCc, map_add]
  map_smul' c f := by
    apply (equivCc μ α).injective
    change groupRightCc g (toCc μ α (c • f)) =
      toCc μ α (c • fromCc μ α (groupRightCc g (toCc μ α f)))
    simp only [toCc_smul, toCc_fromCc, map_smul]

/-- The indexed right group action retains the adopted modular factor. -/
@[simp]
theorem groupRight_apply (g : G) (f : Carrier μ α) (s : G) :
    groupRight μ α g f s = ((Measure.modularCharacter g : ℝ) : ℂ) • f (s * g⁻¹) := rfl

omit [LocallyCompactSpace G] in
/-- The original left group identity acts as the actual identity map. -/
theorem groupLeft_one : groupLeft μ α 1 = LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [groupLeft_apply, inv_one, one_mul, α.apply_one, LinearMap.id_apply]

/-- The original right group identity acts as the actual identity map. -/
theorem groupRight_one : groupRight μ α 1 = LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [groupRight_apply, map_one, NNReal.coe_one, Complex.ofReal_one,
    inv_one, mul_one, one_smul, LinearMap.id_apply]

omit [LocallyCompactSpace G] in
/-- Original left group actions compose in the source group order. -/
theorem groupLeft_mul (g h : G) :
    groupLeft μ α (g * h) = (groupLeft μ α g).comp (groupLeft μ α h) := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [LinearMap.comp_apply, groupLeft_apply, α.apply_mul, mul_inv_rev, mul_assoc]

/-- Original right group actions compose in the double-centralizer order. -/
theorem groupRight_mul (g h : G) :
    groupRight μ α (g * h) = (groupRight μ α h).comp (groupRight μ α g) := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [LinearMap.comp_apply, groupRight_apply, map_mul, NNReal.coe_mul,
    Complex.ofReal_mul, mul_inv_rev, mul_assoc, smul_smul]
  rw [mul_comm (((Measure.modularCharacter g : ℝ) : ℂ))
    (((Measure.modularCharacter h : ℝ) : ℂ))]

omit [LocallyCompactSpace G] in
/-- The source left group and coefficient actions obey the actual covariance equation. -/
theorem groupLeft_coefficientLeft (g : G) (a : A) :
    (groupLeft μ α g).comp (coefficientLeft μ α a) =
      (coefficientLeft μ α (α g a)).comp (groupLeft μ α g) := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [LinearMap.comp_apply, groupLeft_apply, coefficientLeft_apply, α.apply_mul_elem]

/-- The source right group and coefficient actions obey the second covariance component. -/
theorem coefficientRight_groupRight (g : G) (a : A) :
    (coefficientRight μ α a).comp (groupRight μ α g) =
      (groupRight μ α g).comp (coefficientRight μ α (α g a)) := by
  apply LinearMap.ext
  intro f
  apply ext μ α
  intro s
  simp only [LinearMap.comp_apply, coefficientRight_apply, groupRight_apply]
  have ha : α (s * g⁻¹) (α g a) = α s a := by
    rw [← α.apply_mul, mul_assoc, inv_mul_cancel, mul_one]
  change (α.aut (s * g⁻¹)) ((α.aut g) a) = (α.aut s) a at ha
  rw [ha, smul_mul_assoc]

end CoreGroup

section CoreStar

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) (α : PointNormCStarAction G A)

/-- The source star exchanges the left coefficient with the adjoint right coefficient. -/
theorem crossedStar_coefficientLeft (a : A) (f : Carrier μ α) :
    crossedStar μ α (coefficientLeft μ α a f) =
      coefficientRight μ α (star a) (crossedStar μ α f) := by
  apply ext μ α
  intro s
  simp only [crossedStar_apply, coefficientLeft_apply, coefficientRight_apply,
    star_mul, α.apply_mul_elem, smul_mul_assoc]

/-- The source star exchanges the right coefficient with the adjoint left coefficient. -/
theorem crossedStar_coefficientRight (a : A) (f : Carrier μ α) :
    crossedStar μ α (coefficientRight μ α a f) =
      coefficientLeft μ α (star a) (crossedStar μ α f) := by
  apply ext μ α
  intro s
  rw [crossedStar_apply, coefficientRight_apply, coefficientLeft_apply, crossedStar_apply]
  rw [star_mul, ← α.apply_star, α.apply_mul_elem, α.apply_apply_inv, mul_smul_comm]

/-- The source star exchanges inverse left translation with inverse right translation. -/
theorem crossedStar_groupLeft (g : G) (f : Carrier μ α) :
    crossedStar μ α (groupLeft μ α g f) =
      groupRight μ α g⁻¹ (crossedStar μ α f) := by
  apply ext μ α
  intro s
  have hδ : Measure.modularCharacter g⁻¹ * Measure.modularCharacter (s * g) =
      Measure.modularCharacter s := by
    rw [map_mul, mul_left_comm, ← map_mul, inv_mul_cancel, map_one, mul_one]
  have hd : ((Measure.modularCharacter g⁻¹ : ℝ) : ℂ) *
      ((Measure.modularCharacter (s * g) : ℝ) : ℂ) =
        ((Measure.modularCharacter s : ℝ) : ℂ) := by exact_mod_cast hδ
  rw [crossedStar_apply, groupLeft_apply, groupRight_apply, crossedStar_apply, inv_inv]
  rw [← α.apply_star, ← α.apply_mul, mul_inv_rev, smul_smul, hd]

/-- The source star exchanges modular right translation with inverse left translation. -/
theorem crossedStar_groupRight (g : G) (f : Carrier μ α) :
    crossedStar μ α (groupRight μ α g f) =
      groupLeft μ α g⁻¹ (crossedStar μ α f) := by
  apply ext μ α
  intro s
  have hstar : star ((Measure.modularCharacter g : ℝ) : ℂ) =
      ((Measure.modularCharacter g : ℝ) : ℂ) := by simp
  have hδ : Measure.modularCharacter s * Measure.modularCharacter g =
      Measure.modularCharacter (g * s) := by rw [map_mul, mul_comm]
  have hd : ((Measure.modularCharacter s : ℝ) : ℂ) *
      ((Measure.modularCharacter g : ℝ) : ℂ) =
        ((Measure.modularCharacter (g * s) : ℝ) : ℂ) := by exact_mod_cast hδ
  rw [crossedStar_apply, groupRight_apply, groupLeft_apply, crossedStar_apply, inv_inv]
  rw [star_smul, hstar, α.apply_smul, α.apply_smul, ← α.apply_mul,
    inv_mul_cancel_left, mul_inv_rev, smul_smul, hd]

end CoreStar

section CoreCompatibility

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (α : PointNormCStarAction G A)

omit [LocallyCompactSpace G] [μ.Regular] in
/-- Left coefficients are the original left centralizers of Haar convolution. -/
theorem coefficientLeft_convolution (a : A) (f h : Carrier μ α) :
    coefficientLeft μ α a (convolution μ α f h) =
      convolution μ α (coefficientLeft μ α a f) h := by
  apply ext μ α
  intro s
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  rw [coefficientLeft_apply, convolution_apply, convolution_apply]
  simp_rw [coefficientLeft_apply]
  let L : A →L[ℂ] A := ContinuousLinearMap.mul ℂ A a
  have hL (z : A) : L z = a * z := rfl
  calc
    a * (∫ t : G, f t * α t (h (t⁻¹ * s)) ∂μ) =
        L (∫ t : G, kernel α (toCc μ α f) (toCc μ α h) s t ∂μ) := rfl
    _ = ∫ t : G, L (kernel α (toCc μ α f) (toCc μ α h) s t) ∂μ :=
      (L.integral_comp_comm (integrable_kernel μ α (toCc μ α f) (toCc μ α h) s)).symm
    _ = ∫ t : G, (a * f t) * α t (h (t⁻¹ * s)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hL, kernel]
      exact (mul_assoc _ _ _).symm

omit [LocallyCompactSpace G] [μ.Regular] in
/-- Right coefficients are the original right centralizers of Haar convolution. -/
theorem coefficientRight_convolution (a : A) (f h : Carrier μ α) :
    coefficientRight μ α a (convolution μ α f h) =
      convolution μ α f (coefficientRight μ α a h) := by
  apply ext μ α
  intro s
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  rw [coefficientRight_apply, convolution_apply, convolution_apply]
  simp_rw [coefficientRight_apply]
  let R : A →L[ℂ] A := (ContinuousLinearMap.mul ℂ A).flip (α s a)
  have hR (z : A) : R z = z * α s a := rfl
  calc
    (∫ t : G, f t * α t (h (t⁻¹ * s)) ∂μ) * α s a =
        R (∫ t : G, kernel α (toCc μ α f) (toCc μ α h) s t ∂μ) := rfl
    _ = ∫ t : G, R (kernel α (toCc μ α f) (toCc μ α h) s t) ∂μ :=
      (R.integral_comp_comm (integrable_kernel μ α (toCc μ α f) (toCc μ α h) s)).symm
    _ = ∫ t : G, f t * α t (h (t⁻¹ * s) * α (t⁻¹ * s) a) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      have ha : α t (α (t⁻¹ * s) a) = α s a := by
        rw [← α.apply_mul, mul_inv_cancel_left]
      rw [hR, kernel]
      change (α.aut t) ((α.aut (t⁻¹ * s)) a) = (α.aut s) a at ha
      rw [map_mul (α.aut t), ha]
      exact mul_assoc _ _ _

omit [LocallyCompactSpace G] [μ.Regular] in
/-- The two original coefficient actions form one compatible centralizer pair. -/
theorem convolution_coefficientLeft (a : A) (f h : Carrier μ α) :
    convolution μ α f (coefficientLeft μ α a h) =
      convolution μ α (coefficientRight μ α a f) h := by
  apply ext μ α
  intro s
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  rw [convolution_apply, convolution_apply]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [coefficientLeft_apply, coefficientRight_apply, map_mul (α.aut t), mul_assoc]

omit [LocallyCompactSpace G] [μ.Regular] in
/-- Original inverse left translation is the left centralizer of Haar convolution. -/
theorem groupLeft_convolution (g : G) (f h : Carrier μ α) :
    groupLeft μ α g (convolution μ α f h) =
      convolution μ α (groupLeft μ α g f) h := by
  apply ext μ α
  intro s
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  rw [groupLeft_apply, convolution_apply, convolution_apply]
  let T : A →L[ℂ] A :=
    ⟨LinearMap.ofClass (α.aut g), (StarAlgEquiv.isometry (α.aut g)).continuous⟩
  have hT (z : A) : T z = α g z := rfl
  let K : G → A := fun u => α g (f (g⁻¹ * u)) * α u (h (u⁻¹ * s))
  have hPoint (t : G) :
      T (kernel α (toCc μ α f) (toCc μ α h) (g⁻¹ * s) t) = K (g * t) := by
    rw [hT, kernel]
    simp only [K, α.apply_mul_elem, α.apply_mul, inv_mul_cancel_left,
      mul_inv_rev, mul_assoc]
  calc
    α g (∫ t : G, f t * α t (h (t⁻¹ * (g⁻¹ * s))) ∂μ) =
        T (∫ t : G, kernel α (toCc μ α f) (toCc μ α h) (g⁻¹ * s) t ∂μ) := rfl
    _ = ∫ t : G, T (kernel α (toCc μ α f) (toCc μ α h) (g⁻¹ * s) t) ∂μ :=
      (T.integral_comp_comm (integrable_kernel μ α (toCc μ α f) (toCc μ α h) (g⁻¹ * s))).symm
    _ = ∫ t : G, K (g * t) ∂μ := integral_congr_ae (Eventually.of_forall hPoint)
    _ = ∫ u : G, K u ∂μ := integral_mul_left_eq_self (μ := μ) K g
    _ = ∫ u : G, groupLeft μ α g f u * α u (h (u⁻¹ * s)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [groupLeft_apply]

omit [μ.Regular] in
/-- Original modular right translation is the right centralizer of Haar convolution. -/
theorem groupRight_convolution (g : G) (f h : Carrier μ α) :
    groupRight μ α g (convolution μ α f h) =
      convolution μ α f (groupRight μ α g h) := by
  apply ext μ α
  intro s
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  rw [groupRight_apply, convolution_apply, convolution_apply]
  calc
    ((Measure.modularCharacter g : ℝ) : ℂ) •
        (∫ t : G, f t * α t (h (t⁻¹ * (s * g⁻¹))) ∂μ) =
      ∫ t : G, ((Measure.modularCharacter g : ℝ) : ℂ) •
        (f t * α t (h (t⁻¹ * (s * g⁻¹)))) ∂μ := (integral_smul _ _).symm
    _ = ∫ t : G, f t * α t (groupRight μ α g h (t⁻¹ * s)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [groupRight_apply, map_smul (α.aut t), mul_smul_comm, mul_assoc]

/-- Original left and modular right translations form the source centralizer pair. -/
theorem convolution_groupLeft (g : G) (f h : Carrier μ α) :
    convolution μ α f (groupLeft μ α g h) =
      convolution μ α (groupRight μ α g f) h := by
  apply ext μ α
  intro s
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  rw [convolution_apply, convolution_apply]
  let K : G → A := fun u => f (u * g⁻¹) * α u (h (u⁻¹ * s))
  have hPoint (t : G) : f t * α t (groupLeft μ α g h (t⁻¹ * s)) = K (t * g) := by
    rw [groupLeft_apply]
    simp only [K, α.apply_mul, mul_inv_rev, mul_assoc]
    rw [mul_inv_cancel, mul_one]
  calc
    (∫ t : G, f t * α t (groupLeft μ α g h (t⁻¹ * s)) ∂μ) =
        ∫ t : G, K (t * g) ∂μ := integral_congr_ae (Eventually.of_forall hPoint)
    _ = (Measure.modularCharacter g : ℝ) • ∫ u : G, K u ∂μ :=
      MeasureTheory.integral_mul_right_modular μ K g
    _ = ((Measure.modularCharacter g : ℝ) : ℂ) • ∫ u : G, K u ∂μ := rfl
    _ = ∫ u : G, ((Measure.modularCharacter g : ℝ) : ℂ) • K u ∂μ :=
      (integral_smul _ _).symm
    _ = ∫ u : G, groupRight μ α g f u * α u (h (u⁻¹ * s)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [groupRight_apply, smul_mul_assoc]

end CoreCompatibility

end

end HaarTwistedCore
