/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.SLE.BrownianDyadicModulus
import Code.SLE.LoewnerHolomorphicDependence










open MeasureTheory

namespace StatMech.SLE


noncomputable def canonicalBrownianLoewnerDomain (kappa : Real) :
    (Real -> Real) -> Real -> Set Complex :=
  fun omega => loewnerUnswallowedDomain
    (sleDriving kappa brownianContinuousModification omega)


noncomputable def canonicalBrownianLoewnerMaps (kappa : Real) :
    (Real -> Real) -> Real -> Complex -> Complex :=
  fun omega => loewnerMaximalMaps
    (sleDriving kappa brownianContinuousModification omega)


noncomputable def canonicalBrownianLoewnerHull (kappa : Real) :
    (Real -> Real) -> Real -> Set Complex :=
  fun omega => loewnerSwallowedSet
    (sleDriving kappa brownianContinuousModification omega)



theorem canonicalBrownian_isChordalSLE (kappa : Real) (hkappa : 0 <= kappa) :
    IsChordalSLE kappa brownianContinuousModification brownianProductLaw
      (canonicalBrownianLoewnerDomain kappa)
      (canonicalBrownianLoewnerMaps kappa) := by
  refine {
    kappa_nonneg := hkappa
    isBrownian := brownianContinuousModification_isStandardBrownianMotion
    loewner := ?_ }
  filter_upwards [
    brownianContinuousModification_isStandardBrownianMotion.continuous_paths]
      with omega homega
  exact loewnerMaximalMaps_satisfiesMaximalLoewnerEquation
    (continuous_const.mul homega)



theorem canonicalBrownianLoewnerHull_isCompactHull (kappa : Real) :
    ∀ᵐ omega ∂brownianProductLaw,
      forall t, 0 <= t ->
        IsCompactHull (canonicalBrownianLoewnerHull kappa omega t) := by
  filter_upwards [
    brownianContinuousModification_isStandardBrownianMotion.continuous_paths]
      with omega homega
  intro t ht
  exact loewnerSwallowedSet_isCompactHull
    (continuous_const.mul homega) ht



theorem canonicalBrownianLoewnerHull_monotoneOn
    (kappa : Real) (omega : Real -> Real) :
    MonotoneOn (canonicalBrownianLoewnerHull kappa omega) (Set.Ici 0) :=
  loewnerSwallowedSet_monotoneOn
    (sleDriving kappa brownianContinuousModification omega)



theorem canonicalBrownianLoewnerDomain_eq_complement
    (kappa : Real) (omega : Real -> Real) (t : Real) :
    canonicalBrownianLoewnerDomain kappa omega t =
      upperHalfPlane \ canonicalBrownianLoewnerHull kappa omega t := by
  exact (upperHalfPlane_diff_loewnerSwallowedSet
    (sleDriving kappa brownianContinuousModification omega) t).symm



theorem canonicalBrownianLoewnerMaps_conformalOn (kappa : Real) :
    ∀ᵐ omega ∂brownianProductLaw,
      forall t, 0 <= t -> forall z,
        z ∈ canonicalBrownianLoewnerDomain kappa omega t ->
          ConformalAt (canonicalBrownianLoewnerMaps kappa omega t) z := by
  filter_upwards [
    brownianContinuousModification_isStandardBrownianMotion.continuous_paths]
      with omega homega
  intro t ht z hz
  exact loewnerMaximalMaps_conformalOn
    (continuous_const.mul homega) ht z hz



theorem canonicalBrownianLoewnerMaps_homeomorph (kappa : Real) :
    ∀ᵐ omega ∂brownianProductLaw, ∀ t, 0 <= t ->
      Nonempty (canonicalBrownianLoewnerDomain kappa omega t ≃ₜ
        upperHalfPlane) := by
  filter_upwards [
    brownianContinuousModification_isStandardBrownianMotion.continuous_paths]
      with omega homega
  intro t ht
  exact ⟨loewnerMaximalMapsHomeomorph
    (continuous_const.mul homega) ht⟩

end StatMech.SLE
