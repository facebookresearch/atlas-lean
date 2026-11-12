/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.SLE.FKIsingInterfaceConvergenceReduction
import Code.SLE.CanonicalBrownianLaw
import Code.SLE.CanonicalBrownianSLE













open Filter MeasureTheory

namespace StatMech.SLE



noncomputable def fkIsingObservableJet (t W u : Real) : Real :=
  1 + W / 2 * u + (3 * W ^ 2 - 16 * t) / 8 * u ^ 2



theorem fkIsingObservableJet_secondCoeff
    (t W : Real) :
    (3 * W ^ 2 - 16 * t) / 8 =
      (3 / 8 : Real) * (W ^ 2 - kappaFKIsing * t) := by
  norm_num [kappaFKIsing]
  ring




theorem fkIsingObservableJet_sq_mul_denominator
    (t W u : Real) :
    let a := W / 2
    let b := (3 * W ^ 2 - 16 * t) / 8
    let remainder :=
      (2 * a * b - W * (a ^ 2 + 2 * b) + 4 * t * a) +
      (b ^ 2 - 2 * a * b * W + 2 * t * (a ^ 2 + 2 * b)) * u +
      (-W * b ^ 2 + 4 * t * a * b) * u ^ 2 +
      (2 * t * b ^ 2) * u ^ 3
    fkIsingObservableJet t W u ^ 2 * (1 - W * u + 2 * t * u ^ 2) =
      1 - 2 * t * u ^ 2 + u ^ 3 * remainder := by
  dsimp [fkIsingObservableJet]
  ring

theorem kappaFKIsing_pos : 0 < kappaFKIsing := by
  norm_num [kappaFKIsing]

theorem sq_sqrt_kappaFKIsing : Real.sqrt kappaFKIsing ^ 2 = kappaFKIsing := by
  exact Real.sq_sqrt kappaFKIsing_pos.le

theorem sqrt_kappaFKIsing_ne_zero : Real.sqrt kappaFKIsing ≠ 0 :=
  (Real.sqrt_pos.mpr kappaFKIsing_pos).ne'


theorem fkIsingDriving_div_sqrt
    {Omega : Type*} (B : Real → Omega → Real) (omega : Omega) (t : Real) :
    sleDriving kappaFKIsing B omega t / Real.sqrt kappaFKIsing = B t omega := by
  rw [sleDriving_apply]
  exact mul_div_cancel_left₀ (B t omega) sqrt_kappaFKIsing_ne_zero




theorem isChordalSLE_kappaFKIsing_of_brownian_loewner
    {Omega : Type*} [MeasurableSpace Omega]
    (B : Real → Omega → Real) (P : Measure Omega)
    (D : Omega → Real → Set ℂ)
    (g : Omega → Real → ℂ → ℂ)
    (hB : IsStandardBrownianMotion B P)
    (hloewner : ∀ᵐ omega ∂P,
      SatisfiesMaximalLoewnerEquation
        (sleDriving kappaFKIsing B omega) (D omega) (g omega)) :
    IsChordalSLE kappaFKIsing B P D g where
  kappa_nonneg := kappaFKIsing_pos.le
  isBrownian := hB
  loewner := hloewner



theorem isChordalSLE_kappaFKIsing_of_canonicalBrownian_loewner
    (D : (Real -> Real) -> Real -> Set ℂ)
    (g : (Real -> Real) -> Real -> ℂ -> ℂ)
    (hloewner : ∀ᵐ omega ∂brownianProductLaw,
      SatisfiesMaximalLoewnerEquation
        (sleDriving kappaFKIsing brownianContinuousModification omega)
        (D omega) (g omega)) :
    IsChordalSLE kappaFKIsing brownianContinuousModification
      brownianProductLaw D g :=
  isChordalSLE_kappaFKIsing_of_brownian_loewner
    brownianContinuousModification brownianProductLaw D g
      brownianContinuousModification_isStandardBrownianMotion hloewner




theorem isChordalSLE_kappaFKIsing_of_canonical_loewner :
    IsChordalSLE kappaFKIsing brownianContinuousModification
      brownianProductLaw
      (fun omega => loewnerUnswallowedDomain
        (sleDriving kappaFKIsing brownianContinuousModification omega))
      (fun omega => loewnerMaximalMaps
        (sleDriving kappaFKIsing brownianContinuousModification omega)) := by
  simpa [canonicalBrownianLoewnerDomain, canonicalBrownianLoewnerMaps] using
    canonicalBrownian_isChordalSLE kappaFKIsing kappaFKIsing_pos.le




theorem IsChordalSLE.driving_processLaw_eq_canonicalScaled
    {Omega : Type*} [MeasurableSpace Omega]
    {kappa : Real} {B : Real -> Omega -> Real} {P : Measure Omega}
    {D : Omega -> Real -> Set Complex}
    {g : Omega -> Real -> Complex -> Complex}
    (hSLE : IsChordalSLE kappa B P D g) :
    P.map (fun omega => sleDriving kappa B omega) =
      brownianProductLaw.map
        (fun b : Real -> Real => fun t => Real.sqrt kappa * b t) := by
  calc
    P.map (fun omega => sleDriving kappa B omega) =
        brownianProductLaw.map
          (fun omega => sleDriving kappa brownianContinuousModification omega) :=
      standardBrownian_sleDriving_processLaw_eq hSLE.isBrownian
        brownianContinuousModification_isStandardBrownianMotion kappa
    _ = brownianProductLaw.map
          (fun b : Real -> Real => fun t => Real.sqrt kappa * b t) :=
      brownianContinuousModification_sleDriving_processLaw kappa





theorem tendsto_fkIsing_sleDriving_processLaw_of_isChordalSLE
    {Omega : Type*} [MeasurableSpace Omega]
    (B : Nat -> Real -> Omega -> Real) (P : Nat -> Measure Omega)
    (D : Nat -> Omega -> Real -> Set Complex)
    (g : Nat -> Omega -> Real -> Complex -> Complex)
    (hSLE : forall n,
      IsChordalSLE kappaFKIsing (B n) (P n) (D n) (g n)) :
    Tendsto
      (fun n => (P n).map
        (fun omega => sleDriving kappaFKIsing (B n) omega))
      atTop
      (pure (brownianProductLaw.map
        (fun b : Real -> Real => fun t =>
          Real.sqrt kappaFKIsing * b t))) := by
  apply tendsto_const_pure.congr'
  filter_upwards [] with n
  exact (hSLE n).driving_processLaw_eq_canonicalScaled.symm

end StatMech.SLE
