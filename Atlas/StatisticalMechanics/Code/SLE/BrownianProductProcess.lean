/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.SLE.BrownianProjectiveExtension
import Code.SLE.BrownianMomentBound
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic









open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StatMech.SLE



def brownianCoordinateProcess (t : Real) (omega : Real -> Real) : Real :=
  omega t

theorem brownianCoordinateProcess_measurable (t : Real) :
    Measurable (brownianCoordinateProcess t) := by
  change Measurable (fun omega : Real -> Real => omega t)
  fun_prop

instance brownianFiniteDimensionalPiLaw.isGaussian (I : Finset Real) :
    IsGaussian (brownianFiniteDimensionalPiLaw I) := by
  unfold brownianFiniteDimensionalPiLaw
  change IsGaussian ((brownianFiniteDimensionalLaw I).map
    (PiLp.continuousLinearEquiv 2 Real (fun _ : I => Real)))
  infer_instance


theorem brownianCoordinateProcess_isGaussianProcess :
    IsGaussianProcess brownianCoordinateProcess brownianProductLaw where
  hasGaussianLaw I := by
    refine ⟨?_⟩
    simp only [brownianCoordinateProcess]
    rw [brownianProductLaw_isProjectiveLimit I]
    infer_instance



theorem brownianFiniteDimensionalPiLaw_measurePreserving_increment
    (I : Finset Real) (s t : I) :
    MeasurePreserving (fun x : I -> Real => x t - x s)
      (brownianFiniteDimensionalPiLaw I)
      (gaussianReal 0 |(t : Real) - (s : Real)|.toNNReal) where
  measurable := by fun_prop
  map_eq := by
    rw [brownianFiniteDimensionalPiLaw,
      Measure.map_map (by fun_prop)
        (WithLp.measurable_ofLp 2 (I -> Real))]
    exact (brownianFiniteDimensionalLaw_measurePreserving_increment I s t).map_eq



theorem brownianFiniteDimensionalPiLaw_measurePreserving_eval
    (I : Finset Real) (t : I) :
    MeasurePreserving (fun x : I -> Real => x t)
      (brownianFiniteDimensionalPiLaw I)
      (gaussianReal 0 |(t : Real)|.toNNReal) where
  measurable := by fun_prop
  map_eq := by
    rw [brownianFiniteDimensionalPiLaw,
      Measure.map_map (by fun_prop)
        (WithLp.measurable_ofLp 2 (I -> Real))]
    exact (brownianFiniteDimensionalLaw_measurePreserving_eval I t).map_eq



theorem brownianCoordinateProcess_eval_law (t : Real) :
    HasLaw (brownianCoordinateProcess t)
      (gaussianReal 0 |t|.toNNReal) brownianProductLaw := by
  let I : Finset Real := {t}
  let tI : I := ⟨t, by simp [I]⟩
  have hrestrict : Measurable (fun omega : Real -> Real => I.restrict omega) :=
    Finset.measurable_restrict I
  constructor
  · exact (brownianCoordinateProcess_measurable t).aemeasurable
  calc
    brownianProductLaw.map (brownianCoordinateProcess t) =
        (brownianProductLaw.map fun omega => I.restrict omega).map
          (fun x => x tI) := by
            rw [Measure.map_map (by fun_prop) hrestrict]
            rfl
    _ = (brownianFiniteDimensionalPiLaw I).map (fun x => x tI) := by
      rw [brownianProductLaw_isProjectiveLimit I]
    _ = gaussianReal 0 |t|.toNNReal := by
      simpa [tI] using
        (brownianFiniteDimensionalPiLaw_measurePreserving_eval I tI).map_eq


theorem brownianCoordinateProcess_start :
    ∀ᵐ omega ∂brownianProductLaw, brownianCoordinateProcess 0 omega = 0 := by
  have hmap : brownianProductLaw.map (brownianCoordinateProcess 0) =
      Measure.dirac 0 := by
    simpa [gaussianReal_zero_var] using
      (brownianCoordinateProcess_eval_law 0).map_eq
  have hdirac : ∀ᵐ x ∂brownianProductLaw.map
      (brownianCoordinateProcess 0), x = 0 := by
    rw [hmap]
    simp
  exact (ae_map_iff (brownianCoordinateProcess_measurable 0).aemeasurable
    (by measurability)).mp hdirac



theorem brownianFiniteDimensionalPiLaw_indepFun_increments
    (I : Finset Real) (s t u v : I)
    (hst : (s : Real) <= t) (htu : (t : Real) <= u)
    (huv : (u : Real) <= v) :
    IndepFun (fun x : I -> Real => x t - x s)
      (fun x : I -> Real => x v - x u)
      (brownianFiniteDimensionalPiLaw I) := by
  let F : EuclideanSpace Real I -> (I -> Real) := WithLp.ofLp
  let X : EuclideanSpace Real I -> Real := fun x => x t - x s
  let Y : EuclideanSpace Real I -> Real := fun x => x v - x u
  let X' : (I -> Real) -> Real := fun x => x t - x s
  let Y' : (I -> Real) -> Real := fun x => x v - x u
  apply indepFun_of_identDistrib_pair
    (brownianFiniteDimensionalLaw_indepFun_increments I s t u v hst htu huv)
  constructor
  · fun_prop
  · fun_prop
  rw [brownianFiniteDimensionalPiLaw,
    Measure.map_map (by fun_prop)
      (WithLp.measurable_ofLp 2 (I -> Real))]
  rfl



theorem brownianCoordinateProcess_indep_increments
    (s t u v : Real) (hst : s <= t) (htu : t <= u) (huv : u <= v) :
    IndepFun (fun omega =>
        brownianCoordinateProcess t omega - brownianCoordinateProcess s omega)
      (fun omega =>
        brownianCoordinateProcess v omega - brownianCoordinateProcess u omega)
      brownianProductLaw := by
  let I : Finset Real := {s, t, u, v}
  let sI : I := ⟨s, by simp [I]⟩
  let tI : I := ⟨t, by simp [I]⟩
  let uI : I := ⟨u, by simp [I]⟩
  let vI : I := ⟨v, by simp [I]⟩
  let X : (I -> Real) -> Real := fun x => x tI - x sI
  let Y : (I -> Real) -> Real := fun x => x vI - x uI
  let X' : (Real -> Real) -> Real := fun omega =>
    brownianCoordinateProcess t omega - brownianCoordinateProcess s omega
  let Y' : (Real -> Real) -> Real := fun omega =>
    brownianCoordinateProcess v omega - brownianCoordinateProcess u omega
  have hrestrict : Measurable (fun omega : Real -> Real => I.restrict omega) :=
    Finset.measurable_restrict I
  apply indepFun_of_identDistrib_pair
    (brownianFiniteDimensionalPiLaw_indepFun_increments I sI tI uI vI
      (by simpa [sI, tI] using hst) (by simpa [tI, uI] using htu)
      (by simpa [uI, vI] using huv))
  constructor
  · fun_prop
  · exact ((brownianCoordinateProcess_measurable t).sub
        (brownianCoordinateProcess_measurable s)).prodMk
        ((brownianCoordinateProcess_measurable v).sub
          (brownianCoordinateProcess_measurable u)) |>.aemeasurable
  calc
    (brownianFiniteDimensionalPiLaw I).map (fun x => (X x, Y x)) =
        (brownianProductLaw.map fun omega => I.restrict omega).map
          (fun x => (X x, Y x)) := by
            rw [brownianProductLaw_isProjectiveLimit I]
    _ = brownianProductLaw.map (fun omega => (X' omega, Y' omega)) := by
      rw [Measure.map_map (by fun_prop) hrestrict]
      rfl



theorem brownianCoordinateProcess_increment_law (s t : Real) :
    HasLaw (fun omega =>
      brownianCoordinateProcess t omega - brownianCoordinateProcess s omega)
      (gaussianReal 0 |t - s|.toNNReal) brownianProductLaw := by
  let I : Finset Real := {s, t}
  let sI : I := ⟨s, by simp [I]⟩
  let tI : I := ⟨t, by simp [I]⟩
  have hrestrict : Measurable (fun omega : Real -> Real => I.restrict omega) :=
    Finset.measurable_restrict I
  have hincrement : Measurable (fun x : I -> Real => x tI - x sI) := by
    fun_prop
  refine { aemeasurable := ?_, map_eq := ?_ }
  · exact ((brownianCoordinateProcess_measurable t).sub
      (brownianCoordinateProcess_measurable s)).aemeasurable
  calc
    brownianProductLaw.map (fun omega =>
        brownianCoordinateProcess t omega - brownianCoordinateProcess s omega) =
        (brownianProductLaw.map (fun omega => I.restrict omega)).map
          (fun x => x tI - x sI) := by
            rw [Measure.map_map hincrement hrestrict]
            rfl
    _ = (brownianFiniteDimensionalPiLaw I).map
          (fun x => x tI - x sI) := by
            rw [brownianProductLaw_isProjectiveLimit I]
    _ = gaussianReal 0 |t - s|.toNNReal := by
      simpa [sI, tI] using
        (brownianFiniteDimensionalPiLaw_measurePreserving_increment I sI tI).map_eq


theorem integral_norm_increment_pow_four_brownianProductLaw (s t : Real) :
    integral brownianProductLaw (fun omega =>
      norm (brownianCoordinateProcess t omega -
        brownianCoordinateProcess s omega) ^ 4) =
      3 * |t - s| ^ 2 := by
  let I : Finset Real := {s, t}
  let sI : I := ⟨s, by simp [I]⟩
  let tI : I := ⟨t, by simp [I]⟩
  have hrestrict : Measurable (fun omega : Real -> Real => I.restrict omega) :=
    Finset.measurable_restrict I
  calc
    integral brownianProductLaw (fun omega =>
        norm (brownianCoordinateProcess t omega -
          brownianCoordinateProcess s omega) ^ 4) =
        integral (brownianProductLaw.map fun omega => I.restrict omega)
          (fun x => norm (x tI - x sI) ^ 4) := by
            rw [integral_map hrestrict.aemeasurable (by fun_prop)]
            rfl
    _ = integral (brownianFiniteDimensionalPiLaw I)
          (fun x => norm (x tI - x sI) ^ 4) := by
            rw [brownianProductLaw_isProjectiveLimit I]
    _ = 3 * |t - s| ^ 2 := by
      simpa [sI, tI] using
        (integral_norm_increment_pow_four_brownianFiniteDimensionalPiLaw I sI tI)



theorem brownianCoordinateProcess_isKolmogorovProcess :
    IsKolmogorovProcess brownianCoordinateProcess brownianProductLaw 4 2 3 := by
  apply IsKolmogorovProcess.mk_of_secondCountableTopology
  · exact brownianCoordinateProcess_measurable
  · intro s t
    have hint : Integrable (fun omega =>
        norm (brownianCoordinateProcess t omega -
          brownianCoordinateProcess s omega) ^ 4) brownianProductLaw := by
      have hG := brownianCoordinateProcess_isGaussianProcess.hasGaussianLaw_fun_sub
        (s := t) (t := s)
      have hmem : MemLp (fun omega =>
          brownianCoordinateProcess t omega -
            brownianCoordinateProcess s omega) 4 brownianProductLaw :=
        hG.memLp (by norm_num)
      exact hmem.integrable_norm_pow (by norm_num)
    calc
      (∫⁻ omega, edist (brownianCoordinateProcess s omega)
            (brownianCoordinateProcess t omega) ^ (4 : Real)
          ∂brownianProductLaw) =
          ENNReal.ofReal (integral brownianProductLaw (fun omega =>
            norm (brownianCoordinateProcess t omega -
              brownianCoordinateProcess s omega) ^ 4)) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint
          (ae_of_all _ fun _ => by positivity)]
        apply lintegral_congr
        intro omega
        rw [edist_dist]
        simp [Real.dist_eq, Real.norm_eq_abs, abs_sub_comm]
      _ = ENNReal.ofReal (3 * |t - s| ^ 2) := by
        rw [integral_norm_increment_pow_four_brownianProductLaw]
      _ = (3 : NNReal) * edist s t ^ (2 : Real) := by
        rw [edist_dist, Real.dist_eq]
        simp only [abs_sub_comm, sq_abs, Nat.ofNat_nonneg, ENNReal.ofReal_mul,
          ENNReal.ofReal_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat]
        congr 1
        rw [← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]
      _ <= (3 : NNReal) * edist s t ^ (2 : Real) := le_rfl
  · norm_num
  · norm_num

end StatMech.SLE
