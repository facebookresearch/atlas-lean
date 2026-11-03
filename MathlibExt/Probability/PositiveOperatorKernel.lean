/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Markov kernels represented by positive operators

On a compact metrizable Borel space, a positive continuous linear operator on real-valued
continuous functions that fixes `1` is represented by a Markov kernel. The construction uses
`RealRMK.rieszMeasure` pointwise; weak continuity of the resulting probability measures and the
Portmanteau theorem supply the required kernel measurability. The proof-owning existence theorem is
slightly stronger than the headline: continuity of the operator itself is unnecessary when its
codomain is already `C(E, ℝ)`. The continuous-operator theorem remains the public headline wrapper.

The identity and composition results identify the construction with Mathlib's canonical kernel
operations. No separate Feller-semigroup structure is introduced.

## References

* W. Rudin, *Real and Complex Analysis*, Riesz–Markov–Kakutani representation theorem.
* S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Chapter 1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BoundedContinuousFunction CompactlySupported ENNReal ProbabilityTheory

namespace MathlibExt.Probability.PositiveOperatorKernel

section CompactlySupported

variable {E : Type*} [TopologicalSpace E] [CompactSpace E]

/-- On a compact space, a continuous function is canonically compactly supported. -/
private def compactlySupported (f : C(E, ℝ)) : C_c(E, ℝ) :=
  ⟨f, HasCompactSupport.of_compactSpace f⟩

@[simp]
private theorem compactlySupported_toContinuousMap (f : C(E, ℝ)) :
    (compactlySupported f).toContinuousMap = f :=
  rfl

end CompactlySupported

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  [CompactSpace E] [TopologicalSpace.MetrizableSpace E]

/-- The positive functional obtained by evaluating a positive linear map at one state. -/
private def pointFunctional (T : C(E, ℝ) →ₚ[ℝ] C(E, ℝ)) (x : E) : C_c(E, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => T f.toContinuousMap x
      map_add' := fun f g => by
        rw [show (f + g).toContinuousMap = f.toContinuousMap + g.toContinuousMap by ext; rfl,
          map_add]
        rfl
      map_smul' := fun c f => by
        rw [show (c • f).toContinuousMap = c • f.toContinuousMap by ext; rfl, map_smul]
        rfl }
    fun f hf => by
      apply ContinuousMap.le_def.mp (T.map_nonneg ?_) x
      exact ContinuousMap.le_def.mpr fun y => hf y

/-- The Riesz measure representing evaluation of `T` at one state. -/
private noncomputable def pointMeasure (T : C(E, ℝ) →ₚ[ℝ] C(E, ℝ)) (x : E) : Measure E :=
  RealRMK.rieszMeasure (pointFunctional T x)

/-- The pointwise Riesz measure represents `T` on every continuous function. -/
private theorem integral_pointMeasure (T : C(E, ℝ) →ₚ[ℝ] C(E, ℝ)) (f : C(E, ℝ)) (x : E) :
    ∫ y, f y ∂pointMeasure T x = T f x := by
  rw [pointMeasure]
  convert RealRMK.integral_rieszMeasure (pointFunctional T x) (compactlySupported f) using 1 <;>
    rfl

/-- Unitality normalizes every pointwise Riesz measure to total mass one. -/
private theorem isProbabilityMeasure_pointMeasure (T : C(E, ℝ) →ₚ[ℝ] C(E, ℝ))
    (hT : T 1 = 1) (x : E) : IsProbabilityMeasure (pointMeasure T x) := by
  rw [isProbabilityMeasure_iff_real]
  simpa [hT] using integral_pointMeasure T (1 : C(E, ℝ)) x

/-- The pointwise Riesz measure, bundled as a probability measure. -/
private noncomputable def pointProbabilityMeasure (T : C(E, ℝ) →ₚ[ℝ] C(E, ℝ))
    (hT : T 1 = 1) (x : E) : ProbabilityMeasure E :=
  ⟨pointMeasure T x, isProbabilityMeasure_pointMeasure T hT x⟩

/-- The representing probability measure depends weakly continuously on the state. -/
private theorem continuous_pointProbabilityMeasure (T : C(E, ℝ) →ₚ[ℝ] C(E, ℝ))
    (hT : T 1 = 1) : Continuous (pointProbabilityMeasure T hT) := by
  refine ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr fun f => ?_
  have hfun : (fun x => ∫ y, f y ∂(pointProbabilityMeasure T hT x : Measure E)) = T f := by
    funext x
    simpa [pointProbabilityMeasure] using integral_pointMeasure T f x
  rw [hfun]
  exact (T f).continuous

/-- The family of pointwise Riesz measures is measurable in the Giry measurable space. -/
private theorem measurable_pointMeasure (T : C(E, ℝ) →ₚ[ℝ] C(E, ℝ)) (hT : T 1 = 1) :
    Measurable (pointMeasure T) := by
  let _ (x : E) : IsProbabilityMeasure (pointMeasure T x) :=
    isProbabilityMeasure_pointMeasure T hT x
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (S := {s : Set E | IsClosed s})
  · exact BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed
  · exact isPiSystem_isClosed
  · intro s hs
    have hsc : UpperSemicontinuous fun x => pointMeasure T x s := by
      rw [upperSemicontinuous_iff_limsup_le]
      intro x
      simpa [pointProbabilityMeasure] using
        ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
          (continuous_pointProbabilityMeasure T hT).continuousAt hs
    exact measurable_of_Iio fun r => (hsc.isOpen_preimage r).measurableSet

/-- A positive unital linear map from `C(E, ℝ)` to itself is represented by a Markov kernel.
Continuity of the operator is unnecessary: each output already belongs to `C(E, ℝ)`. -/
theorem exists_markovKernelOfPositiveLinearMap (T : C(E, ℝ) →ₚ[ℝ] C(E, ℝ))
    (hT : T 1 = 1) :
    ∃ K : Kernel E E, IsMarkovKernel K ∧
      ∀ (f : C(E, ℝ)) (x : E), ∫ y, f y ∂K x = T f x := by
  let K : Kernel E E := ⟨pointMeasure T, measurable_pointMeasure T hT⟩
  refine ⟨K, ⟨fun x => isProbabilityMeasure_pointMeasure T hT x⟩, ?_⟩
  intro f x
  exact integral_pointMeasure T f x

/-- **Positive-operator-to-Markov-kernel bridge.** On a compact metrizable Borel space,
a positive continuous linear operator on `C(E, ℝ)` that fixes `1` is represented by a Markov
kernel. The integral identity holds for every continuous function and every starting state. -/
theorem exists_markovKernelOfPositiveOperator (T : C(E, ℝ) →P[ℝ] C(E, ℝ))
    (hT : T 1 = 1) :
    ∃ K : Kernel E E, IsMarkovKernel K ∧
      ∀ (f : C(E, ℝ)) (x : E), ∫ y, f y ∂K x = T f x := by
  exact exists_markovKernelOfPositiveLinearMap T.toPositiveLinearMap hT

/-- The canonical chosen Markov kernel representing `T`. Its characterization theorem is
`integral_markovKernelOfPositiveOperator`; clients should use that theorem rather than unfold this
definition. -/
noncomputable def markovKernelOfPositiveOperator (T : C(E, ℝ) →P[ℝ] C(E, ℝ))
    (hT : T 1 = 1) : Kernel E E :=
  (exists_markovKernelOfPositiveOperator T hT).choose

/-- The representing kernel has a probability measure at every starting state. -/
noncomputable instance isMarkovKernel_markovKernelOfPositiveOperator
    (T : C(E, ℝ) →P[ℝ] C(E, ℝ)) (hT : T 1 = 1) :
    IsMarkovKernel (markovKernelOfPositiveOperator T hT) :=
  (exists_markovKernelOfPositiveOperator T hT).choose_spec.1

/-- The chosen kernel represents `T` on every real-valued continuous function. -/
@[simp]
theorem integral_markovKernelOfPositiveOperator (T : C(E, ℝ) →P[ℝ] C(E, ℝ))
    (hT : T 1 = 1) (f : C(E, ℝ)) (x : E) :
    ∫ y, f y ∂markovKernelOfPositiveOperator T hT x = T f x :=
  (exists_markovKernelOfPositiveOperator T hT).choose_spec.2 f x

/-- Two Markov kernels on a compact metrizable Borel space are equal when they integrate every
real-valued continuous function equally at every starting state. -/
theorem kernel_ext_of_forall_integral_continuous_eq {K L : Kernel E E}
    [IsMarkovKernel K] [IsMarkovKernel L]
    (h : ∀ (f : C(E, ℝ)) (x : E), ∫ y, f y ∂K x = ∫ y, f y ∂L x) : K = L := by
  apply Kernel.ext
  intro x
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  exact h f.toContinuousMap x

/-- The kernel represented by the identity operator is Mathlib's identity kernel. -/
theorem markovKernelOfPositiveOperator_id :
    markovKernelOfPositiveOperator (PositiveContinuousLinearMap.id ℝ C(E, ℝ)) (by rfl) =
      (Kernel.id : Kernel E E) := by
  apply kernel_ext_of_forall_integral_continuous_eq
  intro f x
  rw [integral_markovKernelOfPositiveOperator, Kernel.id_apply]
  simp

/-- Pointwise form of the identity theorem: every transition measure is Dirac. -/
@[simp]
theorem markovKernelOfPositiveOperator_id_apply (x : E) :
    markovKernelOfPositiveOperator (PositiveContinuousLinearMap.id ℝ C(E, ℝ)) (by rfl) x =
      Measure.dirac x := by
  rw [markovKernelOfPositiveOperator_id, Kernel.id_apply]

/-- Operator composition is represented by canonical kernel composition. The order is reversed:
`T.comp U` acts as `f ↦ T (U f)`, so the represented kernel first uses `K_T` and then `K_U`. -/
theorem markovKernelOfPositiveOperator_comp (T U : C(E, ℝ) →P[ℝ] C(E, ℝ))
    (hT : T 1 = 1) (hU : U 1 = 1) :
    markovKernelOfPositiveOperator (T.comp U) (by
      change T (U 1) = 1
      rw [hU, hT]) =
      markovKernelOfPositiveOperator U hU ∘ₖ markovKernelOfPositiveOperator T hT := by
  apply kernel_ext_of_forall_integral_continuous_eq
  intro f x
  rw [integral_markovKernelOfPositiveOperator]
  have hf : Integrable (fun y => f y)
      ((markovKernelOfPositiveOperator U hU ∘ₖ markovKernelOfPositiveOperator T hT) x) :=
    (compactlySupported f).integrable
  rw [Kernel.integral_comp hf]
  simp_rw [integral_markovKernelOfPositiveOperator]
  rfl

end MathlibExt.Probability.PositiveOperatorKernel
