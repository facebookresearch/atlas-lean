/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareBoundaryCompactAverage
import Code.Universality.IsingFermionicPhysicalRobinCompatibility
import Mathlib.MeasureTheory.Integral.DominatedConvergence











open Filter Set Topology

namespace StatMech.Universality

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm





theorem PhysicalSplitRobinConsistencyInputs.primitive_tendsto_at_of_incidenceEmbedding
    {N : Nat → Nat} {hN : ∀ k, 0 < N k}
    {Phi : Complex → Complex} {mesh bulkRate layerRate : Nat → Real}
    (H : PhysicalSplitRobinConsistencyInputs
      N hN Phi mesh bulkRate layerRate)
    (lipschitzConstant : NNReal)
    (hPhi : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
    (e : ∀ k, FKIsingSquareInteriorRadialIncidence (N k) (hN k))
    (z : Complex)
    (hembedding : Tendsto
      (fun k ↦ fullSquareScaledVertexEmbedding (N k) (mesh k)
        (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) (e k)))
      atTop (nhds z)) :
    Tendsto
        (fun k ↦
          (fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) (e k)))
        atTop (nhds (Phi z).im) ∧
      Tendsto
        (fun k ↦
          (fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) (e k)))
        atTop (nhds (Phi z).im) := by
  let sample : Nat → Complex := fun k ↦
    fullSquareScaledVertexEmbedding (N k) (mesh k)
      (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) (e k))
  let vertex : Nat → Real := fun k ↦
    (fkIsingSquareBoundaryLayerCoordinateOneForm
        (N k) (hN k)).vertexPrimitive
      (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) (e k))
  let face : Nat → Real := fun k ↦
    (fkIsingSquareBoundaryLayerCoordinateOneForm
        (N k) (hN k)).facePrimitive
      (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) (e k))
  have htarget : Tendsto (fun k ↦ (Phi (sample k)).im)
      atTop (nhds (Phi z).im) :=
    (hPhi.continuous.tendsto z).comp hembedding
  have hvertexError : Tendsto
      (fun k ↦ vertex k - (Phi (sample k)).im) atTop (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro eta heta
    filter_upwards [H.primitive_convergence lipschitzConstant hPhi eta heta]
      with k hk
    simpa [Real.dist_eq, vertex, sample] using (hk (e k)).1
  have hfaceError : Tendsto
      (fun k ↦ face k - (Phi (sample k)).im) atTop (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro eta heta
    filter_upwards [H.primitive_convergence lipschitzConstant hPhi eta heta]
      with k hk
    simpa [Real.dist_eq, face, sample] using (hk (e k)).2
  constructor
  · simpa [vertex] using hvertexError.add htarget
  · simpa [face] using hfaceError.add htarget

end FKIsingSquareBoundaryLayerCoordinateOneForm



theorem isingFermionicEntireSquarePrimitive_tendsto_at
    {F : Nat → Complex → Complex} {f : Complex → Complex}
    (hF : ∀ n, Differentiable Complex (F n))
    (hf : Differentiable Complex f)
    (hlimit : TendstoLocallyUniformlyOn F f atTop Set.univ)
    (z : Complex) :
    Tendsto (fun n ↦ isingFermionicEntireSquarePrimitive (F n) z)
      atTop (nhds (isingFermionicEntireSquarePrimitive f z)) := by
  have hsquare : TendstoLocallyUniformlyOn
      (fun n w ↦ F n w * F n w) (fun w ↦ f w * f w)
      atTop Set.univ := by
    simpa only [pow_two] using hlimit.mul₀ hlimit
      hf.continuous.continuousOn hf.continuous.continuousOn
  have hhorizontal : TendstoUniformlyOn
      (fun n (x : Real) ↦ F n (x : Complex) * F n x)
      (fun x : Real ↦ f x * f x) atTop (Set.uIcc (0 : Real) z.re) := by
    have hcomp : TendstoLocallyUniformlyOn
        (fun n (x : Real) ↦ F n x * F n x)
        (fun x : Real ↦ f x * f x) atTop (Set.uIcc (0 : Real) z.re) :=
      hsquare.comp (t := Set.uIcc (0 : Real) z.re)
      (fun x : Real ↦ (x : Complex))
      (fun _ _ ↦ Set.mem_univ _) Complex.continuous_ofReal.continuousOn
    exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      isCompact_uIcc).mp hcomp
  have hvertical : TendstoUniformlyOn
      (fun n (y : Real) ↦ F n (z.re + y * Complex.I) ^ 2)
      (fun y : Real ↦ f (z.re + y * Complex.I) ^ 2)
      atTop (Set.uIcc (0 : Real) z.im) := by
    have hcomp : TendstoLocallyUniformlyOn
        (fun n (y : Real) ↦ F n (z.re + y * Complex.I) ^ 2)
        (fun y : Real ↦ f (z.re + y * Complex.I) ^ 2)
        atTop (Set.uIcc (0 : Real) z.im) := by
      simpa only [pow_two] using (hsquare.comp
        (t := Set.uIcc (0 : Real) z.im)
        (fun y : Real ↦ z.re + y * Complex.I)
        (fun _ _ ↦ Set.mem_univ _) (by fun_prop))
    exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      isCompact_uIcc).mp hcomp
  have hhorizontalContinuous : ∀ n,
      ContinuousOn (fun x : Real ↦ F n (x : Complex) * F n x)
        (Set.uIcc (0 : Real) z.re) := fun n ↦
    ((hF n).continuous.comp Complex.continuous_ofReal).mul
      ((hF n).continuous.comp Complex.continuous_ofReal) |>.continuousOn
  have hverticalContinuous : ∀ n,
      ContinuousOn (fun y : Real ↦ F n (z.re + y * Complex.I) ^ 2)
        (Set.uIcc (0 : Real) z.im) := fun n ↦ by
    have hpath : Continuous (fun y : Real ↦
        (z.re : Complex) + (y : Complex) * Complex.I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    exact ((hF n).continuous.comp hpath).pow 2 |>.continuousOn
  have hhorizontalIntegral :=
    TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
      (μ := MeasureTheory.volume)
      (Filter.Eventually.of_forall hhorizontalContinuous) hhorizontal
  have hverticalIntegral :=
    TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
      (μ := MeasureTheory.volume)
      (Filter.Eventually.of_forall hverticalContinuous) hvertical
  simpa [isingFermionicEntireSquarePrimitive, Complex.wedgeIntegral,
    pow_two] using hhorizontalIntegral.add
      (hverticalIntegral.const_smul Complex.I)




theorem isingFermionic_dense_primitive_identification_of_finite_scale_values
    {F : Nat → Complex → Complex} {f Phi target : Complex → Complex}
    (hF : ∀ n, Differentiable Complex (F n))
    (hf : Differentiable Complex f)
    (hlimit : TendstoLocallyUniformlyOn F f atTop Set.univ)
    (S : Set Complex) (C : Real)
    (hvalues : ∀ z ∈ S,
      Tendsto (fun n ↦ (isingFermionicEntireSquarePrimitive (F n) z).im)
        atTop (nhds ((Phi z).im + C)))
    (root : Complex)
    (hroot : Tendsto (fun n ↦ F n root) atTop (nhds (target root))) :
    Set.EqOn
        (fun z ↦ (isingFermionicEntireSquarePrimitive f z).im)
        (fun z ↦ (Phi z).im + C) S ∧
      f root = target root := by
  constructor
  · intro z hz
    apply tendsto_nhds_unique
      ((Complex.continuous_im.tendsto _).comp
        (isingFermionicEntireSquarePrimitive_tendsto_at hF hf hlimit z))
      (hvalues z hz)
  · apply tendsto_nhds_unique (hlimit.tendsto_at (Set.mem_univ root)) hroot





theorem isingFermionicEntireSquarePrimitive_im_tendsto_of_discretePrimitive
    {F : Nat → Complex → Complex} {Phi : Complex → Complex}
    (discretePrimitive : Nat → Complex → Real) (C : Real)
    (z : Complex)
    (hcompare : Tendsto
      (fun n ↦ (isingFermionicEntireSquarePrimitive (F n) z).im -
        discretePrimitive n z) atTop (nhds 0))
    (hdiscrete : Tendsto (fun n ↦ discretePrimitive n z)
      atTop (nhds ((Phi z).im + C))) :
    Tendsto
      (fun n ↦ (isingFermionicEntireSquarePrimitive (F n) z).im)
      atTop (nhds ((Phi z).im + C)) := by
  convert hcompare.add hdiscrete using 1 <;> simp




theorem
    fkIsingExpandingBoundarySquare_scalingLimit_of_holder_and_dense_primitiveValues
    (I : fkIsingExpandingBoundarySquareCaratheodoryApproximation.HolderInterpolation)
    (target Phi : Complex → Complex)
    (htarget : DifferentiableOn Complex target
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (htarget_ne : target
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
    (hPhi : DifferentiableOn Complex Phi
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2)
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (E : StatMech.FrontierA.CompactExhaustion
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (S : Set Complex) (hSdense : Dense S) (C : Real)
    (hvalues : ∀ z ∈ S,
      Tendsto
        (fun k ↦
          (isingFermionicEntireSquarePrimitive
            (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant k)
            z).im)
        atTop (nhds ((Phi z).im + C)))
    (hroot : Tendsto
      (fun k ↦
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
          k fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)
      atTop (nhds (target
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.root))) :
    TendstoLocallyUniformlyOn
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
        target atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U ∧
      TendstoLocallyUniformlyOn
        (deriv ∘
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant)
        (deriv target) atTop
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
  apply fkIsingExpandingBoundarySquare_scalingLimit_of_holder_and_dense_primitiveIm
    I target Phi htarget htarget_ne hPhi hPhideriv E
  intro phi psi f hphi hpsi hlimit
  have hfOn : DifferentiableOn Complex f Set.univ :=
    hlimit.differentiableOn
      (Filter.Eventually.of_forall (fun k ↦
        fkIsingExpandingBoundarySquare_normalizedInterpolant_holomorphic
          (phi (psi k)))) isOpen_univ
  have hf : Differentiable Complex f := differentiableOn_univ.mp hfOn
  let F : Nat → Complex → Complex := fun k ↦
    fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
      (phi (psi k))
  have hF : ∀ k, Differentiable Complex (F k) := fun k ↦
    differentiableOn_univ.mp
      (fkIsingExpandingBoundarySquare_normalizedInterpolant_holomorphic
        (phi (psi k)))
  have hvaluesSub : ∀ z ∈ S,
      Tendsto (fun k ↦ (isingFermionicEntireSquarePrimitive (F k) z).im)
        atTop (nhds ((Phi z).im + C)) := by
    intro z hz
    exact (hvalues z hz).comp (hphi.comp hpsi).tendsto_atTop
  have hrootSub : Tendsto
      (fun k ↦ F k fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)
      atTop (nhds (target
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)) :=
    hroot.comp (hphi.comp hpsi).tendsto_atTop
  obtain ⟨hprimitive, hanchor⟩ :=
    isingFermionic_dense_primitive_identification_of_finite_scale_values
      hF hf hlimit S C hvaluesSub
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.root hrootSub
  exact ⟨S, C, hSdense, hprimitive, hanchor⟩





theorem
    fkIsingExpandingBoundarySquare_scalingLimit_of_holder_and_dense_discretePrimitive
    (I : fkIsingExpandingBoundarySquareCaratheodoryApproximation.HolderInterpolation)
    (target Phi : Complex → Complex)
    (htarget : DifferentiableOn Complex target
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (htarget_ne : target
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
    (hPhi : DifferentiableOn Complex Phi
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2)
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (E : StatMech.FrontierA.CompactExhaustion
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (S : Set Complex) (hSdense : Dense S) (C : Real)
    (discretePrimitive : Nat → Complex → Real)
    (hcompare : ∀ z ∈ S, Tendsto
      (fun k ↦
        (isingFermionicEntireSquarePrimitive
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant k)
          z).im - discretePrimitive k z)
      atTop (nhds 0))
    (hdiscrete : ∀ z ∈ S, Tendsto (fun k ↦ discretePrimitive k z)
      atTop (nhds ((Phi z).im + C)))
    (hroot : Tendsto
      (fun k ↦
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
          k fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)
      atTop (nhds (target
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.root))) :
    TendstoLocallyUniformlyOn
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
        target atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U ∧
      TendstoLocallyUniformlyOn
        (deriv ∘
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant)
        (deriv target) atTop
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
  apply
    fkIsingExpandingBoundarySquare_scalingLimit_of_holder_and_dense_primitiveValues
      I target Phi htarget htarget_ne hPhi hPhideriv E S hSdense C
  · intro z hz
    exact isingFermionicEntireSquarePrimitive_im_tendsto_of_discretePrimitive
      discretePrimitive C z (hcompare z hz) (hdiscrete z hz)
  · exact hroot

end

end StatMech.Universality
