/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPrimitiveValueBridge
import Code.Universality.IsingFermionicBoundaryRadialMultiCellRegularity











open Filter Set Topology

namespace StatMech.Universality

noncomputable section



structure FKIsingDenseIncidenceFamily
    (N : Nat -> Nat) (hN : forall k, 0 < N k) (mesh : Nat -> Real) where
  point : Nat -> Complex
  incidence : (j k : Nat) ->
    FKIsingSquareInteriorRadialIncidence (N k) (hN k)
  embedding_tendsto : forall j, Tendsto
    (fun k =>
      FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledVertexEmbedding
        (N k) (mesh k)
      (fkIsingSquareInteriorRadialEndpoint (N k) (hN k)
        (incidence j k))) atTop (nhds (point j))
  dense_range : DenseRange point

namespace FKIsingDenseIncidenceFamily

variable {N : Nat -> Nat} {hN : forall k, 0 < N k}
variable {mesh : Nat -> Real}



def discreteVertexPrimitive
    (D : FKIsingDenseIncidenceFamily N hN mesh) (j k : Nat) : Real :=
  (fkIsingSquareBoundaryLayerCoordinateOneForm
      (N k) (hN k)).vertexPrimitive
    (fkIsingSquareInteriorRadialEndpoint (N k) (hN k)
      (D.incidence j k))



theorem discreteVertexPrimitive_tendsto
    {Phi : Complex -> Complex} {bulkRate layerRate : Nat -> Real}
    (D : FKIsingDenseIncidenceFamily N hN mesh)
    (H : FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs
      N hN Phi mesh bulkRate layerRate)
    (lipschitzConstant : NNReal)
    (hPhi : LipschitzWith lipschitzConstant (fun z => (Phi z).im))
    (j : Nat) :
    Tendsto (fun k => D.discreteVertexPrimitive j k)
      atTop (nhds (Phi (D.point j)).im) := by
  exact
    (H.primitive_tendsto_at_of_incidenceEmbedding lipschitzConstant hPhi
      (D.incidence j) (D.point j) (D.embedding_tendsto j)).1

end FKIsingDenseIncidenceFamily







structure FKIsingDenseIncidencePrimitivePathCompatibility
    {N : Nat -> Nat} {hN : forall k, 0 < N k} {mesh : Nat -> Real}
    (F : Nat -> Complex -> Complex)
    (D : FKIsingDenseIncidenceFamily N hN mesh) where
  steps : Nat -> Nat -> Nat
  stepLength : Nat -> Nat -> Real
  error : Nat -> Nat -> Real
  pathBound : Nat -> Real
  canonicalPath : Nat -> Nat -> Nat -> Real
  discretePath : Nat -> Nat -> Nat -> Real
  canonical_endpoint : forall j k,
    canonicalPath j k (steps j k) =
      (isingFermionicEntireSquarePrimitive (F k) (D.point j)).im
  discrete_endpoint : forall j k,
    discretePath j k (steps j k) = D.discreteVertexPrimitive j k
  base_tendsto : forall j, Tendsto
    (fun k => canonicalPath j k 0 - discretePath j k 0)
      atTop (nhds 0)
  error_tendsto : forall j, Tendsto (error j) atTop (nhds 0)
  error_nonneg : forall j k, 0 <= error j k
  pathBound_nonneg : forall j, 0 <= pathBound j
  path_length_le : forall j k,
    (steps j k : Real) * stepLength j k <= pathBound j
  increment_error : forall j k i, i < steps j k ->
    abs ((canonicalPath j k (i + 1) - canonicalPath j k i) -
      (discretePath j k (i + 1) - discretePath j k i)) <=
        stepLength j k * error j k

namespace FKIsingDenseIncidencePrimitivePathCompatibility

variable {N : Nat -> Nat} {hN : forall k, 0 < N k}
variable {mesh : Nat -> Real} {F : Nat -> Complex -> Complex}
variable {D : FKIsingDenseIncidenceFamily N hN mesh}



theorem tendsto_canonical_sub_discrete
    (P : FKIsingDenseIncidencePrimitivePathCompatibility
      (N := N) (hN := hN) (mesh := mesh) F D) (j : Nat) :
    Tendsto
      (fun k =>
        (isingFermionicEntireSquarePrimitive (F k) (D.point j)).im -
          D.discreteVertexPrimitive j k) atTop (nhds 0) := by
  let gap : Nat -> Nat -> Real := fun k i =>
    P.canonicalPath j k i - P.discretePath j k i
  have hbound : forall k,
      abs (gap k (P.steps j k)) <=
        abs (gap k 0) + P.pathBound j * P.error j k := by
    intro k
    have htel : gap k (P.steps j k) - gap k 0 =
        Finset.sum (Finset.range (P.steps j k))
          (fun i => gap k (i + 1) - gap k i) := by
      rw [Finset.sum_sub_distrib]
      have h := Finset.sum_range_sub' (gap k) (P.steps j k)
      rw [Finset.sum_sub_distrib] at h
      linarith
    calc
      abs (gap k (P.steps j k)) <=
          abs (gap k 0) + abs (gap k (P.steps j k) - gap k 0) := by
        have h := abs_add_le (gap k 0)
          (gap k (P.steps j k) - gap k 0)
        convert h using 1 <;> ring
      _ = abs (gap k 0) +
          abs (Finset.sum (Finset.range (P.steps j k))
            (fun i => gap k (i + 1) - gap k i)) := by rw [htel]
      _ <= abs (gap k 0) +
          Finset.sum (Finset.range (P.steps j k))
            (fun i => abs (gap k (i + 1) - gap k i)) := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ <= abs (gap k 0) +
          Finset.sum (Finset.range (P.steps j k))
            (fun _ => P.stepLength j k * P.error j k) := by
        gcongr with i hi
        have hi' : i < P.steps j k := Finset.mem_range.mp hi
        have hinc := P.increment_error j k i hi'
        dsimp only [gap]
        convert hinc using 1 <;> ring
      _ = abs (gap k 0) +
          (P.steps j k : Real) * P.stepLength j k * P.error j k := by
        simp [mul_assoc]
      _ <= abs (gap k 0) + P.pathBound j * P.error j k := by
        simpa [add_comm] using add_le_add_left
          (mul_le_mul_of_nonneg_right (P.path_length_le j k)
            (P.error_nonneg j k)) (abs (gap k 0))
  have hrhs : Tendsto
      (fun k => abs (gap k 0) + P.pathBound j * P.error j k)
      atTop (nhds 0) := by
    convert (P.base_tendsto j).abs.add
      (tendsto_const_nhds.mul (P.error_tendsto j)) using 1 <;>
      simp [gap]
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  rw [Metric.tendsto_nhds] at hrhs
  filter_upwards [hrhs epsilon hepsilon] with k hk
  rw [Real.dist_eq]
  have hrhsNonneg :
      0 <= abs (gap k 0) + P.pathBound j * P.error j k :=
    add_nonneg (abs_nonneg _) (mul_nonneg (P.pathBound_nonneg j)
      (P.error_nonneg j k))
  simpa [gap, P.canonical_endpoint j k, P.discrete_endpoint j k] using
    lt_of_le_of_lt (hbound k)
      (by simpa [Real.dist_eq, abs_of_nonneg hrhsNonneg] using hk)



theorem canonicalPrimitive_tendsto
    {Phi : Complex -> Complex} {bulkRate layerRate : Nat -> Real}
    (P : FKIsingDenseIncidencePrimitivePathCompatibility
      (N := N) (hN := hN) (mesh := mesh) F D)
    (H : FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs
      N hN Phi mesh bulkRate layerRate)
    (lipschitzConstant : NNReal)
    (hPhi : LipschitzWith lipschitzConstant (fun z => (Phi z).im))
    (j : Nat) :
    Tendsto
      (fun k =>
        (isingFermionicEntireSquarePrimitive (F k) (D.point j)).im)
      atTop (nhds (Phi (D.point j)).im) := by
  convert (P.tendsto_canonical_sub_discrete j).add
    (D.discreteVertexPrimitive_tendsto H lipschitzConstant hPhi j) using 1 <;>
    simp

end FKIsingDenseIncidencePrimitivePathCompatibility



theorem isingFermionicEntireSquarePrimitive_tendsto_at_of_continuous
    {F : Nat -> Complex -> Complex} {f : Complex -> Complex}
    (hF : forall n, Continuous (F n))
    (hf : Continuous f)
    (hlimit : TendstoLocallyUniformlyOn F f atTop Set.univ)
    (z : Complex) :
    Tendsto (fun n => isingFermionicEntireSquarePrimitive (F n) z)
      atTop (nhds (isingFermionicEntireSquarePrimitive f z)) := by
  have hsquare : TendstoLocallyUniformlyOn
      (fun n w => F n w * F n w) (fun w => f w * f w)
      atTop Set.univ := by
    simpa only [pow_two] using hlimit.mul₀ hlimit
      hf.continuousOn hf.continuousOn
  have hhorizontal : TendstoUniformlyOn
      (fun n (x : Real) => F n (x : Complex) * F n x)
      (fun x : Real => f x * f x) atTop (Set.uIcc (0 : Real) z.re) := by
    have hcomp : TendstoLocallyUniformlyOn
        (fun n (x : Real) => F n x * F n x)
        (fun x : Real => f x * f x) atTop (Set.uIcc (0 : Real) z.re) :=
      hsquare.comp (t := Set.uIcc (0 : Real) z.re)
        (fun x : Real => (x : Complex))
        (fun _ _ => Set.mem_univ _) Complex.continuous_ofReal.continuousOn
    exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      isCompact_uIcc).mp hcomp
  have hvertical : TendstoUniformlyOn
      (fun n (y : Real) => F n (z.re + y * Complex.I) ^ 2)
      (fun y : Real => f (z.re + y * Complex.I) ^ 2)
      atTop (Set.uIcc (0 : Real) z.im) := by
    have hcomp : TendstoLocallyUniformlyOn
        (fun n (y : Real) => F n (z.re + y * Complex.I) ^ 2)
        (fun y : Real => f (z.re + y * Complex.I) ^ 2)
        atTop (Set.uIcc (0 : Real) z.im) := by
      simpa only [pow_two] using (hsquare.comp
        (t := Set.uIcc (0 : Real) z.im)
        (fun y : Real => z.re + y * Complex.I)
        (fun _ _ => Set.mem_univ _) (by fun_prop))
    exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      isCompact_uIcc).mp hcomp
  have hhorizontalContinuous : forall n,
      ContinuousOn (fun x : Real => F n (x : Complex) * F n x)
        (Set.uIcc (0 : Real) z.re) := fun n =>
    ((hF n).comp Complex.continuous_ofReal).mul
      ((hF n).comp Complex.continuous_ofReal) |>.continuousOn
  have hverticalContinuous : forall n,
      ContinuousOn (fun y : Real => F n (z.re + y * Complex.I) ^ 2)
        (Set.uIcc (0 : Real) z.im) := fun n => by
    have hpath : Continuous (fun y : Real =>
        (z.re : Complex) + (y : Complex) * Complex.I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    exact ((hF n).comp hpath).pow 2 |>.continuousOn
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



@[simp] theorem isingFermionicEntireSquarePrimitive_neg
    (f : Complex -> Complex) (z : Complex) :
    isingFermionicEntireSquarePrimitive (fun w => -f w) z =
      isingFermionicEntireSquarePrimitive f z := by
  simp [isingFermionicEntireSquarePrimitive]




theorem isingFermionicEntireSquarePrimitive_values_do_not_force_root :
    And (forall z,
      isingFermionicEntireSquarePrimitive (fun _ => (-1 : Complex)) z =
        isingFermionicEntireSquarePrimitive (fun _ => (1 : Complex)) z)
      (¬ Tendsto (fun _ : Nat => (-1 : Complex)) atTop
        (nhds (1 : Complex))) := by
  constructor
  · intro z
    simpa using
      (isingFermionicEntireSquarePrimitive_neg (fun _ => (1 : Complex)) z)
  · intro h
    have hneg : Tendsto (fun _ : Nat => (-1 : Complex)) atTop
        (nhds (-1 : Complex)) := tendsto_const_nhds
    have heq : (-1 : Complex) = 1 := tendsto_nhds_unique hneg h
    norm_num at heq

namespace FKIsingCaratheodoryApproximation





theorem StableFullMedialInterpolation.scalingLimit_of_compactHolder_denseIncidencePaths
    {tangent : forall n,
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.M n -> Complex}
    (I : fkIsingExpandingBoundarySquareCaratheodoryApproximation.StableFullMedialInterpolation
      tangent)
    (Hholder :
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.MeshUniformCompactHolder
        I.interpolant)
    (B : Real) (hanchorBound : forall n,
      norm (I.interpolant n
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.root) <= B)
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {mesh bulkRate layerRate : Nat -> Real}
    (target Phi : Complex -> Complex)
    (D : FKIsingDenseIncidenceFamily N hN mesh)
    (P : FKIsingDenseIncidencePrimitivePathCompatibility
      (N := N) (hN := hN) (mesh := mesh) I.interpolant D)
    (Hrobin :
      FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs
        N hN Phi mesh bulkRate layerRate)
    (lipschitzConstant : NNReal)
    (hPhiLip : LipschitzWith lipschitzConstant (fun z => (Phi z).im))
    (htarget : DifferentiableOn Complex target
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (htarget_ne : target
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
    (hPhi : DifferentiableOn Complex Phi
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z => target z ^ 2)
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (E : StatMech.FrontierA.CompactExhaustion
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hMorera : forall (phi psi : Nat -> Nat) (f : Complex -> Complex),
      StrictMono phi -> StrictMono psi ->
      TendstoLocallyUniformlyOn
        (fun n => I.interpolant (phi (psi n))) f atTop
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.U ->
      Complex.IsConservativeOn f
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hroot : Tendsto
      (fun n => I.interpolant n
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)
      atTop (nhds (target
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.root))) :
    TendstoLocallyUniformlyOn I.interpolant target atTop
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
  apply StableFullMedialInterpolation.scalingLimit_of_tensorTentCompactHolder
    fkIsingExpandingBoundarySquareCaratheodoryApproximation I Hholder B
      hanchorBound target Phi htarget htarget_ne hPhi hPhideriv E
  intro phi psi f hphi hpsi hlimit
  have hfContinuous : Continuous f := continuousOn_univ.mp
    (hlimit.continuousOn (Filter.Frequently.of_forall
      (fun n => I.continuousOn (phi (psi n)))))
  have hfOn : DifferentiableOn Complex f Set.univ :=
    (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn
      isOpen_univ).1
        ⟨hMorera phi psi f hphi hpsi hlimit, hfContinuous.continuousOn⟩
  have hf : Differentiable Complex f := differentiableOn_univ.mp hfOn
  let Fsub : Nat -> Complex -> Complex := fun n =>
    I.interpolant (phi (psi n))
  have hFsub : forall n, Continuous (Fsub n) := fun n =>
    continuousOn_univ.mp (I.continuousOn (phi (psi n)))
  have hprimitiveDense : Set.EqOn
      (fun z => (isingFermionicEntireSquarePrimitive f z).im)
      (fun z => (Phi z).im) (Set.range D.point) := by
    rintro z <;> rintro ⟨j, rfl⟩
    have hcanonicalSub : Tendsto
        (fun n =>
          (isingFermionicEntireSquarePrimitive (Fsub n) (D.point j)).im)
        atTop (nhds (Phi (D.point j)).im) := by
      exact (P.canonicalPrimitive_tendsto Hrobin lipschitzConstant hPhiLip j).comp
        (hphi.comp hpsi).tendsto_atTop
    have hlimitPrimitive : Tendsto
        (fun n =>
          (isingFermionicEntireSquarePrimitive (Fsub n) (D.point j)).im)
        atTop
        (nhds (isingFermionicEntireSquarePrimitive f (D.point j)).im) := by
      exact (Complex.continuous_im.tendsto _).comp
        (isingFermionicEntireSquarePrimitive_tendsto_at_of_continuous
          hFsub hfContinuous (by simpa [Fsub] using hlimit) (D.point j))
    exact tendsto_nhds_unique hlimitPrimitive hcanonicalSub
  have hanchor : f
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.root =
      target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root := by
    apply tendsto_nhds_unique
      (hlimit.tendsto_at (Set.mem_univ _))
    exact hroot.comp (hphi.comp hpsi).tendsto_atTop
  refine ⟨hMorera phi psi f hphi hpsi hlimit,
    isingFermionicEntireSquarePrimitive f, 0,
    (isingFermionicEntireSquarePrimitive_differentiable hf).differentiableOn,
    ?_, ?_, hanchor⟩
  · intro z _hz
    exact (isingFermionicEntireSquarePrimitive_hasDerivAt hf z).deriv
  · intro z _hz
    have hprimitiveDenseZero : Set.EqOn
        (fun w => (isingFermionicEntireSquarePrimitive f w).im)
        (fun w => (Phi w).im + 0) (Set.range D.point) := by
      simpa using hprimitiveDense
    simpa using isingFermionicEntireSquarePrimitive_im_eq_of_dense
      hf (differentiableOn_univ.mp hPhi).continuous (Set.range D.point)
      D.dense_range 0 hprimitiveDenseZero z






theorem BoundaryRadialTensorTentGeometry.scalingLimit_of_compactHolder_denseIncidencePaths
    (G : BoundaryRadialTensorTentGeometry
      fkIsingExpandingBoundarySquareCaratheodoryApproximation)
    (Hholder :
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.MeshUniformCompactHolder
        (BoundaryRadialTensorTentGeometry.interpolant
          fkIsingExpandingBoundarySquareCaratheodoryApproximation G))
    (B : Real) (hanchorBound : forall n,
      norm (BoundaryRadialTensorTentGeometry.interpolant
        fkIsingExpandingBoundarySquareCaratheodoryApproximation G n
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.root) <= B)
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {mesh bulkRate layerRate : Nat -> Real}
    (target Phi : Complex -> Complex)
    (D : FKIsingDenseIncidenceFamily N hN mesh)
    (P : FKIsingDenseIncidencePrimitivePathCompatibility
      (N := N) (hN := hN) (mesh := mesh)
      (BoundaryRadialTensorTentGeometry.interpolant
        fkIsingExpandingBoundarySquareCaratheodoryApproximation G) D)
    (Hrobin :
      FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs
        N hN Phi mesh bulkRate layerRate)
    (lipschitzConstant : NNReal)
    (hPhiLip : LipschitzWith lipschitzConstant (fun z => (Phi z).im))
    (htarget : DifferentiableOn Complex target
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (htarget_ne : target
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
    (hPhi : DifferentiableOn Complex Phi
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z => target z ^ 2)
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (E : StatMech.FrontierA.CompactExhaustion
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hMorera : forall (phi psi : Nat -> Nat) (f : Complex -> Complex),
      StrictMono phi -> StrictMono psi ->
      TendstoLocallyUniformlyOn
        (fun n => BoundaryRadialTensorTentGeometry.interpolant
          fkIsingExpandingBoundarySquareCaratheodoryApproximation G
            (phi (psi n))) f atTop
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.U ->
      Complex.IsConservativeOn f
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hroot : Tendsto
      (fun n => BoundaryRadialTensorTentGeometry.interpolant
        fkIsingExpandingBoundarySquareCaratheodoryApproximation G n
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)
      atTop (nhds (target
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.root))) :
    TendstoLocallyUniformlyOn
      (BoundaryRadialTensorTentGeometry.interpolant
        fkIsingExpandingBoundarySquareCaratheodoryApproximation G)
      target atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
  let I := BoundaryRadialTensorTentGeometry.toStableFullMedialInterpolationCompact
    fkIsingExpandingBoundarySquareCaratheodoryApproximation G Hholder
  exact StableFullMedialInterpolation.scalingLimit_of_compactHolder_denseIncidencePaths
    I Hholder B hanchorBound target Phi D P Hrobin lipschitzConstant hPhiLip
      htarget htarget_ne hPhi hPhideriv E hMorera hroot

end FKIsingCaratheodoryApproximation

end

end StatMech.Universality
