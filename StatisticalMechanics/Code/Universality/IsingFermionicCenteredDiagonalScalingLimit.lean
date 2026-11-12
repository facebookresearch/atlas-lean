/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicCenteredFourSectorAssembly
import Code.Universality.IsingFermionicCenteredRootReduction
import Code.Universality.IsingFermionicConcreteMorera
import Code.Universality.IsingFermionicDenseIncidenceRootBound
import Code.Universality.IsingFermionicCenteredTVRoot
import Code.Universality.IsingFermionicCanonicalDenseIncidence










open Filter Set Topology

namespace StatMech.Universality

noncomputable section

namespace FKIsingCaratheodoryApproximation




theorem
    scalingLimit_of_continuous_compactHolder_denseIncidencePaths_of_root_tendsto
    (F : Nat → Complex → Complex)
    (hcontinuous : ∀ n, Continuous (F n))
    (Hholder :
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.MeshUniformCompactHolder
        F)
    {N : Nat → Nat} {hN : ∀ k, 0 < N k}
    {mesh bulkRate layerRate : Nat → Real}
    (target Phi : Complex → Complex)
    (D : FKIsingDenseIncidenceFamily N hN mesh)
    (P : FKIsingDenseIncidencePrimitivePathCompatibility
      (N := N) (hN := hN) (mesh := mesh) F D)
    (Hrobin :
      FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs
        N hN Phi mesh bulkRate layerRate)
    (lipschitzConstant : NNReal)
    (hPhiLip : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
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
    (hMorera : ∀ (phi psi : Nat → Nat) (f : Complex → Complex),
      StrictMono phi → StrictMono psi →
      TendstoLocallyUniformlyOn
        (fun n ↦ F (phi (psi n))) f atTop
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.U →
      Complex.IsConservativeOn f
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hroot : Tendsto
      (fun n ↦ F n
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)
      atTop (nhds (target
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.root))) :
    TendstoLocallyUniformlyOn F target atTop
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
  let A := fkIsingExpandingBoundarySquareCaratheodoryApproximation
  let u : Nat → Complex := fun n ↦ F n A.root
  have hu : Tendsto u atTop (nhds (target A.root)) := by
    simpa [A, u] using hroot
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto u hu).subset_closedBall 0
  have hanchorBound : ∀ n, norm (F n A.root) ≤ B := by
    intro n
    have hn := hB (show u n ∈ Set.range u from ⟨n, rfl⟩)
    rw [Metric.mem_closedBall] at hn
    simpa [u, dist_eq_norm] using hn
  have hbounded : ∀ K : Set Complex, IsCompact K → K ⊆ A.U →
      ∃ C : Real, ∀ n z, z ∈ K → norm (F n z) ≤ C := by
    intro K hK hKU
    let K' : Set Complex := insert A.root K
    have hK' : IsCompact K' := hK.insert A.root
    have hK'U : K' ⊆ A.U := by
      intro z hz
      rcases hz with rfl | hz
      · exact A.root_mem
      · exact hKU hz
    obtain ⟨C, alpha, _halpha, hholder⟩ := Hholder.holder K' hK' hK'U
    have hdistContinuous : Continuous (fun z : Complex ↦ dist z A.root) :=
      continuous_id.dist continuous_const
    obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn
      hdistContinuous.continuousOn
    refine ⟨B + (C : Real) * R ^ (alpha : Real), ?_⟩
    intro n z hz
    have hz' : z ∈ K' := Or.inr hz
    have hroot' : A.root ∈ K' := Or.inl rfl
    calc
      norm (F n z) ≤ norm (F n A.root) + norm (F n z - F n A.root) :=
        norm_le_norm_add_norm_sub' _ _
      _ = norm (F n A.root) + dist (F n z) (F n A.root) := by
        rw [dist_eq_norm]
      _ ≤ B + (C : Real) * dist z A.root ^ (alpha : Real) :=
        add_le_add (hanchorBound n) ((hholder n).dist_le hz' hroot')
      _ ≤ B + (C : Real) * R ^ (alpha : Real) := by
        gcongr
        simpa [Real.norm_of_nonneg dist_nonneg] using hR z hz
  have hcompact :
      StatMech.FrontierA.IsLocallyUniformlySequentiallyPrecompact F A.U :=
    StatMech.FrontierA.equicontinuousFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion
      F A.U A.isOpen
      (fun K hK hKU ↦
        MeshUniformCompactHolder.equicontinuousOn A Hholder K hK hKU)
      hbounded E
  apply StatMech.FrontierA.tendstoLocallyUniformlyOn_of_subsequential_limits_unique
    F target A.U A.isOpen hcompact
  intro phi psi f hphi hpsi hlimit
  have hfContinuous : Continuous f := continuousOn_univ.mp
    (hlimit.continuousOn (Filter.Frequently.of_forall
      (fun n ↦ (hcontinuous (phi (psi n))).continuousOn)))
  have hfOn : DifferentiableOn Complex f Set.univ :=
    (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn
      isOpen_univ).1
        ⟨hMorera phi psi f hphi hpsi hlimit, hfContinuous.continuousOn⟩
  have hf : Differentiable Complex f := differentiableOn_univ.mp hfOn
  let Fsub : Nat → Complex → Complex := fun n ↦ F (phi (psi n))
  have hFsub : ∀ n, Continuous (Fsub n) := fun n ↦
    hcontinuous (phi (psi n))
  have hprimitiveDense : Set.EqOn
      (fun z ↦ (isingFermionicEntireSquarePrimitive f z).im)
      (fun z ↦ (Phi z).im) (Set.range D.point) := by
    rintro z ⟨j, rfl⟩
    have hcanonicalSub : Tendsto
        (fun n ↦
          (isingFermionicEntireSquarePrimitive (Fsub n) (D.point j)).im)
        atTop (nhds (Phi (D.point j)).im) := by
      exact (P.canonicalPrimitive_tendsto Hrobin lipschitzConstant hPhiLip j).comp
        (hphi.comp hpsi).tendsto_atTop
    have hlimitPrimitive : Tendsto
        (fun n ↦
          (isingFermionicEntireSquarePrimitive (Fsub n) (D.point j)).im)
        atTop
        (nhds (isingFermionicEntireSquarePrimitive f (D.point j)).im) := by
      exact (Complex.continuous_im.tendsto _).comp
        (isingFermionicEntireSquarePrimitive_tendsto_at_of_continuous
          hFsub hfContinuous (by simpa [Fsub] using hlimit) (D.point j))
    exact tendsto_nhds_unique hlimitPrimitive hcanonicalSub
  have hanchor : f A.root = target A.root := by
    apply tendsto_nhds_unique (hlimit.tendsto_at A.root_mem)
    exact hu.comp (hphi.comp hpsi).tendsto_atTop
  have him : ∀ z ∈ A.U,
      (isingFermionicEntireSquarePrimitive f z).im = (Phi z).im + 0 := by
    intro z _hz
    have hprimitiveDenseZero : Set.EqOn
        (fun w ↦ (isingFermionicEntireSquarePrimitive f w).im)
        (fun w ↦ (Phi w).im + 0) (Set.range D.point) := by
      simpa using hprimitiveDense
    simpa using isingFermionicEntireSquarePrimitive_im_eq_of_dense
      hf (differentiableOn_univ.mp hPhi).continuous (Set.range D.point)
      D.dense_range 0 hprimitiveDenseZero z
  have hsquare := isingFermionic_square_eq_of_primitive_im_eq
    f target (isingFermionicEntireSquarePrimitive f) Phi A.U A.root 0
    A.isOpen A.isPreconnected A.root_mem
    (isingFermionicEntireSquarePrimitive_differentiable hf).differentiableOn
    hPhi (fun z _hz ↦ (isingFermionicEntireSquarePrimitive_hasDerivAt hf z).deriv)
    hPhideriv him
  exact isingFermionic_squareRoot_unique_of_anchor
    f target A.U A.root A.isOpen A.isPreconnected A.root_mem
    hf.differentiableOn htarget hsquare hanchor htarget_ne




theorem scalingLimit_of_centeredFourSectorDiagonal_denseIncidencePaths
    (L : NNReal) (N0 : Nat) (hN0 : 1 ≤ N0)
    (hdiag : ∀ q : Fin 4, ∀ k, N0 ≤ k → ∀ i j,
      isingCenteredRadialIndexSector
          (fkIsingExpandingSquareSide k) i j = q →
        FKIsingExpandingCenteredDiagonalCellBound L k i j)
    {N : Nat → Nat} {hN : ∀ k, 0 < N k}
    {mesh bulkRate layerRate : Nat → Real}
    (target Phi : Complex → Complex)
    (D : FKIsingDenseIncidenceFamily N hN mesh)
    (P : FKIsingDenseIncidencePrimitivePathCompatibility
      (N := N) (hN := hN) (mesh := mesh)
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant D)
    (Hrobin :
      FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs
        N hN Phi mesh bulkRate layerRate)
    (lipschitzConstant : NNReal)
    (hPhiLip : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
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
    (hbase : Tendsto
      (fun k ↦ fkIsingExpandingBoundarySquareCenteredRootNode k 0 0)
      atTop (nhds (target 0))) :
    TendstoLocallyUniformlyOn
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant target atTop
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
  have hstrict : FKIsingExpandingCenteredStrictNeighborTransport :=
    fkIsingExpandingCenteredStrictNeighborTransport_of_four_sector_diagonal
      L N0 hN0 hdiag
  have Hholder :=
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_meshUniformCompactHolder_of_centeredStrictNeighbor
      hstrict
  have hroot :=
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_root_tendsto_of_centeredStrictNeighbor
      target hstrict hbase
  have hMorera : ∀ (phi psi : Nat → Nat) (f : Complex → Complex),
      StrictMono phi → StrictMono psi →
      TendstoLocallyUniformlyOn
        (fun n ↦ fkIsingExpandingBoundarySquareCenteredReflectedInterpolant
          (phi (psi n))) f atTop
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.U →
      Complex.IsConservativeOn f
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
    intro phi psi f hphi hpsi hlimit
    have hlimit' : TendstoLocallyUniformlyOn
        (fun n ↦ fkIsingExpandingBoundarySquareCenteredReflectedInterpolant
          (phi (psi n))) f atTop Set.univ := by
      simpa [fkIsingExpandingBoundarySquareCaratheodoryApproximation] using hlimit
    have hf :=
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_isConservativeOn_subsequentialLimit
        (hphi.comp hpsi).tendsto_atTop hlimit'
    simpa [fkIsingExpandingBoundarySquareCaratheodoryApproximation] using hf
  exact scalingLimit_of_continuous_compactHolder_denseIncidencePaths_of_root_tendsto
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_continuous
    Hholder target Phi D P Hrobin lipschitzConstant hPhiLip htarget
    htarget_ne hPhi hPhideriv E hMorera hroot




theorem scalingLimit_of_centeredFullCarrierTV_denseIncidencePaths
    {N : Nat → Nat} {hN : ∀ k, 0 < N k}
    {mesh bulkRate layerRate : Nat → Real}
    (target Phi : Complex → Complex)
    (D : FKIsingDenseIncidenceFamily N hN mesh)
    (P : FKIsingDenseIncidencePrimitivePathCompatibility
      (N := N) (hN := hN) (mesh := mesh)
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant D)
    (Hrobin :
      FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs
        N hN Phi mesh bulkRate layerRate)
    (lipschitzConstant : NNReal)
    (hPhiLip : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
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
    (hbase : Tendsto
      (fun k ↦ fkIsingExpandingBoundarySquareCenteredRootNode k 0 0)
      atTop (nhds (target 0))) :
    TendstoLocallyUniformlyOn
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant target atTop
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
  have Hholder :=
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_meshUniformCompactHolder_fullCarrierTV
  have hroot :=
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_root_tendsto_fullCarrierTV
      target hbase
  have hMorera : ∀ (phi psi : Nat → Nat) (f : Complex → Complex),
      StrictMono phi → StrictMono psi →
      TendstoLocallyUniformlyOn
        (fun n ↦ fkIsingExpandingBoundarySquareCenteredReflectedInterpolant
          (phi (psi n))) f atTop
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.U →
      Complex.IsConservativeOn f
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
    intro phi psi f hphi hpsi hlimit
    have hlimit' : TendstoLocallyUniformlyOn
        (fun n ↦ fkIsingExpandingBoundarySquareCenteredReflectedInterpolant
          (phi (psi n))) f atTop Set.univ := by
      simpa [fkIsingExpandingBoundarySquareCaratheodoryApproximation] using hlimit
    have hf :=
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_isConservativeOn_subsequentialLimit
        (hphi.comp hpsi).tendsto_atTop hlimit'
    simpa [fkIsingExpandingBoundarySquareCaratheodoryApproximation] using hf
  exact scalingLimit_of_continuous_compactHolder_denseIncidencePaths_of_root_tendsto
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_continuous
    Hholder target Phi D P Hrobin lipschitzConstant hPhiLip htarget
    htarget_ne hPhi hPhideriv E hMorera hroot






theorem scalingLimit_of_centeredFullCarrierTV_canonicalRationalPaths
    {bulkRate layerRate : Nat → Real}
    (target Phi : Complex → Complex)
    (L : FKIsingCanonicalDensePrimitiveLocalInputs
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant)
    (Hrobin :
      FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs
        fkIsingExpandingSquareSide fkIsingExpandingSquareSide_pos Phi
        fkIsingExpandingSquareScale bulkRate layerRate)
    (lipschitzConstant : NNReal)
    (hPhiLip : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
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
    (hbase : Tendsto
      (fun k ↦ fkIsingExpandingBoundarySquareCenteredRootNode k 0 0)
      atTop (nhds (target 0))) :
    TendstoLocallyUniformlyOn
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant target atTop
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
  exact scalingLimit_of_centeredFullCarrierTV_denseIncidencePaths
    target Phi fkIsingExpandingSquareDenseIncidenceFamily
    L.toPathCompatibility Hrobin lipschitzConstant hPhiLip htarget
    htarget_ne hPhi hPhideriv E hbase

end FKIsingCaratheodoryApproximation

end

end StatMech.Universality
