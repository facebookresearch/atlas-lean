/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate











namespace StatMech.Universality

open Finset SimpleGraph
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section




theorem isingFiniteWeighted_harmonic_approximation_of_layer_barriers
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary layer : V -> Prop)
    (harmonic target bulkBarrier layerBarrier : V -> Real)
    (boundaryError bulkResidual layerResidual bulkBound layerBound : Real)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (hharmonic : IsingFiniteWeightedHarmonicOn
      conductance boundary harmonic)
    (hboundary : forall x, boundary x ->
      |harmonic x - target x| <= boundaryError)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hbulk_nonneg : forall x, 0 <= bulkBarrier x)
    (hlayer_nonneg : forall x, 0 <= layerBarrier x)
    (hbulk_bound : forall x, bulkBarrier x <= bulkBound)
    (hlayer_bound : forall x, layerBarrier x <= layerBound)
    (hbulk_laplacian : forall x, Not (boundary x) ->
      isingFiniteWeightedLaplacian conductance bulkBarrier x <= -1)
    (hlayer_laplacian_nonpos : forall x, Not (boundary x) ->
      isingFiniteWeightedLaplacian conductance layerBarrier x <= 0)
    (hlayer_laplacian : forall x, Not (boundary x) -> layer x ->
      isingFiniteWeightedLaplacian conductance layerBarrier x <= -1)
    (htarget_bulk : forall x, Not (boundary x) -> Not (layer x) ->
      |isingFiniteWeightedLaplacian conductance target x| <= bulkResidual)
    (htarget_layer : forall x, Not (boundary x) -> layer x ->
      |isingFiniteWeightedLaplacian conductance target x| <= layerResidual) :
    forall x, |harmonic x - target x| <=
      boundaryError + bulkResidual * bulkBound + layerResidual * layerBound := by
  let upper : V -> Real := fun x =>
    target x + bulkResidual * bulkBarrier x +
      layerResidual * layerBarrier x + boundaryError
  let lower : V -> Real := fun x =>
    target x - bulkResidual * bulkBarrier x -
      layerResidual * layerBarrier x - boundaryError
  have hupper_super :
      IsingFiniteWeightedSuperharmonicOn conductance boundary upper := by
    intro x hx
    rw [show upper = fun y =>
        ((target y + bulkResidual * bulkBarrier y) +
          layerResidual * layerBarrier y) + boundaryError by rfl,
      isingFiniteWeightedLaplacian_add_const,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_const_mul,
      isingFiniteWeightedLaplacian_const_mul]
    by_cases hxl : layer x
    · have ht := (abs_le.mp (htarget_layer x hx hxl)).2
      have hb := hbulk_laplacian x hx
      have hl := hlayer_laplacian x hx hxl
      nlinarith
    · have ht := (abs_le.mp (htarget_bulk x hx hxl)).2
      have hb := hbulk_laplacian x hx
      have hl := hlayer_laplacian_nonpos x hx
      nlinarith
  have hlower_sub :
      IsingFiniteWeightedSubharmonicOn conductance boundary lower := by
    intro x hx
    rw [show lower = fun y =>
        ((target y + (-bulkResidual) * bulkBarrier y) +
          (-layerResidual) * layerBarrier y) + (-boundaryError) by
          funext y
          dsimp only [lower]
          ring,
      isingFiniteWeightedLaplacian_add_const,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_const_mul,
      isingFiniteWeightedLaplacian_const_mul]
    by_cases hxl : layer x
    · have ht := (abs_le.mp (htarget_layer x hx hxl)).1
      have hb := hbulk_laplacian x hx
      have hl := hlayer_laplacian x hx hxl
      nlinarith
    · have ht := (abs_le.mp (htarget_bulk x hx hxl)).1
      have hb := hbulk_laplacian x hx
      have hl := hlayer_laplacian_nonpos x hx
      nlinarith
  have hupper : forall x, harmonic x <= upper x := by
    apply isingFiniteWeighted_harmonic_le_superharmonic
      G conductance boundary harmonic upper hconductance hpositive hhit
      hharmonic hupper_super
    intro x hx
    have hb := (abs_le.mp (hboundary x hx)).2
    have hq := hbulk_nonneg x
    have hl := hlayer_nonneg x
    dsimp only [upper]
    nlinarith
  have hlower : forall x, lower x <= harmonic x := by
    apply isingFiniteWeighted_subharmonic_le_harmonic
      G conductance boundary lower harmonic hconductance hpositive hhit
      hlower_sub hharmonic
    intro x hx
    have hb := (abs_le.mp (hboundary x hx)).1
    have hq := hbulk_nonneg x
    have hl := hlayer_nonneg x
    dsimp only [lower]
    nlinarith
  intro x
  rw [abs_le]
  have hq := hbulk_bound x
  have hl := hlayer_bound x
  have hu := hupper x
  have hd := hlower x
  dsimp only [upper] at hu
  dsimp only [lower] at hd
  constructor <;> nlinarith

namespace FKIsingSquareBoundaryLayerCoordinateOneForm



noncomputable def vertexGhostLayerBarrier
    (n : Nat) : Option (FKIsingSquareFullVertexNode n) -> Real
  | none => 0
  | some _ => 1 / isingFermionicGhostCoefficient


noncomputable def faceGhostLayerBarrier
    (n : Nat) : Option (FKIsingSquareFullFaceNode n) -> Real
  | none => 0
  | some _ => 1 / isingFermionicGhostCoefficient

theorem vertexGhostLayerBarrier_nonneg (n : Nat) :
    forall x, 0 <= vertexGhostLayerBarrier n x := by
  intro x
  cases x <;> simp [vertexGhostLayerBarrier,
    isingFermionicGhostCoefficient_pos.le]

theorem faceGhostLayerBarrier_nonneg (n : Nat) :
    forall c, 0 <= faceGhostLayerBarrier n c := by
  intro c
  cases c <;> simp [faceGhostLayerBarrier,
    isingFermionicGhostCoefficient_pos.le]

theorem vertexGhostLayerBarrier_le (n : Nat) :
    forall x, vertexGhostLayerBarrier n x <=
      1 / isingFermionicGhostCoefficient := by
  intro x
  cases x <;> simp [vertexGhostLayerBarrier,
    isingFermionicGhostCoefficient_pos.le]

theorem faceGhostLayerBarrier_le (n : Nat) :
    forall c, faceGhostLayerBarrier n c <=
      1 / isingFermionicGhostCoefficient := by
  intro c
  cases c <;> simp [faceGhostLayerBarrier,
    isingFermionicGhostCoefficient_pos.le]

theorem vertexGhostLayerBarrier_laplacian
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    isingFiniteWeightedLaplacian (vertexGhostConductance n)
        (vertexGhostLayerBarrier n) (some x) =
      -(fkIsingSquareFullVertexGhostMultiplicity n x : Real) := by
  change isingFiniteWeightedLaplacian
    (isingFiniteGhostConductance (fkIsingSquareFullVertexGraph n)
      (isingFermionicGhostRate
        (fkIsingSquareFullVertexGhostMultiplicity n)))
    (vertexGhostLayerBarrier n) (some x) = _
  rw [show vertexGhostLayerBarrier n =
      isingFiniteGhostExtension 0
        (fun _ => 1 / isingFermionicGhostCoefficient) by
    funext z
    cases z <;> rfl,
    isingFiniteGhostLaplacian_some]
  simp only [isingFiniteGraphLaplacian]
  simp only [sub_self, Finset.sum_const_zero, zero_add]
  unfold isingFermionicGhostRate
  field_simp [isingFermionicGhostCoefficient_pos.ne']
  ring

theorem faceGhostLayerBarrier_laplacian
    (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    isingFiniteWeightedLaplacian (faceGhostConductance n)
        (faceGhostLayerBarrier n) (some c) =
      -(fkIsingSquareFullFaceGhostMultiplicity n c : Real) := by
  change isingFiniteWeightedLaplacian
    (isingFiniteGhostConductance (fkIsingSquareFullFaceGraph n)
      (isingFermionicGhostRate
        (fkIsingSquareFullFaceGhostMultiplicity n)))
    (faceGhostLayerBarrier n) (some c) = _
  rw [show faceGhostLayerBarrier n =
      isingFiniteGhostExtension 0
        (fun _ => 1 / isingFermionicGhostCoefficient) by
    funext z
    cases z <;> rfl,
    isingFiniteGhostLaplacian_some]
  simp only [isingFiniteGraphLaplacian]
  simp only [sub_self, Finset.sum_const_zero, zero_add]
  unfold isingFermionicGhostRate
  field_simp [isingFermionicGhostCoefficient_pos.ne']
  ring

def vertexGhostLayer (n : Nat) :
    Option (FKIsingSquareFullVertexNode n) -> Prop
  | none => False
  | some x => 0 < fkIsingSquareFullVertexGhostMultiplicity n x

def faceGhostLayer (n : Nat) :
    Option (FKIsingSquareFullFaceNode n) -> Prop
  | none => False
  | some c => 0 < fkIsingSquareFullFaceGhostMultiplicity n c

theorem vertexGhostLayerBarrier_laplacian_nonpos
    (n : Nat) (z : Option (FKIsingSquareFullVertexNode n))
    (hz : Not (vertexDirichletBoundary n z)) :
    isingFiniteWeightedLaplacian (vertexGhostConductance n)
      (vertexGhostLayerBarrier n) z <= 0 := by
  cases z with
  | none => exact False.elim (hz trivial)
  | some x =>
      rw [vertexGhostLayerBarrier_laplacian]
      exact neg_nonpos.mpr (Nat.cast_nonneg _)

theorem faceGhostLayerBarrier_laplacian_nonpos
    (n : Nat) (z : Option (FKIsingSquareFullFaceNode n))
    (hz : Not (faceDirichletBoundary n z)) :
    isingFiniteWeightedLaplacian (faceGhostConductance n)
      (faceGhostLayerBarrier n) z <= 0 := by
  cases z with
  | none => exact False.elim (hz trivial)
  | some c =>
      rw [faceGhostLayerBarrier_laplacian]
      exact neg_nonpos.mpr (Nat.cast_nonneg _)

theorem vertexGhostLayerBarrier_laplacian_le_neg_one
    (n : Nat) (z : Option (FKIsingSquareFullVertexNode n))
    (hz : Not (vertexDirichletBoundary n z))
    (hlayer : vertexGhostLayer n z) :
    isingFiniteWeightedLaplacian (vertexGhostConductance n)
      (vertexGhostLayerBarrier n) z <= -1 := by
  cases z with
  | none => exact False.elim hlayer
  | some x =>
      rw [vertexGhostLayerBarrier_laplacian]
      have hm : (1 : Real) <=
          (fkIsingSquareFullVertexGhostMultiplicity n x : Real) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hlayer))
      linarith

theorem faceGhostLayerBarrier_laplacian_le_neg_one
    (n : Nat) (z : Option (FKIsingSquareFullFaceNode n))
    (hz : Not (faceDirichletBoundary n z))
    (hlayer : faceGhostLayer n z) :
    isingFiniteWeightedLaplacian (faceGhostConductance n)
      (faceGhostLayerBarrier n) z <= -1 := by
  cases z with
  | none => exact False.elim hlayer
  | some c =>
      rw [faceGhostLayerBarrier_laplacian]
      have hm : (1 : Real) <=
          (fkIsingSquareFullFaceGhostMultiplicity n c : Real) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hlayer))
      linarith




theorem vertexDirichlet_target_error_le_split
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullVertexNode n) -> Real)
    (bulkResidual layerResidual : Real)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hbulk : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      fkIsingSquareFullVertexGhostMultiplicity n x = 0 ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance n)
        target (some x)| <= bulkResidual)
    (hlayer : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity n x ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance n)
        target (some x)| <= layerResidual) :
    forall z, |vertexDirichlet n hn z - target z| <=
      vertexBoundaryConsistencyError n hn target +
        bulkResidual * vertexExplicitPoissonBarrierBound n +
        layerResidual * (1 / isingFermionicGhostCoefficient) := by
  apply isingFiniteWeighted_harmonic_approximation_of_layer_barriers
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexGhostLayer n)
    (vertexDirichlet n hn) target
    (vertexExplicitPoissonBarrier n) (vertexGhostLayerBarrier n)
    (vertexBoundaryConsistencyError n hn target)
    bulkResidual layerResidual
    (vertexExplicitPoissonBarrierBound n)
    (1 / isingFermionicGhostCoefficient)
    (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n)
    (vertexDirichlet_harmonicOn n hn)
  · intro z hz
    rw [vertexDirichlet_boundary n hn z hz]
    exact isingFiniteWeightedBoundaryError_bound
      (vertexDirichletBoundary n) (vertexGhostPrimitive n hn) target z hz
  · exact hbulkResidual
  · exact hlayerResidual
  · exact vertexExplicitPoissonBarrier_nonneg n
  · exact vertexGhostLayerBarrier_nonneg n
  · exact vertexExplicitPoissonBarrier_le_bound n
  · exact vertexGhostLayerBarrier_le n
  · exact vertexExplicitPoissonBarrier_laplacian n hn
  · exact vertexGhostLayerBarrier_laplacian_nonpos n
  · exact vertexGhostLayerBarrier_laplacian_le_neg_one n
  · intro z hz hnotLayer
    cases z with
    | none => exact False.elim (hz trivial)
    | some x =>
        apply hbulk x hz
        exact Nat.eq_zero_of_not_pos hnotLayer
  · intro z hz hLayer
    cases z with
    | none => exact False.elim hLayer
    | some x => exact hlayer x hz hLayer


theorem faceDirichlet_target_error_le_split
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullFaceNode n) -> Real)
    (bulkResidual layerResidual : Real)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hbulk : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      fkIsingSquareFullFaceGhostMultiplicity n c = 0 ->
      |isingFiniteWeightedLaplacian (faceGhostConductance n)
        target (some c)| <= bulkResidual)
    (hlayer : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity n c ->
      |isingFiniteWeightedLaplacian (faceGhostConductance n)
        target (some c)| <= layerResidual) :
    forall z, |faceDirichlet n hn z - target z| <=
      faceBoundaryConsistencyError n hn target +
        bulkResidual * faceExplicitPoissonBarrierBound n +
        layerResidual * (1 / isingFermionicGhostCoefficient) := by
  apply isingFiniteWeighted_harmonic_approximation_of_layer_barriers
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceGhostLayer n)
    (faceDirichlet n hn) target
    (faceExplicitPoissonBarrier n) (faceGhostLayerBarrier n)
    (faceBoundaryConsistencyError n hn target)
    bulkResidual layerResidual
    (faceExplicitPoissonBarrierBound n)
    (1 / isingFermionicGhostCoefficient)
    (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n)
    (faceDirichlet_harmonicOn n hn)
  · intro z hz
    rw [faceDirichlet_boundary n hn z hz]
    exact isingFiniteWeightedBoundaryError_bound
      (faceDirichletBoundary n) (faceGhostPrimitive n hn) target z hz
  · exact hbulkResidual
  · exact hlayerResidual
  · exact faceExplicitPoissonBarrier_nonneg n
  · exact faceGhostLayerBarrier_nonneg n
  · exact faceExplicitPoissonBarrier_le_bound n
  · exact faceGhostLayerBarrier_le n
  · exact faceExplicitPoissonBarrier_laplacian n
  · exact faceGhostLayerBarrier_laplacian_nonpos n
  · exact faceGhostLayerBarrier_laplacian_le_neg_one n
  · intro z hz hnotLayer
    cases z with
    | none => exact False.elim (hz trivial)
    | some c =>
        apply hbulk c hz
        exact Nat.eq_zero_of_not_pos hnotLayer
  · intro z hz hLayer
    cases z with
    | none => exact False.elim hLayer
    | some c => exact hlayer c hz hLayer




theorem vertexSampled_target_error_le_split
    (n : Nat) (hn : 0 < n)
    (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex) (bulkResidual layerResidual : Real)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hbulk : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      fkIsingSquareFullVertexGhostMultiplicity n x = 0 ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => (Phi (embedding y)).im) x| <= bulkResidual)
    (hlayer : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity n x ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => (Phi (embedding y)).im) x| <= layerResidual)
    (hfreeTrace : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity n x ->
      (Phi (embedding x)).im = 1) :
    forall z,
      |vertexDirichlet n hn z -
          vertexSampledImaginaryTarget n embedding Phi z| <=
        vertexBoundaryConsistencyError n hn
            (vertexSampledImaginaryTarget n embedding Phi) +
          bulkResidual * vertexExplicitPoissonBarrierBound n +
          layerResidual * (1 / isingFermionicGhostCoefficient) := by
  apply vertexDirichlet_target_error_le_split n hn
    (vertexSampledImaginaryTarget n embedding Phi)
    bulkResidual layerResidual hbulkResidual hlayerResidual
  · intro x hx hzero
    have htarget : vertexSampledImaginaryTarget n embedding Phi =
        isingFiniteGhostExtension 1
          (fun y => (Phi (embedding y)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget]
    unfold vertexGhostConductance
    rw [isingFiniteGhostLaplacian_some]
    simpa [isingFermionicGhostRate, hzero] using hbulk x hx hzero
  · intro x hx hpos
    have htarget : vertexSampledImaginaryTarget n embedding Phi =
        isingFiniteGhostExtension 1
          (fun y => (Phi (embedding y)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget]
    unfold vertexGhostConductance
    rw [isingFiniteGhostLaplacian_some, hfreeTrace x hx hpos]
    simpa using hlayer x hx hpos


theorem faceSampled_target_error_le_split
    (n : Nat) (hn : 0 < n)
    (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex) (bulkResidual layerResidual : Real)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hbulk : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      fkIsingSquareFullFaceGhostMultiplicity n c = 0 ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d => (Phi (embedding d)).im) c| <= bulkResidual)
    (hlayer : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity n c ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d => (Phi (embedding d)).im) c| <= layerResidual)
    (hfreeTrace : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity n c ->
      (Phi (embedding c)).im = 0) :
    forall z,
      |faceDirichlet n hn z -
          faceSampledImaginaryTarget n embedding Phi z| <=
        faceBoundaryConsistencyError n hn
            (faceSampledImaginaryTarget n embedding Phi) +
          bulkResidual * faceExplicitPoissonBarrierBound n +
          layerResidual * (1 / isingFermionicGhostCoefficient) := by
  apply faceDirichlet_target_error_le_split n hn
    (faceSampledImaginaryTarget n embedding Phi)
    bulkResidual layerResidual hbulkResidual hlayerResidual
  · intro c hc hzero
    have htarget : faceSampledImaginaryTarget n embedding Phi =
        isingFiniteGhostExtension 0
          (fun d => (Phi (embedding d)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget]
    unfold faceGhostConductance
    rw [isingFiniteGhostLaplacian_some]
    simpa [isingFermionicGhostRate, hzero] using hbulk c hc hzero
  · intro c hc hpos
    have htarget : faceSampledImaginaryTarget n embedding Phi =
        isingFiniteGhostExtension 0
          (fun d => (Phi (embedding d)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget]
    unfold faceGhostConductance
    rw [isingFiniteGhostLaplacian_some, hfreeTrace c hc hpos]
    simpa using hlayer c hc hpos

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
