/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalRobinCompatibility













namespace StatMech.Universality

open Finset SimpleGraph Filter Metric Set Topology
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section




noncomputable def isingFiniteWeightedLocalizedPoissonBarrier
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary exceptional : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b) : V -> Real := by
  classical
  exact isingFiniteWeightedDirichletSolve G conductance boundary
    hconductance hpositive hhit
    (fun x => if boundary x then 0 else if exceptional x then -1 else 0)

theorem isingFiniteWeightedLocalizedPoissonBarrier_boundary
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary exceptional : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (x : V) (hx : boundary x) :
    isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
      exceptional hconductance hpositive hhit x = 0 := by
  classical
  have h := congrFun (isingFiniteWeightedDirichletOperator_solve
    G conductance boundary hconductance hpositive hhit
    (fun y => if boundary y then 0 else if exceptional y then -1 else 0)) x
  change (if boundary x then
      isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
        exceptional hconductance hpositive hhit x else
      isingFiniteWeightedLaplacian conductance
        (isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
          exceptional hconductance hpositive hhit) x) =
    (if boundary x then 0 else if exceptional x then -1 else 0) at h
  simpa [hx] using h

theorem isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_mem
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary exceptional : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (x : V) (hx : Not (boundary x)) (hxe : exceptional x) :
    isingFiniteWeightedLaplacian conductance
      (isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
        exceptional hconductance hpositive hhit) x = -1 := by
  classical
  have h := congrFun (isingFiniteWeightedDirichletOperator_solve
    G conductance boundary hconductance hpositive hhit
    (fun y => if boundary y then 0 else if exceptional y then -1 else 0)) x
  change (if boundary x then
      isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
        exceptional hconductance hpositive hhit x else
      isingFiniteWeightedLaplacian conductance
        (isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
          exceptional hconductance hpositive hhit) x) =
    (if boundary x then 0 else if exceptional x then -1 else 0) at h
  simpa [hx, hxe] using h

theorem isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_not_mem
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary exceptional : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (x : V) (hx : Not (boundary x)) (hxe : Not (exceptional x)) :
    isingFiniteWeightedLaplacian conductance
      (isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
        exceptional hconductance hpositive hhit) x = 0 := by
  classical
  have h := congrFun (isingFiniteWeightedDirichletOperator_solve
    G conductance boundary hconductance hpositive hhit
    (fun y => if boundary y then 0 else if exceptional y then -1 else 0)) x
  change (if boundary x then
      isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
        exceptional hconductance hpositive hhit x else
      isingFiniteWeightedLaplacian conductance
        (isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
          exceptional hconductance hpositive hhit) x) =
    (if boundary x then 0 else if exceptional x then -1 else 0) at h
  simpa [hx, hxe] using h

theorem isingFiniteWeightedLocalizedPoissonBarrier_nonneg
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary exceptional : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b) :
    forall x, 0 <= isingFiniteWeightedLocalizedPoissonBarrier G conductance
      boundary exceptional hconductance hpositive hhit x := by
  apply isingFiniteWeighted_const_le_superharmonic
    G conductance boundary
    (isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
      exceptional hconductance hpositive hhit) 0
    hconductance hpositive hhit
  · intro x hx
    by_cases hxe : exceptional x
    · rw [isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_mem
        G conductance boundary exceptional hconductance hpositive hhit x hx hxe]
      norm_num
    · rw [isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_not_mem
        G conductance boundary exceptional hconductance hpositive hhit x hx hxe]
  · intro x hx
    rw [isingFiniteWeightedLocalizedPoissonBarrier_boundary
      G conductance boundary exceptional hconductance hpositive hhit x hx]





theorem isingFiniteWeighted_harmonic_approximation_of_endpoint_barriers
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary layer exceptional : V -> Prop)
    (harmonic target bulkBarrier layerBarrier endpointBarrier : V -> Real)
    (boundaryError bulkResidual layerResidual endpointResidual : Real)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (hharmonic : IsingFiniteWeightedHarmonicOn
      conductance boundary harmonic)
    (hboundary : forall x, boundary x ->
      |harmonic x - target x| <= boundaryError)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hendpointResidual : 0 <= endpointResidual)
    (hbulk_nonneg : forall x, 0 <= bulkBarrier x)
    (hlayer_nonneg : forall x, 0 <= layerBarrier x)
    (hendpoint_nonneg : forall x, 0 <= endpointBarrier x)
    (hbulk_laplacian : forall x, Not (boundary x) ->
      isingFiniteWeightedLaplacian conductance bulkBarrier x <= -1)
    (hlayer_laplacian_nonpos : forall x, Not (boundary x) ->
      isingFiniteWeightedLaplacian conductance layerBarrier x <= 0)
    (hlayer_laplacian : forall x, Not (boundary x) -> layer x ->
      isingFiniteWeightedLaplacian conductance layerBarrier x <= -1)
    (hendpoint_laplacian_nonpos : forall x, Not (boundary x) ->
      isingFiniteWeightedLaplacian conductance endpointBarrier x <= 0)
    (hendpoint_laplacian : forall x, Not (boundary x) -> exceptional x ->
      isingFiniteWeightedLaplacian conductance endpointBarrier x <= -1)
    (htarget_bulk : forall x, Not (boundary x) -> Not (layer x) ->
      Not (exceptional x) ->
      |isingFiniteWeightedLaplacian conductance target x| <= bulkResidual)
    (htarget_layer : forall x, Not (boundary x) -> layer x ->
      Not (exceptional x) ->
      |isingFiniteWeightedLaplacian conductance target x| <= layerResidual)
    (htarget_endpoint : forall x, Not (boundary x) -> exceptional x ->
      |isingFiniteWeightedLaplacian conductance target x| <= endpointResidual) :
    forall x, |harmonic x - target x| <= boundaryError +
      bulkResidual * bulkBarrier x + layerResidual * layerBarrier x +
        endpointResidual * endpointBarrier x := by
  let upper : V -> Real := fun x =>
    target x + bulkResidual * bulkBarrier x +
      layerResidual * layerBarrier x +
        endpointResidual * endpointBarrier x + boundaryError
  let lower : V -> Real := fun x =>
    target x - bulkResidual * bulkBarrier x -
      layerResidual * layerBarrier x -
        endpointResidual * endpointBarrier x - boundaryError
  have hupper_super :
      IsingFiniteWeightedSuperharmonicOn conductance boundary upper := by
    intro x hx
    rw [show upper = fun y =>
        ((((target y + bulkResidual * bulkBarrier y) +
          layerResidual * layerBarrier y) +
          endpointResidual * endpointBarrier y) + boundaryError) by rfl,
      isingFiniteWeightedLaplacian_add_const,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_const_mul,
      isingFiniteWeightedLaplacian_const_mul,
      isingFiniteWeightedLaplacian_const_mul]
    by_cases hxe : exceptional x
    · have ht := (abs_le.mp (htarget_endpoint x hx hxe)).2
      have hb := hbulk_laplacian x hx
      have hl := hlayer_laplacian_nonpos x hx
      have he := hendpoint_laplacian x hx hxe
      nlinarith
    · by_cases hxl : layer x
      · have ht := (abs_le.mp (htarget_layer x hx hxl hxe)).2
        have hb := hbulk_laplacian x hx
        have hl := hlayer_laplacian x hx hxl
        have he := hendpoint_laplacian_nonpos x hx
        nlinarith
      · have ht := (abs_le.mp (htarget_bulk x hx hxl hxe)).2
        have hb := hbulk_laplacian x hx
        have hl := hlayer_laplacian_nonpos x hx
        have he := hendpoint_laplacian_nonpos x hx
        nlinarith
  have hlower_sub :
      IsingFiniteWeightedSubharmonicOn conductance boundary lower := by
    intro x hx
    rw [show lower = fun y =>
        ((((target y + (-bulkResidual) * bulkBarrier y) +
          (-layerResidual) * layerBarrier y) +
          (-endpointResidual) * endpointBarrier y) + (-boundaryError)) by
          funext y
          dsimp only [lower]
          ring,
      isingFiniteWeightedLaplacian_add_const,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_const_mul,
      isingFiniteWeightedLaplacian_const_mul,
      isingFiniteWeightedLaplacian_const_mul]
    by_cases hxe : exceptional x
    · have ht := (abs_le.mp (htarget_endpoint x hx hxe)).1
      have hb := hbulk_laplacian x hx
      have hl := hlayer_laplacian_nonpos x hx
      have he := hendpoint_laplacian x hx hxe
      nlinarith
    · by_cases hxl : layer x
      · have ht := (abs_le.mp (htarget_layer x hx hxl hxe)).1
        have hb := hbulk_laplacian x hx
        have hl := hlayer_laplacian x hx hxl
        have he := hendpoint_laplacian_nonpos x hx
        nlinarith
      · have ht := (abs_le.mp (htarget_bulk x hx hxl hxe)).1
        have hb := hbulk_laplacian x hx
        have hl := hlayer_laplacian_nonpos x hx
        have he := hendpoint_laplacian_nonpos x hx
        nlinarith
  have hupper : forall x, harmonic x <= upper x := by
    apply isingFiniteWeighted_harmonic_le_superharmonic
      G conductance boundary harmonic upper hconductance hpositive hhit
      hharmonic hupper_super
    intro x hx
    have hb := (abs_le.mp (hboundary x hx)).2
    have hq := hbulk_nonneg x
    have hl := hlayer_nonneg x
    have he := hendpoint_nonneg x
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
    have he := hendpoint_nonneg x
    dsimp only [lower]
    nlinarith
  intro x
  rw [abs_le]
  have hu := hupper x
  have hd := hlower x
  dsimp only [upper] at hu
  dsimp only [lower] at hd
  constructor <;> nlinarith

namespace FKIsingSquareBoundaryLayerCoordinateOneForm





theorem expandingSquare_scaledFourth_factor_eq_one (k : Nat) :
    |fkIsingExpandingSquareScale k| ^ 4 *
        (fkIsingExpandingSquareSide k : Real) ^ 2 = 1 := by
  have hk : (0 : Real) < (k : Real) + 1 := by positivity
  rw [fkIsingExpandingSquareScale, fkIsingExpandingSquareSide]
  push_cast
  rw [abs_of_pos (one_div_pos.mpr hk)]
  field_simp



theorem tendsto_expandingSquare_scaledFourth_of_bound_tendsto
    (derivativeBound : Nat -> Real)
    (hbound : Tendsto derivativeBound atTop (nhds 0)) :
    Tendsto
      (fun k => derivativeBound k *
        |fkIsingExpandingSquareScale k| ^ 4 *
          (fkIsingExpandingSquareSide k : Real) ^ 2)
      atTop (nhds 0) := by
  convert hbound using 1
  funext k
  rw [mul_assoc, expandingSquare_scaledFourth_factor_eq_one, mul_one]



def vertexMarkedEndpointLayer (n radius : Nat) :
    Option (FKIsingSquareFullVertexNode n) -> Prop
  | none => False
  | some x =>
      Int.natAbs (x.1 0 + (n : Int)) +
          Int.natAbs (x.1 1 + (n : Int)) <= radius \/
        Int.natAbs (x.1 0 + (n : Int)) +
          Int.natAbs (x.1 1 - (n : Int)) <= radius



def faceMarkedEndpointLayer (n radius : Nat) :
    Option (FKIsingSquareFullFaceNode n) -> Prop
  | none => False
  | some c =>
      let p := fkIsingSquareInteriorCellKey n c
      Int.natAbs (p.1 + (n : Int)) +
          Int.natAbs (p.2 + (n : Int)) <= radius \/
        Int.natAbs (p.1 + (n : Int)) +
          Int.natAbs (p.2 - (n : Int)) <= radius



theorem vertex_fixed_ghost_mem_markedEndpointLayer
    (n radius : Nat) (x : FKIsingSquareFullVertexNode n)
    (hfixed : fkIsingSquareFullVertexFixedBoundary n x)
    (hghost : 0 < fkIsingSquareFullVertexGhostMultiplicity n x) :
    vertexMarkedEndpointLayer n radius (some x) := by
  have hx := fkIsingSquareVertex_coordinate_bounds n x 0
  have hy := fkIsingSquareVertex_coordinate_bounds n x 1
  rw [fkIsingSquareFullVertexGhostMultiplicity_pos_iff] at hghost
  unfold fkIsingSquareFullVertexFixedBoundary fkIsingSquareWiredArc at hfixed
  unfold vertexMarkedEndpointLayer
  rcases hghost with hsouth | heast | hnorth
  · left
    simp [hfixed, hsouth]
  · have hn : n = 0 := by omega
    subst n
    have hy0 : x.1 1 = 0 := by omega
    left
    simp [hfixed, hy0]
  · right
    simp [hfixed, hnorth]



theorem vertex_adj_fixed_ghost_mem_markedEndpointLayer
    (n radius : Nat) (hradius : 0 < radius)
    (x y : FKIsingSquareFullVertexNode n)
    (hxy : (fkIsingSquareFullVertexGraph n).Adj x y)
    (hfixed : fkIsingSquareFullVertexFixedBoundary n y)
    (hghost : 0 < fkIsingSquareFullVertexGhostMultiplicity n y) :
    vertexMarkedEndpointLayer n radius (some x) := by
  have hl1 : l1dist 2 x.1 y.1 = 1 := by
    apply l1dist_of_adj
    exact hxy
  rw [fkIsingSquareFullVertexGhostMultiplicity_pos_iff] at hghost
  unfold fkIsingSquareFullVertexFixedBoundary fkIsingSquareWiredArc at hfixed
  unfold vertexMarkedEndpointLayer
  rcases hghost with hsouth | heast | hnorth
  · left
    have hdist : Int.natAbs (x.1 0 + (n : Int)) +
        Int.natAbs (x.1 1 + (n : Int)) = 1 := by
      simpa [l1dist, hfixed, hsouth] using hl1
    omega
  · have hn : n = 0 := by
      have hy := fkIsingSquareVertex_coordinate_bounds n y 0
      omega
    subst n
    have hy0 : y.1 1 = 0 := by
      have hy := fkIsingSquareVertex_coordinate_bounds 0 y 1
      omega
    left
    have hdist : Int.natAbs (x.1 0) + Int.natAbs (x.1 1) = 1 := by
      simpa [l1dist, hfixed, hy0] using hl1
    omega
  · right
    have hdist : Int.natAbs (x.1 0 + (n : Int)) +
        Int.natAbs (x.1 1 - (n : Int)) = 1 := by
      simpa [l1dist, hfixed, hnorth] using hl1
    omega




theorem face_fixed_ghost_mem_markedEndpointLayer
    (n radius : Nat) (hradius : 0 < radius)
    (c : FKIsingSquareFullFaceNode n)
    (hfixed : fkIsingSquareFullFaceFixedBoundary n c)
    (hghost : 0 < fkIsingSquareFullFaceGhostMultiplicity n c) :
    faceMarkedEndpointLayer n radius (some c) := by
  rw [fkIsingSquareFullFaceGhostMultiplicity_pos_iff] at hghost
  unfold fkIsingSquareFullFaceFixedBoundary at hfixed
  unfold faceMarkedEndpointLayer fkIsingSquareInteriorCellKey
  rcases hfixed with hsouth | heast | hnorth
  · left
    simp [hghost, hsouth]
  · omega
  · right
    simp [hghost]
    have hc : c.2.1 < 2 * n := c.2.2
    omega




theorem face_adj_fixed_ghost_mem_markedEndpointLayer
    (n radius : Nat) (hradius : 2 <= radius)
    (c d : FKIsingSquareFullFaceNode n)
    (hcd : (fkIsingSquareFullFaceGraph n).Adj c d)
    (hfixed : fkIsingSquareFullFaceFixedBoundary n d)
    (hghost : 0 < fkIsingSquareFullFaceGhostMultiplicity n d) :
    faceMarkedEndpointLayer n radius (some c) := by
  rw [fkIsingSquareFullFaceGhostMultiplicity_pos_iff] at hghost
  unfold fkIsingSquareFullFaceFixedBoundary at hfixed
  unfold faceMarkedEndpointLayer fkIsingSquareInteriorCellKey
  rcases hcd with hvertical | hhorizontal
  · have hx : c.1.1 = d.1.1 := congrArg Fin.val hvertical.1
    rcases hfixed with hsouth | heast | hnorth
    · left
      simp [hx, hghost]
      omega
    · omega
    · right
      simp [hx, hghost]
      have hc := c.2.2
      have hd := d.2.2
      rcases hvertical.2 with h | h <;> omega
  · have hy : c.2.1 = d.2.1 := congrArg Fin.val hhorizontal.1
    rcases hfixed with hsouth | heast | hnorth
    · left
      simp [hy, hsouth]
      rcases hhorizontal.2 with h | h <;> omega
    · omega
    · right
      simp [hy]
      have hc := c.1.2
      have hd := d.1.2
      rcases hhorizontal.2 with h | h <;> omega



noncomputable def vertexMarkedEndpointBarrier (n radius : Nat) :
    Option (FKIsingSquareFullVertexNode n) -> Real :=
  isingFiniteWeightedLocalizedPoissonBarrier
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius)
    (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n)


noncomputable def faceMarkedEndpointBarrier (n radius : Nat) :
    Option (FKIsingSquareFullFaceNode n) -> Real :=
  isingFiniteWeightedLocalizedPoissonBarrier
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius)
    (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n)

theorem vertexMarkedEndpointBarrier_nonneg (n radius : Nat) :
    forall z, 0 <= vertexMarkedEndpointBarrier n radius z :=
  isingFiniteWeightedLocalizedPoissonBarrier_nonneg
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius)
    (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n)

theorem faceMarkedEndpointBarrier_nonneg (n radius : Nat) :
    forall z, 0 <= faceMarkedEndpointBarrier n radius z :=
  isingFiniteWeightedLocalizedPoissonBarrier_nonneg
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius)
    (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n)

theorem vertexMarkedEndpointBarrier_laplacian_nonpos
    (n radius : Nat) (z : Option (FKIsingSquareFullVertexNode n))
    (hz : Not (vertexDirichletBoundary n z)) :
    isingFiniteWeightedLaplacian (vertexGhostConductance n)
      (vertexMarkedEndpointBarrier n radius) z <= 0 := by
  unfold vertexMarkedEndpointBarrier
  by_cases hze : vertexMarkedEndpointLayer n radius z
  · rw [isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_mem
      (vertexGhostGraph n) (vertexGhostConductance n)
      (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius)
      (vertexGhostConductance_nonneg n)
      (vertexGhostConductance_pos_of_adj n)
      (vertexGhost_reaches_boundary n) z hz hze]
    norm_num
  · rw [isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_not_mem
      (vertexGhostGraph n) (vertexGhostConductance n)
      (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius)
      (vertexGhostConductance_nonneg n)
      (vertexGhostConductance_pos_of_adj n)
      (vertexGhost_reaches_boundary n) z hz hze]

theorem faceMarkedEndpointBarrier_laplacian_nonpos
    (n radius : Nat) (z : Option (FKIsingSquareFullFaceNode n))
    (hz : Not (faceDirichletBoundary n z)) :
    isingFiniteWeightedLaplacian (faceGhostConductance n)
      (faceMarkedEndpointBarrier n radius) z <= 0 := by
  unfold faceMarkedEndpointBarrier
  by_cases hze : faceMarkedEndpointLayer n radius z
  · rw [isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_mem
      (faceGhostGraph n) (faceGhostConductance n)
      (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius)
      (faceGhostConductance_nonneg n)
      (faceGhostConductance_pos_of_adj n)
      (faceGhost_reaches_boundary n) z hz hze]
    norm_num
  · rw [isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_not_mem
      (faceGhostGraph n) (faceGhostConductance n)
      (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius)
      (faceGhostConductance_nonneg n)
      (faceGhostConductance_pos_of_adj n)
      (faceGhost_reaches_boundary n) z hz hze]

theorem vertexMarkedEndpointBarrier_laplacian_le_neg_one
    (n radius : Nat) (z : Option (FKIsingSquareFullVertexNode n))
    (hz : Not (vertexDirichletBoundary n z))
    (hze : vertexMarkedEndpointLayer n radius z) :
    isingFiniteWeightedLaplacian (vertexGhostConductance n)
      (vertexMarkedEndpointBarrier n radius) z <= -1 := by
  unfold vertexMarkedEndpointBarrier
  rw [isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_mem
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius)
    (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n) z hz hze]

theorem faceMarkedEndpointBarrier_laplacian_le_neg_one
    (n radius : Nat) (z : Option (FKIsingSquareFullFaceNode n))
    (hz : Not (faceDirichletBoundary n z))
    (hze : faceMarkedEndpointLayer n radius z) :
    isingFiniteWeightedLaplacian (faceGhostConductance n)
      (faceMarkedEndpointBarrier n radius) z <= -1 := by
  unfold faceMarkedEndpointBarrier
  rw [isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_mem
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius)
    (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n) z hz hze]


theorem vertexDirichlet_target_error_le_endpointLocalized
    (n : Nat) (hn : 0 < n) (radius : Nat)
    (target : Option (FKIsingSquareFullVertexNode n) -> Real)
    (bulkResidual layerResidual endpointResidual : Real)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hendpointResidual : 0 <= endpointResidual)
    (hbulk : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      fkIsingSquareFullVertexGhostMultiplicity n x = 0 ->
      Not (vertexMarkedEndpointLayer n radius (some x)) ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance n)
        target (some x)| <= bulkResidual)
    (hlayer : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity n x ->
      Not (vertexMarkedEndpointLayer n radius (some x)) ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance n)
        target (some x)| <= layerResidual)
    (hendpoint : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      vertexMarkedEndpointLayer n radius (some x) ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance n)
        target (some x)| <= endpointResidual) :
    forall z, |vertexDirichlet n hn z - target z| <=
      vertexBoundaryConsistencyError n hn target +
        bulkResidual * vertexExplicitPoissonBarrier n z +
        layerResidual * vertexGhostLayerBarrier n z +
        endpointResidual * vertexMarkedEndpointBarrier n radius z := by
  apply isingFiniteWeighted_harmonic_approximation_of_endpoint_barriers
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexGhostLayer n)
    (vertexMarkedEndpointLayer n radius)
    (vertexDirichlet n hn) target
    (vertexExplicitPoissonBarrier n) (vertexGhostLayerBarrier n)
    (vertexMarkedEndpointBarrier n radius)
    (vertexBoundaryConsistencyError n hn target)
    bulkResidual layerResidual endpointResidual
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
  · exact hendpointResidual
  · exact vertexExplicitPoissonBarrier_nonneg n
  · exact vertexGhostLayerBarrier_nonneg n
  · exact vertexMarkedEndpointBarrier_nonneg n radius
  · exact vertexExplicitPoissonBarrier_laplacian n hn
  · exact vertexGhostLayerBarrier_laplacian_nonpos n
  · exact vertexGhostLayerBarrier_laplacian_le_neg_one n
  · exact vertexMarkedEndpointBarrier_laplacian_nonpos n radius
  · exact vertexMarkedEndpointBarrier_laplacian_le_neg_one n radius
  · intro z hz hnotLayer hnotEndpoint
    cases z with
    | none => exact False.elim (hz trivial)
    | some x =>
        apply hbulk x hz
        · exact Nat.eq_zero_of_not_pos hnotLayer
        · exact hnotEndpoint
  · intro z hz hLayer hnotEndpoint
    cases z with
    | none => exact False.elim hLayer
    | some x => exact hlayer x hz hLayer hnotEndpoint
  · intro z hz hEndpoint
    cases z with
    | none => exact False.elim hEndpoint
    | some x => exact hendpoint x hz hEndpoint


theorem faceDirichlet_target_error_le_endpointLocalized
    (n : Nat) (hn : 0 < n) (radius : Nat)
    (target : Option (FKIsingSquareFullFaceNode n) -> Real)
    (bulkResidual layerResidual endpointResidual : Real)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hendpointResidual : 0 <= endpointResidual)
    (hbulk : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      fkIsingSquareFullFaceGhostMultiplicity n c = 0 ->
      Not (faceMarkedEndpointLayer n radius (some c)) ->
      |isingFiniteWeightedLaplacian (faceGhostConductance n)
        target (some c)| <= bulkResidual)
    (hlayer : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity n c ->
      Not (faceMarkedEndpointLayer n radius (some c)) ->
      |isingFiniteWeightedLaplacian (faceGhostConductance n)
        target (some c)| <= layerResidual)
    (hendpoint : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      faceMarkedEndpointLayer n radius (some c) ->
      |isingFiniteWeightedLaplacian (faceGhostConductance n)
        target (some c)| <= endpointResidual) :
    forall z, |faceDirichlet n hn z - target z| <=
      faceBoundaryConsistencyError n hn target +
        bulkResidual * faceExplicitPoissonBarrier n z +
        layerResidual * faceGhostLayerBarrier n z +
        endpointResidual * faceMarkedEndpointBarrier n radius z := by
  apply isingFiniteWeighted_harmonic_approximation_of_endpoint_barriers
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceGhostLayer n)
    (faceMarkedEndpointLayer n radius)
    (faceDirichlet n hn) target
    (faceExplicitPoissonBarrier n) (faceGhostLayerBarrier n)
    (faceMarkedEndpointBarrier n radius)
    (faceBoundaryConsistencyError n hn target)
    bulkResidual layerResidual endpointResidual
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
  · exact hendpointResidual
  · exact faceExplicitPoissonBarrier_nonneg n
  · exact faceGhostLayerBarrier_nonneg n
  · exact faceMarkedEndpointBarrier_nonneg n radius
  · exact faceExplicitPoissonBarrier_laplacian n
  · exact faceGhostLayerBarrier_laplacian_nonpos n
  · exact faceGhostLayerBarrier_laplacian_le_neg_one n
  · exact faceMarkedEndpointBarrier_laplacian_nonpos n radius
  · exact faceMarkedEndpointBarrier_laplacian_le_neg_one n radius
  · intro z hz hnotLayer hnotEndpoint
    cases z with
    | none => exact False.elim (hz trivial)
    | some c =>
        apply hbulk c hz
        · exact Nat.eq_zero_of_not_pos hnotLayer
        · exact hnotEndpoint
  · intro z hz hLayer hnotEndpoint
    cases z with
    | none => exact False.elim hLayer
    | some c => exact hlayer c hz hLayer hnotEndpoint
  · intro z hz hEndpoint
    cases z with
    | none => exact False.elim hEndpoint
    | some c => exact hendpoint c hz hEndpoint



theorem vertexSampled_target_error_le_endpointLocalized
    (n : Nat) (hn : 0 < n) (radius : Nat)
    (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex)
    (bulkResidual layerResidual endpointResidual : Real)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hendpointResidual : 0 <= endpointResidual)
    (hbulk : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      fkIsingSquareFullVertexGhostMultiplicity n x = 0 ->
      Not (vertexMarkedEndpointLayer n radius (some x)) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => (Phi (embedding y)).im) x| <= bulkResidual)
    (hlayer : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity n x ->
      Not (vertexMarkedEndpointLayer n radius (some x)) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => (Phi (embedding y)).im) x| <= layerResidual)
    (hendpoint : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      vertexMarkedEndpointLayer n radius (some x) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => (Phi (embedding y)).im) x| <= endpointResidual)
    (hfreeTrace : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity n x ->
      (Phi (embedding x)).im = 1) :
    forall z, |vertexDirichlet n hn z -
        vertexSampledImaginaryTarget n embedding Phi z| <=
      vertexBoundaryConsistencyError n hn
          (vertexSampledImaginaryTarget n embedding Phi) +
        bulkResidual * vertexExplicitPoissonBarrier n z +
        layerResidual * vertexGhostLayerBarrier n z +
        endpointResidual * vertexMarkedEndpointBarrier n radius z := by
  apply vertexDirichlet_target_error_le_endpointLocalized n hn radius
    (vertexSampledImaginaryTarget n embedding Phi)
    bulkResidual layerResidual endpointResidual
    hbulkResidual hlayerResidual hendpointResidual
  · intro x hx hzero hnotEndpoint
    have htarget : vertexSampledImaginaryTarget n embedding Phi =
        isingFiniteGhostExtension 1
          (fun y => (Phi (embedding y)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget]
    unfold vertexGhostConductance
    rw [isingFiniteGhostLaplacian_some]
    simpa [isingFermionicGhostRate, hzero] using
      hbulk x hx hzero hnotEndpoint
  · intro x hx hpos hnotEndpoint
    have htarget : vertexSampledImaginaryTarget n embedding Phi =
        isingFiniteGhostExtension 1
          (fun y => (Phi (embedding y)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget]
    unfold vertexGhostConductance
    rw [isingFiniteGhostLaplacian_some, hfreeTrace x hx hpos]
    simpa using hlayer x hx hpos hnotEndpoint
  · intro x hx hEndpoint
    have htarget : vertexSampledImaginaryTarget n embedding Phi =
        isingFiniteGhostExtension 1
          (fun y => (Phi (embedding y)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget]
    unfold vertexGhostConductance
    rw [isingFiniteGhostLaplacian_some]
    by_cases hpos : 0 < fkIsingSquareFullVertexGhostMultiplicity n x
    · rw [hfreeTrace x hx hpos]
      simpa using hendpoint x hx hEndpoint
    · have hzero : fkIsingSquareFullVertexGhostMultiplicity n x = 0 :=
        Nat.eq_zero_of_not_pos hpos
      simpa [isingFermionicGhostRate, hzero] using
        hendpoint x hx hEndpoint


theorem faceSampled_target_error_le_endpointLocalized
    (n : Nat) (hn : 0 < n) (radius : Nat)
    (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex)
    (bulkResidual layerResidual endpointResidual : Real)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hendpointResidual : 0 <= endpointResidual)
    (hbulk : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      fkIsingSquareFullFaceGhostMultiplicity n c = 0 ->
      Not (faceMarkedEndpointLayer n radius (some c)) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d => (Phi (embedding d)).im) c| <= bulkResidual)
    (hlayer : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity n c ->
      Not (faceMarkedEndpointLayer n radius (some c)) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d => (Phi (embedding d)).im) c| <= layerResidual)
    (hendpoint : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      faceMarkedEndpointLayer n radius (some c) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d => (Phi (embedding d)).im) c| <= endpointResidual)
    (hfreeTrace : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity n c ->
      (Phi (embedding c)).im = 0) :
    forall z, |faceDirichlet n hn z -
        faceSampledImaginaryTarget n embedding Phi z| <=
      faceBoundaryConsistencyError n hn
          (faceSampledImaginaryTarget n embedding Phi) +
        bulkResidual * faceExplicitPoissonBarrier n z +
        layerResidual * faceGhostLayerBarrier n z +
        endpointResidual * faceMarkedEndpointBarrier n radius z := by
  apply faceDirichlet_target_error_le_endpointLocalized n hn radius
    (faceSampledImaginaryTarget n embedding Phi)
    bulkResidual layerResidual endpointResidual
    hbulkResidual hlayerResidual hendpointResidual
  · intro c hc hzero hnotEndpoint
    have htarget : faceSampledImaginaryTarget n embedding Phi =
        isingFiniteGhostExtension 0
          (fun d => (Phi (embedding d)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget]
    unfold faceGhostConductance
    rw [isingFiniteGhostLaplacian_some]
    simpa [isingFermionicGhostRate, hzero] using
      hbulk c hc hzero hnotEndpoint
  · intro c hc hpos hnotEndpoint
    have htarget : faceSampledImaginaryTarget n embedding Phi =
        isingFiniteGhostExtension 0
          (fun d => (Phi (embedding d)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget]
    unfold faceGhostConductance
    rw [isingFiniteGhostLaplacian_some, hfreeTrace c hc hpos]
    simpa using hlayer c hc hpos hnotEndpoint
  · intro c hc hEndpoint
    have htarget : faceSampledImaginaryTarget n embedding Phi =
        isingFiniteGhostExtension 0
          (fun d => (Phi (embedding d)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget]
    unfold faceGhostConductance
    rw [isingFiniteGhostLaplacian_some]
    by_cases hpos : 0 < fkIsingSquareFullFaceGhostMultiplicity n c
    · rw [hfreeTrace c hc hpos]
      simpa using hendpoint c hc hEndpoint
    · have hzero : fkIsingSquareFullFaceGhostMultiplicity n c = 0 :=
        Nat.eq_zero_of_not_pos hpos
      simpa [isingFermionicGhostRate, hzero] using
        hendpoint c hc hEndpoint




structure PhysicalEndpointLocalizedRobinInputs
    (N : Nat -> Nat) (hN : forall k, 0 < N k)
    (Phi : Complex -> Complex)
    (mesh : Nat -> Real) (radius : Nat -> Nat)
    (bulkRate layerRate endpointRate : Nat -> Real) where
  mesh_nonneg : forall k, 0 <= mesh k
  bulk_nonneg : forall k, 0 <= bulkRate k
  layer_nonneg : forall k, 0 <= layerRate k
  endpoint_nonneg : forall k, 0 <= endpointRate k
  vertexFixed : forall k x,
    fkIsingSquareFullVertexFixedBoundary (N k) x ->
      (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 0
  faceFixed : forall k c,
    fkIsingSquareFullFaceFixedBoundary (N k) c ->
      (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 1
  vertexFree : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
      (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 1
  faceFree : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
      (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 0
  vertexBulk : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
    Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
        (fun y => (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) y)).im) x| <= bulkRate k
  faceBulk : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
    Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
        (fun d => (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) d)).im) c| <= bulkRate k
  vertexLayer : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
    Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
        (fun y => (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) y)).im) x| <= layerRate k
  faceLayer : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
    Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
        (fun d => (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) d)).im) c| <= layerRate k
  vertexEndpoint : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    vertexMarkedEndpointLayer (N k) (radius k) (some x) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
        (fun y => (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) y)).im) x| <= endpointRate k
  faceEndpoint : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    faceMarkedEndpointLayer (N k) (radius k) (some c) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
        (fun d => (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) d)).im) c| <= endpointRate k
  scaledBulk_tendsto : Tendsto
    (fun k => bulkRate k * (N k : Real) ^ 2) atTop (nhds 0)
  layer_tendsto : Tendsto layerRate atTop (nhds 0)
  mesh_tendsto : Tendsto mesh atTop (nhds 0)






theorem PhysicalEndpointLocalizedRobinInputs.primitive_convergence_away
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real}
    {radius : Nat -> Nat} {bulkRate layerRate endpointRate : Nat -> Real}
    (H : PhysicalEndpointLocalizedRobinInputs
      N hN Phi mesh radius bulkRate layerRate endpointRate)
    (safe : forall k,
      FKIsingSquareInteriorRadialIncidence (N k) (hN k) -> Prop)
    (vertexEndpointWeight faceEndpointWeight mismatchRate : Nat -> Real)
    (hvertexWeight_nonneg : forall k, 0 <= vertexEndpointWeight k)
    (hfaceWeight_nonneg : forall k, 0 <= faceEndpointWeight k)
    (hmismatch_nonneg : forall k, 0 <= mismatchRate k)
    (hvertexWeight : forall k e, safe k e ->
      vertexMarkedEndpointBarrier (N k) (radius k)
        (some (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)) <=
          vertexEndpointWeight k)
    (hfaceWeight : forall k e, safe k e ->
      faceMarkedEndpointBarrier (N k) (radius k)
        (some (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e)) <=
          faceEndpointWeight k)
    (hmismatch : forall k e, safe k e ->
      |(Phi (fullSquareScaledFaceEmbedding (N k) (mesh k)
          (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))).im -
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
          (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| <=
        mismatchRate k)
    (hvertexEndpoint_tendsto : Tendsto
      (fun k => endpointRate k * vertexEndpointWeight k)
      atTop (nhds 0))
    (hfaceEndpoint_tendsto : Tendsto
      (fun k => endpointRate k * faceEndpointWeight k)
      atTop (nhds 0))
    (hmismatch_tendsto : Tendsto mismatchRate atTop (nhds 0)) :
    forall eta : Real, 0 < eta -> ∀ᶠ k in atTop,
      forall e : FKIsingSquareInteriorRadialIncidence (N k) (hN k),
        safe k e ->
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) -
              (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta /\
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) -
              (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta := by
  let common : Nat -> Real := fun k =>
    vertexBarrierGrowthConstant * (bulkRate k * (N k : Real) ^ 2) +
      (1 / isingFermionicGhostCoefficient) * layerRate k
  let upper : Nat -> Real := fun k =>
    common k + endpointRate k * vertexEndpointWeight k +
      endpointRate k * faceEndpointWeight k + mismatchRate k
  have hcommon : Tendsto common atTop (nhds 0) := by
    have hbulk : Tendsto
        (fun k => vertexBarrierGrowthConstant *
          (bulkRate k * (N k : Real) ^ 2)) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul H.scaledBulk_tendsto
    have hlayer : Tendsto
        (fun k => (1 / isingFermionicGhostCoefficient) * layerRate k)
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul H.layer_tendsto
    simpa [common] using hbulk.add hlayer
  have hupper : Tendsto upper atTop (nhds 0) := by
    simpa [upper] using
      ((hcommon.add hvertexEndpoint_tendsto).add
        hfaceEndpoint_tendsto).add hmismatch_tendsto
  intro eta heta
  have heventually : ∀ᶠ k in atTop, dist (upper k) 0 < eta :=
    (Metric.tendsto_nhds.1 hupper) eta heta
  filter_upwards [heventually] with k hk
  intro e hsafe
  have hcommon_nonneg : 0 <= common k := by
    dsimp only [common]
    exact add_nonneg
      (mul_nonneg vertexBarrierGrowthConstant_nonneg
        (mul_nonneg (H.bulk_nonneg k) (sq_nonneg _)))
      (mul_nonneg
        (div_nonneg (by norm_num) isingFermionicGhostCoefficient_pos.le)
        (H.layer_nonneg k))
  have hupper_nonneg : 0 <= upper k := by
    dsimp only [upper]
    exact add_nonneg
      (add_nonneg
        (add_nonneg hcommon_nonneg
          (mul_nonneg (H.endpoint_nonneg k) (hvertexWeight_nonneg k)))
        (mul_nonneg (H.endpoint_nonneg k) (hfaceWeight_nonneg k)))
      (hmismatch_nonneg k)
  have hk' : upper k < eta := by
    simpa [Real.dist_eq, abs_of_nonneg hupper_nonneg] using hk
  let vertexEmbedding := fullSquareScaledVertexEmbedding (N k) (mesh k)
  let faceEmbedding := fullSquareScaledFaceEmbedding (N k) (mesh k)
  let x := fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e
  let c := fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e
  have hv := vertexSampled_target_error_le_endpointLocalized
    (N k) (hN k) (radius k) vertexEmbedding Phi
    (bulkRate k) (layerRate k) (endpointRate k)
    (H.bulk_nonneg k) (H.layer_nonneg k) (H.endpoint_nonneg k)
    (H.vertexBulk k) (H.vertexLayer k) (H.vertexEndpoint k)
    (H.vertexFree k) (some x)
  have hvBoundary : vertexBoundaryConsistencyError (N k) (hN k)
      (vertexSampledImaginaryTarget (N k) vertexEmbedding Phi) = 0 :=
    vertexSampled_boundaryConsistencyError_eq_zero
      (N k) (hN k) vertexEmbedding Phi (H.vertexFixed k)
  have hvBarrier := vertexExplicitPoissonBarrierBound_le_growth
    (N k) (hN k)
  have hv' : |vertexDirichlet (N k) (hN k) (some x) -
      (Phi (vertexEmbedding x)).im| <= upper k := by
    calc
      _ <= vertexBoundaryConsistencyError (N k) (hN k)
            (vertexSampledImaginaryTarget (N k) vertexEmbedding Phi) +
          bulkRate k * vertexExplicitPoissonBarrier (N k) (some x) +
          layerRate k * vertexGhostLayerBarrier (N k) (some x) +
          endpointRate k *
            vertexMarkedEndpointBarrier (N k) (radius k) (some x) := hv
      _ <= 0 + bulkRate k *
            (vertexBarrierGrowthConstant * (N k : Real) ^ 2) +
          layerRate k * (1 / isingFermionicGhostCoefficient) +
          endpointRate k * vertexEndpointWeight k := by
        rw [hvBoundary]
        gcongr
        · exact H.bulk_nonneg k
        · exact (vertexExplicitPoissonBarrier_le_bound (N k) (some x)).trans
            hvBarrier
        · exact H.layer_nonneg k
        · exact vertexGhostLayerBarrier_le (N k) (some x)
        · exact H.endpoint_nonneg k
        · exact hvertexWeight k e hsafe
      _ <= upper k := by
        dsimp only [upper, common]
        have hf : 0 <= endpointRate k * faceEndpointWeight k :=
          mul_nonneg (H.endpoint_nonneg k) (hfaceWeight_nonneg k)
        have hm : 0 <= mismatchRate k := hmismatch_nonneg k
        nlinarith
  have hf := faceSampled_target_error_le_endpointLocalized
    (N k) (hN k) (radius k) faceEmbedding Phi
    (bulkRate k) (layerRate k) (endpointRate k)
    (H.bulk_nonneg k) (H.layer_nonneg k) (H.endpoint_nonneg k)
    (H.faceBulk k) (H.faceLayer k) (H.faceEndpoint k)
    (H.faceFree k) (some c)
  have hfBoundary : faceBoundaryConsistencyError (N k) (hN k)
      (faceSampledImaginaryTarget (N k) faceEmbedding Phi) = 0 :=
    faceSampled_boundaryConsistencyError_eq_zero
      (N k) (hN k) faceEmbedding Phi (H.faceFixed k)
  have hfBarrier : faceExplicitPoissonBarrierBound (N k) <=
      vertexBarrierGrowthConstant * (N k : Real) ^ 2 := by
    calc
      faceExplicitPoissonBarrierBound (N k) =
          (1 / 2 : Real) * (N k : Real) ^ 2 := by
        unfold faceExplicitPoissonBarrierBound
        ring
      _ <= vertexBarrierGrowthConstant * (N k : Real) ^ 2 :=
        mul_le_mul_of_nonneg_right half_le_vertexBarrierGrowthConstant
          (sq_nonneg _)
  have hfOwn : |faceDirichlet (N k) (hN k) (some c) -
      (Phi (faceEmbedding c)).im| <=
        common k + endpointRate k * faceEndpointWeight k := by
    calc
      _ <= faceBoundaryConsistencyError (N k) (hN k)
            (faceSampledImaginaryTarget (N k) faceEmbedding Phi) +
          bulkRate k * faceExplicitPoissonBarrier (N k) (some c) +
          layerRate k * faceGhostLayerBarrier (N k) (some c) +
          endpointRate k *
            faceMarkedEndpointBarrier (N k) (radius k) (some c) := hf
      _ <= 0 + bulkRate k *
            (vertexBarrierGrowthConstant * (N k : Real) ^ 2) +
          layerRate k * (1 / isingFermionicGhostCoefficient) +
          endpointRate k * faceEndpointWeight k := by
        rw [hfBoundary]
        gcongr
        · exact H.bulk_nonneg k
        · exact (faceExplicitPoissonBarrier_le_bound (N k) (some c)).trans
            hfBarrier
        · exact H.layer_nonneg k
        · exact faceGhostLayerBarrier_le (N k) (some c)
        · exact H.endpoint_nonneg k
        · exact hfaceWeight k e hsafe
      _ = _ := by
        dsimp only [common]
        ring
  have hmis := hmismatch k e hsafe
  have hf' : |faceDirichlet (N k) (hN k) (some c) -
      (Phi (vertexEmbedding x)).im| <= upper k := by
    rw [show faceDirichlet (N k) (hN k) (some c) -
        (Phi (vertexEmbedding x)).im =
      (faceDirichlet (N k) (hN k) (some c) -
        (Phi (faceEmbedding c)).im) +
      ((Phi (faceEmbedding c)).im -
        (Phi (vertexEmbedding x)).im) by ring]
    calc
      |_ + _| <= |faceDirichlet (N k) (hN k) (some c) -
          (Phi (faceEmbedding c)).im| +
        |(Phi (faceEmbedding c)).im -
          (Phi (vertexEmbedding x)).im| := abs_add_le _ _
      _ <= (common k + endpointRate k * faceEndpointWeight k) +
          mismatchRate k := add_le_add hfOwn hmis
      _ <= upper k := by
        dsimp only [upper]
        have hvw : 0 <= endpointRate k * vertexEndpointWeight k :=
          mul_nonneg (H.endpoint_nonneg k) (hvertexWeight_nonneg k)
        nlinarith
  have hphysical := physicalIncidence_close_of_dirichlet_close
    (N k) (hN k) e (Phi (vertexEmbedding x)).im (upper k) hv' hf'
  exact ⟨hphysical.1.trans_lt hk', hphysical.2.trans_lt hk'⟩

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
