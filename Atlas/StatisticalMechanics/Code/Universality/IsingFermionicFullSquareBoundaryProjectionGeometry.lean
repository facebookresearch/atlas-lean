/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicMarkedEndpointTraceProjection











namespace StatMech.Universality

open Filter Metric Set
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm



theorem halfDiagonal_displacement_le_scale
    (z direction : Complex) (hdirection : ‖direction‖ <= 2)
    (scale : Real) (hscale : 0 <= scale) :
    dist z (z + ((scale / 2 : Real) : Complex) * direction) <= scale := by
  rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    scale / 2 * ‖direction‖ <= scale / 2 * 2 := by
      gcongr
    _ = scale := by ring

private theorem norm_neg_one_add_I_le_two :
    ‖(-1 + Complex.I : Complex)‖ <= 2 := by
  calc
    ‖(-1 + Complex.I : Complex)‖ <= ‖(-1 : Complex)‖ + ‖Complex.I‖ :=
      norm_add_le _ _
    _ = 2 := by norm_num

private theorem norm_one_add_I_le_two :
    ‖(1 + Complex.I : Complex)‖ <= 2 := by
  calc
    ‖(1 + Complex.I : Complex)‖ <= ‖(1 : Complex)‖ + ‖Complex.I‖ :=
      norm_add_le _ _
    _ = 2 := by norm_num

private theorem norm_one_sub_I_le_two :
    ‖(1 - Complex.I : Complex)‖ <= 2 := by
  calc
    ‖(1 - Complex.I : Complex)‖ <= ‖(1 : Complex)‖ + ‖Complex.I‖ :=
      norm_sub_le _ _
    _ = 2 := by norm_num

private theorem norm_neg_one_sub_I_le_two :
    ‖(-1 - Complex.I : Complex)‖ <= 2 := by
  calc
    ‖(-1 - Complex.I : Complex)‖ <= ‖(-1 : Complex)‖ + ‖Complex.I‖ :=
      norm_sub_le _ _
    _ = 2 := by norm_num


def fullSquareVertexBoundaryProjection
    (n : Nat) (scale : Real) (x : FKIsingSquareFullVertexNode n) : Complex :=
  fullSquareScaledVertexEmbedding n scale x



def fullSquareFaceFixedBoundaryProjection
    (n : Nat) (scale : Real) (c : FKIsingSquareFullFaceNode n) : Complex :=
  let z := fullSquareScaledFaceEmbedding n scale c
  if c.2.1 = 0 then
    z + ((scale / 2 : Real) : Complex) * (-1 + Complex.I)
  else if c.1.1 + 1 = 2 * n then
    z + ((scale / 2 : Real) : Complex) * (1 + Complex.I)
  else
    z + ((scale / 2 : Real) : Complex) * (1 - Complex.I)



def fullSquareVertexFreeBoundaryProjection
    (n : Nat) (scale : Real) (x : FKIsingSquareFullVertexNode n) : Complex :=
  fullSquareScaledVertexEmbedding n scale x


def fullSquareFaceFreeBoundaryProjection
    (n : Nat) (scale : Real) (c : FKIsingSquareFullFaceNode n) : Complex :=
  fullSquareScaledFaceEmbedding n scale c +
    ((scale / 2 : Real) : Complex) * (-1 - Complex.I)


def fullSquareScaledLeftSide (n : Nat) (scale : Real) : Set Complex :=
  {z | z.re + z.im = -2 * (n : Real) * scale}


def fullSquareScaledBottomSide (n : Nat) (scale : Real) : Set Complex :=
  {z | z.re - z.im = -2 * (n : Real) * scale}


def fullSquareScaledRightSide (n : Nat) (scale : Real) : Set Complex :=
  {z | z.re + z.im = 2 * (n : Real) * scale}


def fullSquareScaledTopSide (n : Nat) (scale : Real) : Set Complex :=
  {z | z.re - z.im = 2 * (n : Real) * scale}

def fullSquareScaledFreeSides (n : Nat) (scale : Real) : Set Complex :=
  fullSquareScaledBottomSide n scale ∪
    fullSquareScaledRightSide n scale ∪ fullSquareScaledTopSide n scale

theorem fullSquareVertexBoundaryProjection_mem_leftSide
    (n : Nat) (scale : Real) (x : FKIsingSquareFullVertexNode n)
    (hx : fkIsingSquareFullVertexFixedBoundary n x) :
    fullSquareVertexBoundaryProjection n scale x ∈
      fullSquareScaledLeftSide n scale := by
  change x.1 0 = -(n : Int) at hx
  simp [fullSquareScaledLeftSide, fullSquareVertexBoundaryProjection,
    fullSquareScaledVertexEmbedding, fullSquareScaledCoordinateEmbedding,
    fkIsingSquareFullVertexCoordinate, fkIsingSquareWiredIntPoint]
  rw [hx]
  push_cast
  ring

theorem fullSquareFaceFixedBoundaryProjection_mem_freeSides
    (n : Nat) (scale : Real) (c : FKIsingSquareFullFaceNode n)
    (hc : fkIsingSquareFullFaceFixedBoundary n c) :
    fullSquareFaceFixedBoundaryProjection n scale c ∈
      fullSquareScaledFreeSides n scale := by
  unfold fullSquareFaceFixedBoundaryProjection
  split_ifs with hb hr
  · refine Or.inl (Or.inl ?_)
    simp [fullSquareScaledBottomSide,
      fullSquareScaledFaceEmbedding, fullSquareScaledCoordinateEmbedding,
      fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
      fkIsingSquareWiredIntPoint]
    push_cast at hb ⊢
    rw [hb]
    ring
  · refine Or.inl (Or.inr ?_)
    simp [fullSquareScaledRightSide,
      fullSquareScaledFaceEmbedding, fullSquareScaledCoordinateEmbedding,
      fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
      fkIsingSquareWiredIntPoint]
    have hr' : (c.1.val : Real) + 1 = 2 * (n : Real) := by
      exact_mod_cast hr
    rw [show (c.1.val : Real) = 2 * (n : Real) - 1 by linarith]
    ring
  · refine Or.inr ?_
    rcases hc with hc | hc | hc
    · exact (hb hc).elim
    · exact (hr hc).elim
    · simp [fullSquareScaledTopSide,
        fullSquareScaledFaceEmbedding, fullSquareScaledCoordinateEmbedding,
        fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
        fkIsingSquareWiredIntPoint]
      have hc' : (c.2.val : Real) + 1 = 2 * (n : Real) := by
        exact_mod_cast hc
      rw [show (c.2.val : Real) = 2 * (n : Real) - 1 by linarith]
      ring

theorem fullSquareVertexFreeBoundaryProjection_mem_freeSides
    (n : Nat) (scale : Real) (x : FKIsingSquareFullVertexNode n)
    (hx : 0 < fkIsingSquareFullVertexGhostMultiplicity n x) :
    fullSquareVertexFreeBoundaryProjection n scale x ∈
      fullSquareScaledFreeSides n scale := by
  rw [fkIsingSquareFullVertexGhostMultiplicity_pos_iff] at hx
  rcases hx with hx | hx | hx
  · refine Or.inl (Or.inl ?_)
    simp [fullSquareScaledBottomSide,
      fullSquareVertexFreeBoundaryProjection,
      fullSquareScaledVertexEmbedding, fullSquareScaledCoordinateEmbedding,
      fkIsingSquareFullVertexCoordinate, fkIsingSquareWiredIntPoint]
    rw [hx]
    push_cast
    ring
  · refine Or.inl (Or.inr ?_)
    simp [fullSquareScaledRightSide,
      fullSquareVertexFreeBoundaryProjection,
      fullSquareScaledVertexEmbedding, fullSquareScaledCoordinateEmbedding,
      fkIsingSquareFullVertexCoordinate, fkIsingSquareWiredIntPoint]
    rw [hx]
    push_cast
    ring
  · refine Or.inr ?_
    simp [fullSquareScaledTopSide,
      fullSquareVertexFreeBoundaryProjection,
      fullSquareScaledVertexEmbedding, fullSquareScaledCoordinateEmbedding,
      fkIsingSquareFullVertexCoordinate, fkIsingSquareWiredIntPoint]
    rw [hx]
    push_cast
    ring

theorem fullSquareFaceFreeBoundaryProjection_mem_leftSide
    (n : Nat) (scale : Real) (c : FKIsingSquareFullFaceNode n)
    (hc : 0 < fkIsingSquareFullFaceGhostMultiplicity n c) :
    fullSquareFaceFreeBoundaryProjection n scale c ∈
      fullSquareScaledLeftSide n scale := by
  rw [fkIsingSquareFullFaceGhostMultiplicity_pos_iff] at hc
  simp [fullSquareScaledLeftSide, fullSquareFaceFreeBoundaryProjection,
    fullSquareScaledFaceEmbedding, fullSquareScaledCoordinateEmbedding,
    fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
    fkIsingSquareWiredIntPoint]
  rw [hc]
  ring

@[simp] theorem fullSquareVertexBoundaryProjection_dist
    (n : Nat) (scale : Real) (x : FKIsingSquareFullVertexNode n) :
    dist (fullSquareScaledVertexEmbedding n scale x)
      (fullSquareVertexBoundaryProjection n scale x) = 0 := by
  simp [fullSquareVertexBoundaryProjection]

theorem fullSquareFaceFixedBoundaryProjection_dist_le
    (n : Nat) (scale : Real) (hscale : 0 <= scale)
    (c : FKIsingSquareFullFaceNode n) :
    dist (fullSquareScaledFaceEmbedding n scale c)
      (fullSquareFaceFixedBoundaryProjection n scale c) <= scale := by
  unfold fullSquareFaceFixedBoundaryProjection
  split_ifs
  · exact halfDiagonal_displacement_le_scale _ _
      norm_neg_one_add_I_le_two scale hscale
  · exact halfDiagonal_displacement_le_scale _ _
      norm_one_add_I_le_two scale hscale
  · exact halfDiagonal_displacement_le_scale _ _
      norm_one_sub_I_le_two scale hscale

@[simp] theorem fullSquareVertexFreeBoundaryProjection_dist
    (n : Nat) (scale : Real) (x : FKIsingSquareFullVertexNode n) :
    dist (fullSquareScaledVertexEmbedding n scale x)
      (fullSquareVertexFreeBoundaryProjection n scale x) = 0 := by
  simp [fullSquareVertexFreeBoundaryProjection]

theorem fullSquareFaceFreeBoundaryProjection_dist_le
    (n : Nat) (scale : Real) (hscale : 0 <= scale)
    (c : FKIsingSquareFullFaceNode n) :
    dist (fullSquareScaledFaceEmbedding n scale c)
      (fullSquareFaceFreeBoundaryProjection n scale c) <= scale := by
  exact halfDiagonal_displacement_le_scale _ _
    norm_neg_one_sub_I_le_two scale hscale



noncomputable def PhysicalBoundaryProjectionSampling.ofFullSquareProjections
    {N : Nat -> Nat} {mesh : Nat -> Real} {Phi : Complex -> Complex}
    (L : NNReal) (hPhi : LipschitzWith L (fun z => (Phi z).im))
    (hmesh : forall k, 0 <= mesh k)
    (hvertexTrace : forall k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x ->
        (Phi (fullSquareVertexBoundaryProjection
          (N k) (mesh k) x)).im = 0)
    (hfaceTrace : forall k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c ->
        (Phi (fullSquareFaceFixedBoundaryProjection
          (N k) (mesh k) c)).im = 1) :
    PhysicalBoundaryProjectionSampling N mesh Phi where
  lipschitzConstant := L
  imPhi_lipschitz := hPhi
  vertexProjection k x :=
    fullSquareVertexBoundaryProjection (N k) (mesh k) x.1
  faceProjection k c :=
    fullSquareFaceFixedBoundaryProjection (N k) (mesh k) c.1
  vertexProjection_trace k x := hvertexTrace k x.1 x.2
  faceProjection_trace k c := hfaceTrace k c.1 c.2
  vertexProjection_dist_le_mesh k x := by
    rw [fullSquareVertexBoundaryProjection_dist]
    exact hmesh k
  faceProjection_dist_le_mesh k c :=
    fullSquareFaceFixedBoundaryProjection_dist_le
      (N k) (mesh k) (hmesh k) c.1





structure FullSquareOrdinaryBoundaryProjectionTraceData
    (N : Nat -> Nat) (Phi : Complex -> Complex)
    (mesh : Nat -> Real) (radius : Nat -> Nat) where
  lipschitzConstant : Nat -> NNReal
  region : Nat -> Set Complex
  imPhi_lipschitz : forall k,
    LipschitzOnWith (lipschitzConstant k)
      (fun z => (Phi z).im) (region k)
  vertexFixed : forall k x,
    fkIsingSquareFullVertexFixedBoundary (N k) x ->
    Not (0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x) ->
      fullSquareScaledVertexEmbedding (N k) (mesh k) x ∈ region k /\
      (Phi (fullSquareVertexBoundaryProjection
        (N k) (mesh k) x)).im = 0
  faceFixed : forall k c,
    fkIsingSquareFullFaceFixedBoundary (N k) c ->
    Not (0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c) ->
      fullSquareScaledFaceEmbedding (N k) (mesh k) c ∈ region k /\
      fullSquareFaceFixedBoundaryProjection (N k) (mesh k) c ∈ region k /\
      (Phi (fullSquareFaceFixedBoundaryProjection
        (N k) (mesh k) c)).im = 1
  vertexFree : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
    Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      fullSquareScaledVertexEmbedding (N k) (mesh k) x ∈ region k /\
      (Phi (fullSquareVertexFreeBoundaryProjection
        (N k) (mesh k) x)).im = 1
  faceFree : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
    Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      fullSquareScaledFaceEmbedding (N k) (mesh k) c ∈ region k /\
      fullSquareFaceFreeBoundaryProjection (N k) (mesh k) c ∈ region k /\
      (Phi (fullSquareFaceFreeBoundaryProjection
        (N k) (mesh k) c)).im = 0



noncomputable def FullSquareOrdinaryBoundaryProjectionTraceData.ofSideTraces
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (L : Nat -> NNReal) (S : Nat -> Set Complex)
    (hPhi : forall k,
      LipschitzOnWith (L k) (fun z => (Phi z).im) (S k))
    (hleftTrace : forall k,
      Set.EqOn (fun z => (Phi z).im) (fun _ => 0)
        (fullSquareScaledLeftSide (N k) (mesh k)))
    (hfreeTrace : forall k,
      Set.EqOn (fun z => (Phi z).im) (fun _ => 1)
        (fullSquareScaledFreeSides (N k) (mesh k)))
    (hvertexFixed_mem : forall k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x ->
      Not (0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x) ->
        fullSquareScaledVertexEmbedding (N k) (mesh k) x ∈ S k)
    (hfaceFixed_mem : forall k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c ->
      Not (0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c) ->
        fullSquareScaledFaceEmbedding (N k) (mesh k) c ∈ S k /\
        fullSquareFaceFixedBoundaryProjection (N k) (mesh k) c ∈ S k)
    (hvertexFree_mem : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        fullSquareScaledVertexEmbedding (N k) (mesh k) x ∈ S k)
    (hfaceFree_mem : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        fullSquareScaledFaceEmbedding (N k) (mesh k) c ∈ S k /\
        fullSquareFaceFreeBoundaryProjection (N k) (mesh k) c ∈ S k) :
    FullSquareOrdinaryBoundaryProjectionTraceData N Phi mesh radius where
  lipschitzConstant := L
  region := S
  imPhi_lipschitz := hPhi
  vertexFixed k x hfixed hghost :=
    ⟨hvertexFixed_mem k x hfixed hghost,
      hleftTrace k
        (fullSquareVertexBoundaryProjection_mem_leftSide
          (N k) (mesh k) x hfixed)⟩
  faceFixed k c hfixed hghost :=
    ⟨(hfaceFixed_mem k c hfixed hghost).1,
      (hfaceFixed_mem k c hfixed hghost).2,
      hfreeTrace k
        (fullSquareFaceFixedBoundaryProjection_mem_freeSides
          (N k) (mesh k) c hfixed)⟩
  vertexFree k x hfixed hghost hendpoint :=
    ⟨hvertexFree_mem k x hfixed hghost hendpoint,
      hfreeTrace k
        (fullSquareVertexFreeBoundaryProjection_mem_freeSides
          (N k) (mesh k) x hghost)⟩
  faceFree k c hfixed hghost hendpoint :=
    ⟨(hfaceFree_mem k c hfixed hghost hendpoint).1,
      (hfaceFree_mem k c hfixed hghost hendpoint).2,
      hleftTrace k
        (fullSquareFaceFreeBoundaryProjection_mem_leftSide
          (N k) (mesh k) c hghost)⟩



def fullSquareOrdinaryBoundaryProjectionCarrier
    (n : Nat) (mesh : Real) (radius : Nat) : Set Complex :=
  {z |
    (∃ x : FKIsingSquareFullVertexNode n,
      fkIsingSquareFullVertexFixedBoundary n x ∧
      Not (0 < fkIsingSquareFullVertexGhostMultiplicity n x) ∧
        (z = fullSquareScaledVertexEmbedding n mesh x ∨
          z = fullSquareVertexBoundaryProjection n mesh x)) ∨
    (∃ c : FKIsingSquareFullFaceNode n,
      fkIsingSquareFullFaceFixedBoundary n c ∧
      Not (0 < fkIsingSquareFullFaceGhostMultiplicity n c) ∧
        (z = fullSquareScaledFaceEmbedding n mesh c ∨
          z = fullSquareFaceFixedBoundaryProjection n mesh c)) ∨
    (∃ x : FKIsingSquareFullVertexNode n,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ∧
      0 < fkIsingSquareFullVertexGhostMultiplicity n x ∧
      Not (vertexMarkedEndpointLayer n radius (some x)) ∧
        (z = fullSquareScaledVertexEmbedding n mesh x ∨
          z = fullSquareVertexFreeBoundaryProjection n mesh x)) ∨
    (∃ c : FKIsingSquareFullFaceNode n,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ∧
      0 < fkIsingSquareFullFaceGhostMultiplicity n c ∧
      Not (faceMarkedEndpointLayer n radius (some c)) ∧
        (z = fullSquareScaledFaceEmbedding n mesh c ∨
          z = fullSquareFaceFreeBoundaryProjection n mesh c))}


theorem fullSquareOrdinaryBoundaryProjectionCarrier_finite
    (n : Nat) (mesh : Real) (radius : Nat) :
    (fullSquareOrdinaryBoundaryProjectionCarrier n mesh radius).Finite := by
  have hvertexFixed :=
    (Set.finite_range
      (fun x : FKIsingSquareFullVertexNode n =>
        fullSquareScaledVertexEmbedding n mesh x)).union
      (Set.finite_range
        (fun x : FKIsingSquareFullVertexNode n =>
          fullSquareVertexBoundaryProjection n mesh x))
  have hfaceFixed :=
    (Set.finite_range
      (fun c : FKIsingSquareFullFaceNode n =>
        fullSquareScaledFaceEmbedding n mesh c)).union
      (Set.finite_range
        (fun c : FKIsingSquareFullFaceNode n =>
          fullSquareFaceFixedBoundaryProjection n mesh c))
  have hvertexFree :=
    (Set.finite_range
      (fun x : FKIsingSquareFullVertexNode n =>
        fullSquareScaledVertexEmbedding n mesh x)).union
      (Set.finite_range
        (fun x : FKIsingSquareFullVertexNode n =>
          fullSquareVertexFreeBoundaryProjection n mesh x))
  have hfaceFree :=
    (Set.finite_range
      (fun c : FKIsingSquareFullFaceNode n =>
        fullSquareScaledFaceEmbedding n mesh c)).union
      (Set.finite_range
        (fun c : FKIsingSquareFullFaceNode n =>
          fullSquareFaceFreeBoundaryProjection n mesh c))
  refine
    (hvertexFixed.union (hfaceFixed.union
      (hvertexFree.union hfaceFree))).subset ?_
  intro z hz
  rcases hz with
      ⟨x, _hfixed, _hghost, rfl | rfl⟩ |
      ⟨c, _hfixed, _hghost, rfl | rfl⟩ |
      ⟨x, _hfixed, _hghost, _hendpoint, rfl | rfl⟩ |
      ⟨c, _hfixed, _hghost, _hendpoint, rfl | rfl⟩ <;>
    simp




noncomputable def
    FullSquareOrdinaryBoundaryProjectionTraceData.ofCarrierTraces
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (L : Nat -> NNReal)
    (hPhi : forall k,
      LipschitzOnWith (L k) (fun z => (Phi z).im)
        (fullSquareOrdinaryBoundaryProjectionCarrier
          (N k) (mesh k) (radius k)))
    (hvertexFixedTrace : forall k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x ->
      Not (0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x) ->
        (Phi (fullSquareVertexBoundaryProjection
          (N k) (mesh k) x)).im = 0)
    (hfaceFixedTrace : forall k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c ->
      Not (0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c) ->
        (Phi (fullSquareFaceFixedBoundaryProjection
          (N k) (mesh k) c)).im = 1)
    (hvertexFreeTrace : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        (Phi (fullSquareVertexFreeBoundaryProjection
          (N k) (mesh k) x)).im = 1)
    (hfaceFreeTrace : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        (Phi (fullSquareFaceFreeBoundaryProjection
          (N k) (mesh k) c)).im = 0) :
    FullSquareOrdinaryBoundaryProjectionTraceData N Phi mesh radius where
  lipschitzConstant := L
  region k := fullSquareOrdinaryBoundaryProjectionCarrier
    (N k) (mesh k) (radius k)
  imPhi_lipschitz := hPhi
  vertexFixed k x hfixed hghost :=
    ⟨Or.inl ⟨x, hfixed, hghost, Or.inl rfl⟩,
      hvertexFixedTrace k x hfixed hghost⟩
  faceFixed k c hfixed hghost :=
    ⟨Or.inr (Or.inl ⟨c, hfixed, hghost, Or.inl rfl⟩),
      Or.inr (Or.inl ⟨c, hfixed, hghost, Or.inr rfl⟩),
      hfaceFixedTrace k c hfixed hghost⟩
  vertexFree k x hfixed hghost hendpoint :=
    ⟨Or.inr (Or.inr (Or.inl
      ⟨x, hfixed, hghost, hendpoint, Or.inl rfl⟩)),
      hvertexFreeTrace k x hfixed hghost hendpoint⟩
  faceFree k c hfixed hghost hendpoint :=
    ⟨Or.inr (Or.inr (Or.inr
        ⟨c, hfixed, hghost, hendpoint, Or.inl rfl⟩)),
      Or.inr (Or.inr (Or.inr
        ⟨c, hfixed, hghost, hendpoint, Or.inr rfl⟩)),
      hfaceFreeTrace k c hfixed hghost hendpoint⟩



noncomputable def
    FullSquareOrdinaryBoundaryProjectionTraceData.ofCarrierSideTraces
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (L : Nat -> NNReal)
    (hPhi : forall k,
      LipschitzOnWith (L k) (fun z => (Phi z).im)
        (fullSquareOrdinaryBoundaryProjectionCarrier
          (N k) (mesh k) (radius k)))
    (hleftTrace : forall k,
      Set.EqOn (fun z => (Phi z).im) (fun _ => 0)
        (fullSquareScaledLeftSide (N k) (mesh k)))
    (hfreeTrace : forall k,
      Set.EqOn (fun z => (Phi z).im) (fun _ => 1)
        (fullSquareScaledFreeSides (N k) (mesh k))) :
    FullSquareOrdinaryBoundaryProjectionTraceData N Phi mesh radius :=
  FullSquareOrdinaryBoundaryProjectionTraceData.ofSideTraces
    L (fun k => fullSquareOrdinaryBoundaryProjectionCarrier
      (N k) (mesh k) (radius k))
    hPhi hleftTrace hfreeTrace
    (fun _k x hfixed hghost =>
      Or.inl ⟨x, hfixed, hghost, Or.inl rfl⟩)
    (fun _k c hfixed hghost =>
      ⟨Or.inr (Or.inl ⟨c, hfixed, hghost, Or.inl rfl⟩),
        Or.inr (Or.inl ⟨c, hfixed, hghost, Or.inr rfl⟩)⟩)
    (fun _k x hfixed hghost hendpoint =>
      Or.inr (Or.inr (Or.inl
        ⟨x, hfixed, hghost, hendpoint, Or.inl rfl⟩)))
    (fun _k c hfixed hghost hendpoint =>
      ⟨Or.inr (Or.inr (Or.inr
          ⟨c, hfixed, hghost, hendpoint, Or.inl rfl⟩)),
        Or.inr (Or.inr (Or.inr
          ⟨c, hfixed, hghost, hendpoint, Or.inr rfl⟩))⟩)



noncomputable def
    FullSquareOrdinaryBoundaryProjectionTraceData.toProjectionData
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (H : FullSquareOrdinaryBoundaryProjectionTraceData N Phi mesh radius)
    (hmesh : forall k, 0 <= mesh k) :
    PhysicalEndpointOrdinaryBoundaryProjectionData N Phi mesh radius where
  lipschitzConstant := H.lipschitzConstant
  region := H.region
  imPhi_lipschitz := H.imPhi_lipschitz
  vertexFixed k x hfixed hghost := by
    obtain ⟨hsample, htrace⟩ := H.vertexFixed k x hfixed hghost
    exact
      { boundaryPoint := fullSquareVertexBoundaryProjection
          (N k) (mesh k) x
        sample_mem := hsample
        boundary_mem := by
          simpa [fullSquareVertexBoundaryProjection] using hsample
        trace := htrace
        dist_le_mesh := by
          rw [fullSquareVertexBoundaryProjection_dist]
          exact hmesh k }
  faceFixed k c hfixed hghost := by
    obtain ⟨hsample, hboundary, htrace⟩ := H.faceFixed k c hfixed hghost
    exact
      { boundaryPoint := fullSquareFaceFixedBoundaryProjection
          (N k) (mesh k) c
        sample_mem := hsample
        boundary_mem := hboundary
        trace := htrace
        dist_le_mesh := fullSquareFaceFixedBoundaryProjection_dist_le
          (N k) (mesh k) (hmesh k) c }
  vertexFree k x hfixed hghost hendpoint := by
    obtain ⟨hsample, htrace⟩ :=
      H.vertexFree k x hfixed hghost hendpoint
    exact
      { boundaryPoint := fullSquareVertexFreeBoundaryProjection
          (N k) (mesh k) x
        sample_mem := hsample
        boundary_mem := by
          simpa [fullSquareVertexFreeBoundaryProjection] using hsample
        trace := htrace
        dist_le_mesh := by
          rw [fullSquareVertexFreeBoundaryProjection_dist]
          exact hmesh k }
  faceFree k c hfixed hghost hendpoint := by
    obtain ⟨hsample, hboundary, htrace⟩ :=
      H.faceFree k c hfixed hghost hendpoint
    exact
      { boundaryPoint := fullSquareFaceFreeBoundaryProjection
          (N k) (mesh k) c
        sample_mem := hsample
        boundary_mem := hboundary
        trace := htrace
        dist_le_mesh := fullSquareFaceFreeBoundaryProjection_dist_le
          (N k) (mesh k) (hmesh k) c }





theorem PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofCarrierTracesAndRange
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real} {radius : Nat -> Nat}
    (Hfourth : PhysicalEndpointFourthOrderBulkData N Phi mesh radius)
    (Hlayer : PhysicalEndpointLayerIncrementData N Phi mesh radius)
    (L : Nat -> NNReal)
    (hPhi : forall k,
      LipschitzOnWith (L k) (fun z => (Phi z).im)
        (fullSquareOrdinaryBoundaryProjectionCarrier
          (N k) (mesh k) (radius k)))
    (hvertexFixedTrace : forall k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x ->
      Not (0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x) ->
        (Phi (fullSquareVertexBoundaryProjection
          (N k) (mesh k) x)).im = 0)
    (hfaceFixedTrace : forall k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c ->
      Not (0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c) ->
        (Phi (fullSquareFaceFixedBoundaryProjection
          (N k) (mesh k) c)).im = 1)
    (hvertexFreeTrace : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        (Phi (fullSquareVertexFreeBoundaryProjection
          (N k) (mesh k) x)).im = 1)
    (hfaceFreeTrace : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        (Phi (fullSquareFaceFreeBoundaryProjection
          (N k) (mesh k) c)).im = 0)
    (hvertexRadius : forall k, 0 < radius k)
    (hfaceRadius : forall k, 2 <= radius k)
    (hmesh_nonneg : forall k, 0 <= mesh k)
    (hvertexRange : forall k x,
      0 <= (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im /\
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <= 1)
    (hfaceRange : forall k c,
      0 <= (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im /\
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im <= 1)
    (hscaledFourth_tendsto : Tendsto
      (fun k => |mesh k| ^ 4 * (N k : Real) ^ 2) atTop (nhds 0))
    (htrace_tendsto : Tendsto
      (fun k => (L k : Real) * mesh k) atTop (nhds 0))
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
    PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh radius
      (fun k => (L k : Real) * mesh k)
      (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12)
      (fun k => (4 * Hlayer.constant) * mesh k +
        (3 * isingFermionicGhostCoefficient) * ((L k : Real) * mesh k))
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
  let Htrace : FullSquareOrdinaryBoundaryProjectionTraceData
      N Phi mesh radius :=
    FullSquareOrdinaryBoundaryProjectionTraceData.ofCarrierTraces
      L hPhi hvertexFixedTrace hfaceFixedTrace hvertexFreeTrace hfaceFreeTrace
  let P : PhysicalEndpointOrdinaryBoundaryProjectionData N Phi mesh radius :=
    Htrace.toProjectionData hmesh_nonneg
  exact
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFourthOrderLayerProjectionAndRange
      Hfourth Hlayer P hvertexRadius hfaceRadius hmesh_nonneg
      hvertexRange hfaceRange hscaledFourth_tendsto htrace_tendsto
      hmesh_tendsto





theorem PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofCarrierSideTracesAndRange
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real} {radius : Nat -> Nat}
    (Hfourth : PhysicalEndpointFourthOrderBulkData N Phi mesh radius)
    (Hlayer : PhysicalEndpointLayerIncrementData N Phi mesh radius)
    (L : Nat -> NNReal)
    (hPhi : forall k,
      LipschitzOnWith (L k) (fun z => (Phi z).im)
        (fullSquareOrdinaryBoundaryProjectionCarrier
          (N k) (mesh k) (radius k)))
    (hleftTrace : forall k,
      Set.EqOn (fun z => (Phi z).im) (fun _ => 0)
        (fullSquareScaledLeftSide (N k) (mesh k)))
    (hfreeTrace : forall k,
      Set.EqOn (fun z => (Phi z).im) (fun _ => 1)
        (fullSquareScaledFreeSides (N k) (mesh k)))
    (hvertexRadius : forall k, 0 < radius k)
    (hfaceRadius : forall k, 2 <= radius k)
    (hmesh_nonneg : forall k, 0 <= mesh k)
    (hvertexRange : forall k x,
      0 <= (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im /\
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <= 1)
    (hfaceRange : forall k c,
      0 <= (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im /\
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im <= 1)
    (hscaledFourth_tendsto : Tendsto
      (fun k => |mesh k| ^ 4 * (N k : Real) ^ 2) atTop (nhds 0))
    (htrace_tendsto : Tendsto
      (fun k => (L k : Real) * mesh k) atTop (nhds 0))
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
    PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh radius
      (fun k => (L k : Real) * mesh k)
      (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12)
      (fun k => (4 * Hlayer.constant) * mesh k +
        (3 * isingFermionicGhostCoefficient) * ((L k : Real) * mesh k))
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
  let Htrace : FullSquareOrdinaryBoundaryProjectionTraceData
      N Phi mesh radius :=
    FullSquareOrdinaryBoundaryProjectionTraceData.ofCarrierSideTraces
      L hPhi hleftTrace hfreeTrace
  let P : PhysicalEndpointOrdinaryBoundaryProjectionData N Phi mesh radius :=
    Htrace.toProjectionData hmesh_nonneg
  exact
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFourthOrderLayerProjectionAndRange
      Hfourth Hlayer P hvertexRadius hfaceRadius hmesh_nonneg
      hvertexRange hfaceRange hscaledFourth_tendsto htrace_tendsto
      hmesh_tendsto

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
