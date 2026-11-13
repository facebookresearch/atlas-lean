/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierA.Z2GaugeCubicalPlusCorrDecay

open MeasureTheory Filter Topology
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice

noncomputable section



def internalCentralCellEmbedding (n m : Nat)
    (hnm : centralSquareSide n < m) :
    CubicalCell (centralSquareSide n) (centralSquareSide n)
        (centralSquareSide n + centralSquareSide n) ↪
      CubicalCell (oddCubeSide m) (oddCubeSide m) (oddCubeSide m) where
  toFun q := CubicalCell.mk
    ⟨m + q.x.val, by
      dsimp [oddCubeSide, centralSquareSide] at *
      omega⟩
    ⟨m + q.y.val, by
      dsimp [oddCubeSide, centralSquareSide] at *
      omega⟩
    ⟨m - centralSquareSide n + q.z.val, by
      dsimp [oddCubeSide, centralSquareSide] at *
      omega⟩
  inj' := by
    intro q r h
    rcases q with ⟨qx, qy, qz⟩
    rcases r with ⟨rx, ry, rz⟩
    simp only [CubicalCell.mk.injEq] at h
    simp only [CubicalCell.mk.injEq]
    constructor
    · apply Fin.ext
      have := congrArg Fin.val h.1
      simp only at this
      omega
    constructor
    · apply Fin.ext
      have := congrArg Fin.val h.2.1
      simp only at this
      omega
    · apply Fin.ext
      have := congrArg Fin.val h.2.2
      simp only at this
      omega


def internalCentralVertexEmbedding (n m : Nat)
    (hnm : centralSquareSide n < m) :
    CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
        (centralSquareSide n + centralSquareSide n) ↪
      CubicalDualVertex (oddCubeSide m) (oddCubeSide m) (oddCubeSide m) :=
  (internalCentralCellEmbedding n m hnm).optionMap

@[simp] theorem internalCentralVertexEmbedding_none
    (n m : Nat) (hnm : centralSquareSide n < m) :
    internalCentralVertexEmbedding n m hnm none = none := rfl

@[simp] theorem internalCentralVertexEmbedding_some
    (n m : Nat) (hnm : centralSquareSide n < m)
    (q : CubicalCell (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) :
    internalCentralVertexEmbedding n m hnm (some q) =
      some (internalCentralCellEmbedding n m hnm q) := rfl


def centralCylinderSite (n : Nat)
    (q : CubicalCell (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) : Site 3 := fun i =>
  if i = (0 : Fin 3) then q.x.val
  else if i = (1 : Fin 3) then q.y.val
  else (centralSquareSide n : Int) - q.z.val



theorem oddCubicalCenteredSite_internalCentralCellEmbedding
    (n m : Nat) (hnm : centralSquareSide n < m)
    (q : CubicalCell (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) :
    oddCubicalCenteredSite m (internalCentralCellEmbedding n m hnm q) =
      centralCylinderSite n q := by
  funext i
  fin_cases i
  · simp [centralCylinderSite, internalCentralCellEmbedding]
  · simp [centralCylinderSite, internalCentralCellEmbedding]
  · simp [centralCylinderSite, internalCentralCellEmbedding]
    have hle : centralSquareSide n <= m := hnm.le
    simp only [Nat.cast_add, Nat.cast_sub hle]
    ring



theorem cubicalDualL1_internalCentralVertexEmbedding
    (n m : Nat) (hnm : centralSquareSide n < m)
    (u v : CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) :
    cubicalDualL1 (internalCentralVertexEmbedding n m hnm u)
        (internalCentralVertexEmbedding n m hnm v) =
      cubicalDualL1 u v := by
  cases u with
  | none => rfl
  | some q =>
    cases v with
    | none => rfl
    | some r =>
      simp only [internalCentralVertexEmbedding_some, cubicalDualL1,
        internalCentralCellEmbedding]
      change
        Nat.dist (m + q.x.val) (m + r.x.val) +
            Nat.dist (m + q.y.val) (m + r.y.val) +
              Nat.dist (m - centralSquareSide n + q.z.val)
                (m - centralSquareSide n + r.z.val) =
          Nat.dist q.x.val r.x.val + Nat.dist q.y.val r.y.val +
            Nat.dist q.z.val r.z.val
      rw [Nat.dist_add_add_left, Nat.dist_add_add_left,
        Nat.dist_add_add_left]


theorem mem_centralLowerBoundaryVertices_iff
    (n : Nat)
    (q : CubicalCell (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) :
    some q ∈ centralLowerBoundaryVertices n ↔
      q.z.val < centralSquareSide n ∧
        (q.x.val = 0 ∨ q.x.val + 1 = centralSquareSide n ∨
         q.y.val = 0 ∨ q.y.val + 1 = centralSquareSide n ∨
         q.z.val = 0) := by
  simp [centralLowerBoundaryVertices, centralLowerBottomVertices,
    centralLowerWestVertices, centralLowerEastVertices,
    centralLowerSouthVertices, centralLowerNorthVertices]
  constructor
  · intro h
    rcases h with h | h | h | h | h
    all_goals rcases h with ⟨i, j, h⟩
    all_goals subst q
    all_goals simp [centralSquareSide] at *
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by
        apply Fin.ext
        simp))))
    all_goals omega
  · rintro ⟨hz, h⟩
    rcases q with ⟨x, y, z⟩
    simp only at hz h ⊢
    rcases h with hx | hx | hy | hy | hz0
    · exact Or.inr (Or.inl ⟨y, ⟨z.val, by
        simpa [centralSquareSide] using hz⟩, by
        rw [CubicalCell.mk.injEq]
        refine ⟨hx.symm, rfl, ?_⟩
        apply Fin.ext
        rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨y, ⟨z.val, by
        simpa [centralSquareSide] using hz⟩, by
        rw [CubicalCell.mk.injEq]
        refine ⟨?_, rfl, ?_⟩
        · apply Fin.ext
          simpa [centralSquareSide] using hx.symm
        · apply Fin.ext
          rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨x, ⟨z.val, by simpa [centralSquareSide] using hz⟩, by
          rw [CubicalCell.mk.injEq]
          refine ⟨rfl, hy.symm, ?_⟩
          apply Fin.ext
          rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨x, ⟨z.val, by simpa [centralSquareSide] using hz⟩, by
          rw [CubicalCell.mk.injEq]
          refine ⟨rfl, ?_, ?_⟩
          · apply Fin.ext
            simpa [centralSquareSide] using hy.symm
          · apply Fin.ext
            rfl⟩)))
    · exact Or.inl ⟨x, y, by
        rw [CubicalCell.mk.injEq]
        refine ⟨rfl, rfl, ?_⟩
        simpa using hz0.symm⟩



theorem centralLowerBoundaryVertices_map_internal
    (n m : Nat) (hnm : centralSquareSide n < m) :
    (centralLowerBoundaryVertices n).map
        (internalCentralVertexEmbedding n m hnm) =
      cubicalInternalCentralBoundaryVertices (centralSquareSide n) m := by
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, huv⟩ := Finset.mem_map.mp hv
    cases u with
    | none =>
        exact (none_not_mem_centralLowerBoundaryVertices n hu).elim
    | some q =>
        subst v
        have hq := (mem_centralLowerBoundaryVertices_iff n q).mp hu
        apply Finset.mem_image.mpr
        refine ⟨internalCentralCellEmbedding n m hnm q, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        change
          m <= m + q.x.val ∧
          m + q.x.val < m + centralSquareSide n ∧
          m <= m + q.y.val ∧
          m + q.y.val < m + centralSquareSide n ∧
          m - centralSquareSide n <=
            m - centralSquareSide n + q.z.val ∧
          m - centralSquareSide n + q.z.val < m ∧
          (m + q.x.val = m ∨
           m + q.x.val + 1 = m + centralSquareSide n ∨
           m + q.y.val = m ∨
           m + q.y.val + 1 = m + centralSquareSide n ∨
           m - centralSquareSide n + q.z.val =
             m - centralSquareSide n)
        rcases hq with ⟨hz, hboundary⟩
        have hle : centralSquareSide n <= m := hnm.le
        refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
        rcases hboundary with hx0 | hx1 | hy0 | hy1 | hz0
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (Or.inl (by omega)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (by omega))))
  · intro hv
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
    have hcoord := (Finset.mem_filter.mp hq).2
    let x : Fin (centralSquareSide n) :=
      ⟨q.x.val - m, by omega⟩
    let y : Fin (centralSquareSide n) :=
      ⟨q.y.val - m, by omega⟩
    let z : Fin (centralSquareSide n + centralSquareSide n) :=
      ⟨q.z.val - (m - centralSquareSide n), by
        dsimp [centralSquareSide] at *
        omega⟩
    let r : CubicalCell (centralSquareSide n) (centralSquareSide n)
        (centralSquareSide n + centralSquareSide n) :=
      CubicalCell.mk x y z
    apply Finset.mem_map.mpr
    refine ⟨some r, ?_, ?_⟩
    · rw [mem_centralLowerBoundaryVertices_iff]
      dsimp [r, x, y, z]
      refine ⟨by omega, ?_⟩
      rcases hcoord.2.2.2.2.2.2 with hx0 | hx1 | hy0 | hy1 | hz0
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (Or.inl (by omega)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by omega))))
    · simp only [internalCentralVertexEmbedding_some, Option.some.injEq]
      rw [CubicalCell.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · apply Fin.ext
        dsimp [internalCentralCellEmbedding, r, x]
        omega
      · apply Fin.ext
        dsimp [internalCentralCellEmbedding, r, y]
        omega
      · apply Fin.ext
        dsimp [internalCentralCellEmbedding, r, z]
        omega



theorem centralUpperLayerVertices_map_internal
    (n m : Nat) (hnm : centralSquareSide n < m) :
    (centralUpperLayerVertices n).map
        (internalCentralVertexEmbedding n m hnm) =
      cubicalInternalCentralUpperCoordinateVertices
        (centralSquareSide n) m hnm.le := by
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
    cases u with
    | none => exact (none_not_mem_centralUpperLayerVertices n hu).elim
    | some q =>
        obtain ⟨ij, _, hq⟩ := Finset.mem_image.mp hu
        simp only [Option.some.injEq] at hq
        subst q
        apply Finset.mem_image.mpr
        refine ⟨ij, Finset.mem_univ _, ?_⟩
        simp only [internalCentralVertexEmbedding_some, Option.some.injEq]
        rw [CubicalCell.mk.injEq]
        refine ⟨?_, ?_, ?_⟩
        · apply Fin.ext
          rfl
        · apply Fin.ext
          rfl
        · apply Fin.ext
          dsimp [internalCentralCellEmbedding]
          exact (Nat.sub_add_cancel hnm.le).symm
  · intro hv
    obtain ⟨ij, _, rfl⟩ := Finset.mem_image.mp hv
    let q : CubicalCell (centralSquareSide n) (centralSquareSide n)
        (centralSquareSide n + centralSquareSide n) :=
      CubicalCell.mk ij.1 ij.2
        ⟨centralSquareSide n, by
          dsimp [centralSquareSide]
          omega⟩
    apply Finset.mem_map.mpr
    refine ⟨some q, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨ij, Finset.mem_univ _, ?_⟩
      apply congrArg some
      rw [CubicalCell.mk.injEq]
      exact ⟨rfl, rfl, Fin.ext rfl⟩
    · simp only [internalCentralVertexEmbedding_some, Option.some.injEq]
      rw [CubicalCell.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · apply Fin.ext
        rfl
      · apply Fin.ext
        rfl
      · apply Fin.ext
        dsimp [internalCentralCellEmbedding, q]
        exact Nat.sub_add_cancel hnm.le


def centralCylinderPairs (n : Nat) : Finset
    (CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n) ×
     CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) :=
  (centralLowerBoundaryVertices n).product (centralUpperLayerVertices n)

private theorem map_product_embeddings
    {A B C D : Type*} [DecidableEq A] [DecidableEq B]
    [DecidableEq C] [DecidableEq D]
    (e : A ↪ B) (f : C ↪ D) (s : Finset A) (t : Finset C) :
    (s.product t).map (e.prodMap f) = (s.map e).product (t.map f) := by
  ext uv
  constructor
  · intro huv
    obtain ⟨xy, hxy, hEq⟩ := Finset.mem_map.mp huv
    have hmem := Finset.mem_product.mp hxy
    subst uv
    exact Finset.mem_product.mpr
      ⟨Finset.mem_map.mpr ⟨xy.1, hmem.1, rfl⟩,
       Finset.mem_map.mpr ⟨xy.2, hmem.2, rfl⟩⟩
  · intro huv
    have hmem := Finset.mem_product.mp huv
    obtain ⟨x, hxs, hx⟩ := Finset.mem_map.mp hmem.1
    obtain ⟨y, hyt, hy⟩ := Finset.mem_map.mp hmem.2
    exact Finset.mem_map.mpr
      ⟨(x, y), Finset.mem_product.mpr ⟨hxs, hyt⟩,
       Prod.ext hx hy⟩

theorem centralCylinderPairs_map_internal
    (n m : Nat) (hnm : centralSquareSide n < m) :
    (centralCylinderPairs n).map
        ((internalCentralVertexEmbedding n m hnm).prodMap
          (internalCentralVertexEmbedding n m hnm)) =
      (cubicalInternalCentralBoundaryVertices (centralSquareSide n) m).product
        (cubicalInternalCentralUpperVertices
          (centralSquareSide n) m hnm.le) := by
  unfold centralCylinderPairs
  rw [map_product_embeddings,
    centralLowerBoundaryVertices_map_internal,
    cubicalInternalCentralUpperVertices_eq_coordinate
      (centralSquareSide n) m (by simp [centralSquareSide]) hnm.le,
    centralUpperLayerVertices_map_internal]



theorem cubicalInternalCentralWilsonExpectation_ge_fixed_product
    (n m : Nat) (hnm : centralSquareSide n < m)
    (K : Real) (hK : 0 < K) :
    (∏ uv ∈ centralCylinderPairs n,
      (1 - multibondIsingTwoPoint cubicalDualEnds
        (fun _ : CubicalPlaquette (oddCubeSide m) (oddCubeSide m)
          (oddCubeSide m) => gaugeDualCoupling K)
        (internalCentralVertexEmbedding n m hnm uv.1)
        (internalCentralVertexEmbedding n m hnm uv.2))) <=
      gaugeWilsonExpectation cubicalPlaquetteIncidence (fun _ => K)
        (gaugeSurfaceBoundary cubicalPlaquetteIncidence
          (cubicalInternalCentralSheet
            (centralSquareSide n) m hnm.le)) := by
  let e := internalCentralVertexEmbedding n m hnm
  let pairE := e.prodMap e
  let corr := fun uv :
      CubicalDualVertex (oddCubeSide m) (oddCubeSide m) (oddCubeSide m) ×
        CubicalDualVertex (oddCubeSide m) (oddCubeSide m) (oddCubeSide m) =>
    multibondIsingTwoPoint cubicalDualEnds
      (fun _ : CubicalPlaquette (oddCubeSide m) (oddCubeSide m)
        (oddCubeSide m) => gaugeDualCoupling K) uv.1 uv.2
  let actual :=
    (cubicalInternalCentralInnerVertices
      (centralSquareSide n) m hnm.le).product
    (cubicalInternalCentralUpperVertices
      (centralSquareSide n) m hnm.le)
  let boundary :=
    (cubicalInternalCentralBoundaryVertices
      (centralSquareSide n) m).product
    (cubicalInternalCentralUpperVertices
      (centralSquareSide n) m hnm.le)
  have hsub : actual ⊆ boundary := by
    intro uv huv
    have hmem := Finset.mem_product.mp huv
    exact Finset.mem_product.mpr
      ⟨cubicalInternalCentralInnerVertices_subset_boundary
        (centralSquareSide n) m (by simp [centralSquareSide]) hnm hmem.1,
       hmem.2⟩
  have hJ0 : forall p : CubicalPlaquette (oddCubeSide m) (oddCubeSide m)
      (oddCubeSide m), 0 <= gaugeDualCoupling K := fun _ =>
    (gaugeDualCoupling_pos hK).le
  have hfactor0 : ∀ uv, uv ∈ boundary -> 0 <= 1 - corr uv := by
    intro uv _
    exact sub_nonneg.mpr
      (multibondIsingTwoPoint_le_one_of_nonneg cubicalDualEnds _ hJ0 _ _)
  have hfactor1 : ∀ uv, uv ∈ boundary -> uv ∉ actual ->
      1 - corr uv <= 1 := by
    intro uv _ _
    linarith [multibondIsingTwoPoint_nonneg_of_nonneg
      cubicalDualEnds _ hJ0 uv.1 uv.2]
  calc
    (∏ uv ∈ centralCylinderPairs n,
        (1 - multibondIsingTwoPoint cubicalDualEnds
          (fun _ : CubicalPlaquette (oddCubeSide m) (oddCubeSide m)
            (oddCubeSide m) => gaugeDualCoupling K)
          (e uv.1) (e uv.2))) =
        ∏ uv ∈ boundary, (1 - corr uv) := by
      change (∏ uv ∈ centralCylinderPairs n,
        (1 - corr (pairE uv))) = _
      calc
        _ = ∏ uv ∈ (centralCylinderPairs n).map pairE,
            (1 - corr uv) :=
          (Finset.prod_map (centralCylinderPairs n) pairE
            (fun uv => 1 - corr uv)).symm
        _ = _ := by rw [centralCylinderPairs_map_internal]
    _ <= ∏ uv ∈ actual, (1 - corr uv) :=
      Finset.prod_le_prod_of_subset_of_le_one hsub hfactor0 hfactor1
    _ <= gaugeWilsonExpectation cubicalPlaquetteIncidence (fun _ => K)
        (gaugeSurfaceBoundary cubicalPlaquetteIncidence
          (cubicalInternalCentralSheet
            (centralSquareSide n) m hnm.le)) := by
      exact cubicalInternalCentralWilsonExpectation_ge_product
        (centralSquareSide n) m (by simp [centralSquareSide]) hnm.le
        (fun _ => K) (fun _ => hK)



def centralCylinderVertexSite (n : Nat) :
    CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n) -> Site 3
  | none => 0
  | some q => centralCylinderSite n q



def internalCentralPairCorrelation
    (beta : Real) (n m : Nat) (hnm : centralSquareSide n < m)
    (uv : CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
        (centralSquareSide n + centralSquareSide n) ×
      CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
        (centralSquareSide n + centralSquareSide n)) : Real :=
  multibondIsingTwoPoint cubicalDualEnds
    (fun _ : CubicalPlaquette (oddCubeSide m) (oddCubeSide m)
      (oddCubeSide m) => beta)
    (internalCentralVertexEmbedding n m hnm uv.1)
    (internalCentralVertexEmbedding n m hnm uv.2)




theorem exists_internalCentralPairCorrelation_tendsto
    (beta : Real) (n : Nat) :
    ∃ m : Nat -> Nat, ∃ hm : ∀ k, centralSquareSide n < m k,
      Tendsto m atTop atTop ∧
      ∀ uv, uv ∈ centralCylinderPairs n ->
        Tendsto
          (fun k => internalCentralPairCorrelation beta n (m k) (hm k) uv)
          atTop
          (nhds (plusCorr 3 beta
            (centralCylinderVertexSite n uv.1)
            (centralCylinderVertexSite n uv.2))) := by
  obtain ⟨phi, hphi, hconv⟩ := plusState_isInfiniteVolumeState 3 beta 0
  let shift : Nat -> Nat := fun k => k + centralSquareSide n + 1
  let m : Nat -> Nat := fun k => phi (shift k)
  have hshift : Tendsto shift atTop atTop := by
    exact (tendsto_add_atTop_iff_nat
      (centralSquareSide n + 1)).2 tendsto_id
  have hmTop : Tendsto m atTop atTop := hphi.tendsto_atTop.comp hshift
  have hm : ∀ k, centralSquareSide n < m k := by
    intro k
    dsimp [m, shift]
    have hle := hphi.le_apply (x := k + centralSquareSide n + 1)
    omega
  have hconv' : WeakConvergesTo
      (fun k => plusMeasure 3 (m k) beta 0) (plusState 3 beta 0) := by
    simpa [m, Function.comp_def] using hconv.comp hshift
  refine ⟨m, hm, hmTop, ?_⟩
  intro uv huv
  have hmem := Finset.mem_product.mp huv
  rcases uv with ⟨u, v⟩
  cases u with
  | none =>
      exact (none_not_mem_centralLowerBoundaryVertices n hmem.1).elim
  | some q =>
      cases v with
      | none =>
          exact (none_not_mem_centralUpperLayerVertices n hmem.2).elim
      | some r =>
          have hpair := plusMeasure_pair_tendsto beta m hconv'
            (centralCylinderSite n q) (centralCylinderSite n r)
          change Tendsto
            (fun k => internalCentralPairCorrelation beta n (m k) (hm k)
              (some q, some r)) atTop
            (nhds (plusCorr 3 beta
              (centralCylinderSite n q) (centralCylinderSite n r)))
          apply hpair.congr
          intro k
          rw [internalCentralPairCorrelation]
          simp only [internalCentralVertexEmbedding_some]
          rw [oddCubicalDualTwoPoint_eq_plusMeasure_pair]
          have hqsite := oddCubicalCenteredSite_internalCentralCellEmbedding
            n (m k) (hm k) q
          have hrsite := oddCubicalCenteredSite_internalCentralCellEmbedding
            n (m k) (hm k) r
          unfold oddCubicalCenteredSite at hqsite hrsite
          rw [hqsite, hrsite]



theorem exists_internalCentralCylinderProduct_tendsto
    (beta : Real) (n : Nat) :
    ∃ m : Nat -> Nat, ∃ hm : ∀ k, centralSquareSide n < m k,
      Tendsto m atTop atTop ∧
      Tendsto
        (fun k => ∏ uv ∈ centralCylinderPairs n,
          (1 - internalCentralPairCorrelation beta n (m k) (hm k) uv))
        atTop
        (nhds (∏ uv ∈ centralCylinderPairs n,
          (1 - plusCorr 3 beta
            (centralCylinderVertexSite n uv.1)
            (centralCylinderVertexSite n uv.2)))) := by
  obtain ⟨m, hm, hmTop, hcorr⟩ :=
    exists_internalCentralPairCorrelation_tendsto beta n
  refine ⟨m, hm, hmTop, ?_⟩
  exact tendsto_finset_prod_one_sub (centralCylinderPairs n)
    (fun k uv => internalCentralPairCorrelation beta n (m k) (hm k) uv)
    (fun uv => plusCorr 3 beta
      (centralCylinderVertexSite n uv.1)
      (centralCylinderVertexSite n uv.2)) hcorr



theorem cubicalInternalCentralSheet_eq_map
    (n m : Nat) (hnm : centralSquareSide n <= m) :
    cubicalInternalCentralSheet (centralSquareSide n) m hnm =
      (cubicalXYSheet
        (a := centralSquareSide n) (b := centralSquareSide n) (c := 0)
        (0 : Fin 1)).map
        (cubicalPlaquetteChart m m m
          (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
          (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
          (by dsimp [oddCubeSide]; omega)) := by
  unfold cubicalInternalCentralSheet cubicalXYSheet
  rw [Finset.map_eq_image, Finset.image_image]
  apply Finset.image_congr
  intro ij _
  change CubicalPlaquette.xy _ _ _ =
    CubicalPlaquette.xy
      (finOffsetEmbedding m _ ij.1)
      (finOffsetEmbedding m _ ij.2)
      (finOffsetEmbedding m _ (0 : Fin 1))
  rw [CubicalPlaquette.xy.injEq]
  refine ⟨?_, ?_, ?_⟩
  · apply Fin.ext
    rfl
  · apply Fin.ext
    rfl
  · apply Fin.ext
    rfl


theorem gaugeSurfaceBoundary_cubicalInternalCentralSheet_fixed
    (n m : Nat) (hnm : centralSquareSide n <= m) :
    gaugeSurfaceBoundary cubicalPlaquetteIncidence
        (cubicalInternalCentralSheet (centralSquareSide n) m hnm) =
      (cubicalXYLoop
        (a := centralSquareSide n) (b := centralSquareSide n) (c := 0)
        (0 : Fin 1)).map
        (cubicalEdgeChart m m m
          (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
          (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
          (by dsimp [oddCubeSide]; omega)) := by
  rw [cubicalInternalCentralSheet_eq_map]
  exact gaugeSurfaceBoundary_map
    cubicalPlaquetteIncidence cubicalPlaquetteIncidence
    (cubicalEdgeChart m m m
      (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
      (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
      (by dsimp [oddCubeSide]; omega))
    (cubicalPlaquetteChart m m m
      (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
      (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
      (by dsimp [oddCubeSide]; omega))
    (cubicalPlaquetteIncidence_chart m m m
      (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
      (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
      (by dsimp [oddCubeSide]; omega))
    (cubicalXYSheet (0 : Fin 1))



def cubicalInternalCentralWilsonExpectation
    (K : Real) (n m : Nat) (hnm : centralSquareSide n <= m) : Real :=
  gaugeWilsonExpectation cubicalPlaquetteIncidence
    (fun _ : CubicalPlaquette (oddCubeSide m) (oddCubeSide m)
      (oddCubeSide m) => K)
    (gaugeSurfaceBoundary cubicalPlaquetteIncidence
      (cubicalInternalCentralSheet (centralSquareSide n) m hnm))



theorem cubicalInternalCentralWilsonExpectation_le_fixed_succ
    {K : Real} (hK : 0 <= K) (n m : Nat)
    (hnm : centralSquareSide n <= m) :
    cubicalInternalCentralWilsonExpectation K n m hnm <=
      cubicalFixedLoopWilsonSequence K (centralSquareSide n)
        (centralSquareSide n) (m + 1) := by
  have hinnerXY : m + centralSquareSide n <= oddCubeSide m := by
    dsimp [oddCubeSide]
    omega
  have hinnerZ : m + 0 <= oddCubeSide m := by
    dsimp [oddCubeSide]
    omega
  have houterXY : 1 + oddCubeSide m <=
      (m + 1) + centralSquareSide n + (m + 1) := by
    dsimp [oddCubeSide, centralSquareSide]
    omega
  have houterZ : 1 + oddCubeSide m <= (m + 1) + (m + 1) := by
    dsimp [oddCubeSide]
    omega
  let L := cubicalXYLoop
    (a := centralSquareSide n) (b := centralSquareSide n) (c := 0)
    (0 : Fin 1)
  let inner := cubicalEdgeChart m m m
    (a := centralSquareSide n) (b := centralSquareSide n) (c := 0)
    (A := oddCubeSide m) (B := oddCubeSide m) (C := oddCubeSide m)
    (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
    (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
    (by dsimp [oddCubeSide]; omega)
  let outer := cubicalEdgeChart 1 1 1
    (a := oddCubeSide m) (b := oddCubeSide m) (c := oddCubeSide m)
    (A := (m + 1) + centralSquareSide n + (m + 1))
    (B := (m + 1) + centralSquareSide n + (m + 1))
    (C := (m + 1) + (m + 1))
    (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
    (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
    (by dsimp [oddCubeSide]; omega)
  let target := cubicalEdgeChart (m + 1) (m + 1) (m + 1)
    (a := centralSquareSide n) (b := centralSquareSide n) (c := 0)
    (A := (m + 1) + centralSquareSide n + (m + 1))
    (B := (m + 1) + centralSquareSide n + (m + 1))
    (C := (m + 1) + (m + 1))
    (by omega) (by omega) (by omega)
  have hmap : (L.map inner).map outer = L.map target := by
    rw [Finset.map_map]
    congr 1
    ext e
    simpa [inner, outer, target, Nat.add_comm] using
      (cubicalEdgeChart_comp_apply m m m 1 1 1
        hinnerXY hinnerXY hinnerZ houterXY houterXY houterZ e)
  have h := cubicalWilsonExpectation_le_chart
    (a := oddCubeSide m) (b := oddCubeSide m) (c := oddCubeSide m)
    (A := (m + 1) + centralSquareSide n + (m + 1))
    (B := (m + 1) + centralSquareSide n + (m + 1))
    (C := (m + 1) + (m + 1))
    1 1 1
    (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
    (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
    (by dsimp [oddCubeSide]; omega) hK (L.map inner)
  rw [hmap] at h
  simpa [cubicalInternalCentralWilsonExpectation,
    gaugeSurfaceBoundary_cubicalInternalCentralSheet_fixed,
    cubicalFixedLoopWilsonSequence, cubicalPaddedWilsonExpectation,
    L, inner, target] using h



theorem cubicalFixedLoopWilsonSequence_le_internal
    {K : Real} (hK : 0 <= K) (n t m : Nat)
    (hnm : centralSquareSide n <= m)
    (htm : t + centralSquareSide n <= m + 1) :
    cubicalFixedLoopWilsonSequence K (centralSquareSide n)
        (centralSquareSide n) t <=
      cubicalInternalCentralWilsonExpectation K n m hnm := by
  have htm' : t <= m := by
    have hpos : 1 <= centralSquareSide n := by simp [centralSquareSide]
    omega
  have houterXY : m - t + (t + centralSquareSide n + t) <=
      oddCubeSide m := by
    dsimp [oddCubeSide]
    omega
  have houterZ : m - t + (t + t) <= oddCubeSide m := by
    dsimp [oddCubeSide]
    omega
  let L := cubicalXYLoop
    (a := centralSquareSide n) (b := centralSquareSide n) (c := 0)
    (0 : Fin 1)
  let inner := cubicalEdgeChart t t t
    (a := centralSquareSide n) (b := centralSquareSide n) (c := 0)
    (A := t + centralSquareSide n + t)
    (B := t + centralSquareSide n + t) (C := t + t)
    (by omega) (by omega) (by omega)
  let outer := cubicalEdgeChart (m - t) (m - t) (m - t)
    (a := t + centralSquareSide n + t)
    (b := t + centralSquareSide n + t) (c := t + t)
    (A := oddCubeSide m) (B := oddCubeSide m) (C := oddCubeSide m)
    (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
    (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
    (by dsimp [oddCubeSide]; omega)
  let target := cubicalEdgeChart m m m
    (a := centralSquareSide n) (b := centralSquareSide n) (c := 0)
    (A := oddCubeSide m) (B := oddCubeSide m) (C := oddCubeSide m)
    (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
    (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
    (by dsimp [oddCubeSide]; omega)
  have hmap : (L.map inner).map outer = L.map target := by
    rw [Finset.map_map]
    congr 1
    ext e
    simpa [inner, outer, target, Nat.sub_add_cancel htm'] using
      (cubicalEdgeChart_comp_apply t t t (m - t) (m - t) (m - t)
        (by omega) (by omega) (by omega)
        houterXY houterXY houterZ e)
  have h := cubicalWilsonExpectation_le_chart
    (a := t + centralSquareSide n + t)
    (b := t + centralSquareSide n + t) (c := t + t)
    (A := oddCubeSide m) (B := oddCubeSide m) (C := oddCubeSide m)
    (m - t) (m - t) (m - t)
    houterXY houterXY houterZ hK (L.map inner)
  rw [hmap] at h
  simpa [cubicalInternalCentralWilsonExpectation,
    gaugeSurfaceBoundary_cubicalInternalCentralSheet_fixed,
    cubicalFixedLoopWilsonSequence, cubicalPaddedWilsonExpectation,
    L, inner, target] using h



theorem cubicalInternalCentralWilsonExpectation_tendsto
    {K : Real} (hK : 0 < K) (n : Nat)
    (m : Nat -> Nat) (hm : ∀ k, centralSquareSide n <= m k)
    (hmTop : Tendsto m atTop atTop) :
    Tendsto (fun k => cubicalInternalCentralWilsonExpectation K n (m k) (hm k))
      atTop
      (nhds (cubicalInfiniteVolumeWilsonExpectation K
        (centralSquareSide n) (centralSquareSide n))) := by
  apply tendsto_order.2
  constructor
  · intro x hx
    have hcanon : ∀ᶠ t : Nat in atTop,
        x < cubicalFixedLoopWilsonSequence K (centralSquareSide n)
          (centralSquareSide n) t :=
      (cubicalFixedLoopWilsonSequence_tendsto hK
        (centralSquareSide n) (centralSquareSide n)).eventually
        (Ioi_mem_nhds hx)
    obtain ⟨t, ht⟩ := eventually_atTop.1 hcanon
    filter_upwards [hmTop.eventually
      (eventually_ge_atTop (t + centralSquareSide n))] with k hk
    exact (ht t le_rfl).trans_le
      (cubicalFixedLoopWilsonSequence_le_internal hK.le n t (m k)
        (hm k) (by omega))
  · intro y hy
    exact Eventually.of_forall fun k =>
      (cubicalInternalCentralWilsonExpectation_le_fixed_succ
        hK.le n (m k) (hm k)).trans_lt
      ((cubicalPaddedWilsonExpectation_le_infiniteVolume hK
        (centralSquareSide n) (centralSquareSide n)
        (m k + 1) (m k + 1) (m k + 1) (m k + 1)
        (m k + 1) (m k + 1)).trans_lt hy)



theorem centralCylinderPlusCorrProduct_le_infiniteWilson
    (K : Real) (hK : 0 < K) (n : Nat) :
    (∏ uv ∈ centralCylinderPairs n,
      (1 - plusCorr 3 (gaugeDualCoupling K)
        (centralCylinderVertexSite n uv.1)
        (centralCylinderVertexSite n uv.2))) <=
      cubicalInfiniteVolumeWilsonExpectation K
        (centralSquareSide n) (centralSquareSide n) := by
  obtain ⟨m, hm, hmTop, hprod⟩ :=
    exists_internalCentralCylinderProduct_tendsto
      (gaugeDualCoupling K) n
  have hwilson := cubicalInternalCentralWilsonExpectation_tendsto
    hK n m (fun k => (hm k).le) hmTop
  exact le_of_tendsto_of_tendsto hprod hwilson
    (Eventually.of_forall fun k => by
      simpa [internalCentralPairCorrelation,
        cubicalInternalCentralWilsonExpectation] using
        (cubicalInternalCentralWilsonExpectation_ge_fixed_product
          n (m k) (hm k) K hK))



theorem l1dist_centralCylinderVertexSite
    (n : Nat) (uv :
      CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
          (centralSquareSide n + centralSquareSide n) ×
        CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
          (centralSquareSide n + centralSquareSide n))
    (huv : uv ∈ centralCylinderPairs n) :
    l1dist 3 (centralCylinderVertexSite n uv.1)
        (centralCylinderVertexSite n uv.2) =
      cubicalDualL1 uv.1 uv.2 := by
  have hmem := Finset.mem_product.mp huv
  rcases uv with ⟨u, v⟩
  cases u with
  | none => exact (none_not_mem_centralLowerBoundaryVertices n hmem.1).elim
  | some q =>
      cases v with
      | none => exact (none_not_mem_centralUpperLayerVertices n hmem.2).elim
      | some r =>
          let m := centralSquareSide n + 1
          have hnm : centralSquareSide n < m := by dsimp [m]; omega
          rw [centralCylinderVertexSite, centralCylinderVertexSite,
            ← oddCubicalCenteredSite_internalCentralCellEmbedding n m hnm q,
            ← oddCubicalCenteredSite_internalCentralCellEmbedding n m hnm r,
            l1dist_oddCubicalCenteredSite]
          simpa only [internalCentralVertexEmbedding_some] using
            (cubicalDualL1_internalCentralVertexEmbedding
              n m hnm (some q) (some r))


theorem centralCylinderPairs_l1_ge_one
    (n : Nat) (uv :
      CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
          (centralSquareSide n + centralSquareSide n) ×
        CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
          (centralSquareSide n + centralSquareSide n))
    (huv : uv ∈ centralCylinderPairs n) :
    (1 : Real) <= cubicalDualL1 uv.1 uv.2 := by
  have hmem := Finset.mem_product.mp huv
  rcases uv with ⟨u, v⟩
  cases u with
  | none => exact (none_not_mem_centralLowerBoundaryVertices n hmem.1).elim
  | some q =>
      cases v with
      | none => exact (none_not_mem_centralUpperLayerVertices n hmem.2).elim
      | some r =>
          have hq := (mem_centralLowerBoundaryVertices_iff n q).mp hmem.1
          obtain ⟨ij, _, hr⟩ := Finset.mem_image.mp hmem.2
          simp only [Option.some.injEq] at hr
          subst r
          simp only [cubicalDualL1]
          exact_mod_cast (show 1 <=
            Nat.dist q.x.val ij.1.val + Nat.dist q.y.val ij.2.val +
              Nat.dist q.z.val (centralSquareSide n) by
            rw [Nat.dist_eq_sub_of_le hq.1.le]
            omega)


theorem centralCylinderPairs_exp_l1_sum_le
    (decay : Real) (hdecay : 0 < decay) (n : Nat) :
    (∑ uv ∈ centralCylinderPairs n,
      Real.exp (-decay * (cubicalDualL1 uv.1 uv.2 : Real))) <=
      20 * ((1 - Real.exp (-decay))⁻¹) ^ 3 * centralSquareSide n := by
  rw [show (∑ uv ∈ centralCylinderPairs n,
      Real.exp (-decay * (cubicalDualL1 uv.1 uv.2 : Real))) =
      ∑ uv ∈ centralCylinderPairs n,
        Real.exp (-decay) ^ cubicalDualL1 uv.1 uv.2 by
    apply Finset.sum_congr rfl
    intro uv _
    exact exp_neg_mul_natCast_eq_pow_exp_neg decay _]
  calc
    _ <= squareLowerCapExpSum (Real.exp (-decay)) (centralSquareSide n) +
        squareXSideExpSum (Real.exp (-decay))
          (0 : Fin (centralSquareSide n)) +
        squareXSideExpSum (Real.exp (-decay)) (Fin.last n) +
        squareYSideExpSum (Real.exp (-decay))
          (0 : Fin (centralSquareSide n)) +
        squareYSideExpSum (Real.exp (-decay)) (Fin.last n) :=
      centralLowerBoundary_doubleSum_le_coordinate (Real.exp_pos _).le n
    _ <= 20 * ((1 - Real.exp (-decay))⁻¹) ^ 3 * centralSquareSide n :=
      squareCylinderCoordinateExpSum_le_inv (Real.exp_pos _).le
        (by rw [Real.exp_lt_one_iff]; linarith)
        (0 : Fin (centralSquareSide n)) (Fin.last n)
        (0 : Fin (centralSquareSide n)) (Fin.last n)



theorem exists_cubicalInfiniteVolumeWilson_perimeterLower_of_dual_lt_betaC
    (K : Real) (hK : 0 < K)
    (hlt : gaugeDualCoupling K < betaC 3) :
    ∃ decay > 0, ∀ n,
      Real.exp
        (-(gaugePerimeterPenalty (Real.exp (-decay)) *
            (20 * ((1 - Real.exp (-decay))⁻¹) ^ 3)) *
          centralSquareSide n) <=
        cubicalInfiniteVolumeWilsonExpectation K
          (centralSquareSide n) (centralSquareSide n) := by
  have hdual0 : 0 <= gaugeDualCoupling K :=
    (gaugeDualCoupling_pos hK).le
  obtain ⟨decay, hdecay, hcorr⟩ :=
    plusCorr_allPairs_exponential_of_lt_betaC (d := 3) (by norm_num)
      hdual0 hlt
  refine ⟨decay, hdecay, fun n => ?_⟩
  let corr := fun uv :
      CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
          (centralSquareSide n + centralSquareSide n) ×
        CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
          (centralSquareSide n + centralSquareSide n) =>
    plusCorr 3 (gaugeDualCoupling K)
      (centralCylinderVertexSite n uv.1)
      (centralCylinderVertexSite n uv.2)
  apply gauge_perimeterLaw_of_product_and_sum_bounds
    (Real.exp_pos _) (by rw [Real.exp_lt_one_iff]; linarith)
    (centralCylinderPairs n) corr
  · intro uv _
    exact plusCorr_nonneg (gaugeDualCoupling K) hdual0 _ _
  · intro uv huv
    calc
      corr uv <= Real.exp
          (-decay * (l1dist 3
            (centralCylinderVertexSite n uv.1)
            (centralCylinderVertexSite n uv.2) : Real)) := hcorr _ _
      _ = Real.exp
          (-decay * (cubicalDualL1 uv.1 uv.2 : Real)) := by
        rw [l1dist_centralCylinderVertexSite n uv huv]
      _ <= Real.exp (-decay) := by
        rw [Real.exp_le_exp]
        nlinarith [centralCylinderPairs_l1_ge_one n uv huv]
  · exact centralCylinderPlusCorrProduct_le_infiniteWilson K hK n
  · calc
      (∑ uv ∈ centralCylinderPairs n, corr uv) <=
          ∑ uv ∈ centralCylinderPairs n,
            Real.exp (-decay * (cubicalDualL1 uv.1 uv.2 : Real)) := by
        apply Finset.sum_le_sum
        intro uv huv
        rw [← l1dist_centralCylinderVertexSite n uv huv]
        exact hcorr _ _
      _ <= 20 * ((1 - Real.exp (-decay))⁻¹) ^ 3 *
          centralSquareSide n :=
        centralCylinderPairs_exp_l1_sum_le decay hdecay n


theorem isingBetaC_three_pos : 0 < betaC 3 := by
  have hbdd := tildeBetaCIsingSet_bddAbove (d := 3) (by norm_num)
  have hcrit := tildeBetaCIsing_pos (d := 3) (by norm_num)
  have hsqrt : ∀ beta, tildeBetaCIsing 3 <= beta ->
      Real.sqrt (1 - (tildeBetaCIsing 3 / beta) ^ 2) <=
        magnetization 3 beta := fun beta hbeta =>
    sct_magnetization_meanfield_lower_bound_integrated 3 hbdd hcrit hbeta
  rw [bc_eq_ising_of_sqrt_and_susceptibility (d := 3) (by norm_num) hsqrt]
  exact hcrit


theorem exists_cubicalInfiniteVolumeWilson_perimeterLower_of_critical_lt
    (K : Real) (hK : 0 < K)
    (hhigh : gaugeCriticalCoupling (betaC 3) < K) :
    ∃ decay > 0, ∀ n,
      Real.exp
        (-(gaugePerimeterPenalty (Real.exp (-decay)) *
            (20 * ((1 - Real.exp (-decay))⁻¹) ^ 3)) *
          centralSquareSide n) <=
        cubicalInfiniteVolumeWilsonExpectation K
          (centralSquareSide n) (centralSquareSide n) := by
  apply exists_cubicalInfiniteVolumeWilson_perimeterLower_of_dual_lt_betaC
    K hK
  exact (gaugeDualCoupling_lt_iff_gaugeCriticalCoupling_lt
    hK isingBetaC_three_pos).2 hhigh

end

end StatMech.FrontierA
