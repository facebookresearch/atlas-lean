/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.TwoDim.ZhangBKData
import Code.Universality.FrameChangeIso
import Code.Universality.CrossingReflection
import Code.Universality.RSWLowestCrossing
import Code.Universality.KestenBXPWire

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation
open StatMech.RSW.Box



noncomputable def zfk_rotBoxIso
    (omega : ConfigSpace (Sym2 (Site 2))) (N : ℕ) :
    openSubgraphInduce 2 (kdi_rotConfig omega) (box 2 N) ≃g
      openSubgraphInduce 2 omega (box 2 N) where
  toEquiv :=
    { toFun := fun x => ⟨rot90Inv x, rot90Inv_mem_box N x.2⟩
      invFun := fun x => ⟨rot90Fun x, rot90Fun_mem_box N x.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact Equiv.apply_symm_apply rot90Equiv x
      right_inv := fun x => by
        apply Subtype.ext
        exact Equiv.symm_apply_apply rot90Equiv x }
  map_rel_iff' := by
    intro x y
    simp only [openSubgraphInduce_adj]
    exact (zbd_rotOpenIso omega).map_rel_iff

theorem zfk_rot_connectedWithin_box_iff
    (omega : ConfigSpace (Sym2 (Site 2))) (N : ℕ) (x y : box 2 N) :
    ConnectedWithin 2 (kdi_rotConfig omega) (box 2 N) x y ↔
      ConnectedWithin 2 omega (box 2 N)
        ⟨rot90Inv x, rot90Inv_mem_box N x.2⟩
        ⟨rot90Inv y, rot90Inv_mem_box N y.2⟩ := by
  exact (zfk_rotBoxIso omega N).reachable_iff.symm

noncomputable def zfk_translateOpenIso (t : Site 2)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    openSubgraph 2 (translateConfig t omega) ≃g openSubgraph 2 omega where
  toEquiv := Equiv.addRight t
  map_rel_iff' := fun {x y} => (cti_isOpenEdge_translate t omega x y).symm

theorem zfk_translate_clusterInfinite_iff (t : Site 2)
    (omega : ConfigSpace (Sym2 (Site 2))) (x : Site 2) :
    (cluster 2 (translateConfig t omega) x).Infinite ↔
      (cluster 2 omega (x + t)).Infinite := by
  let e : Site 2 ≃ Site 2 := Equiv.addRight t
  have himage : e '' cluster 2 (translateConfig t omega) x =
      cluster 2 omega (e x) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (zfk_translateOpenIso t omega).reachable_iff.mpr hy
    · intro hz
      refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      apply (zfk_translateOpenIso t omega).reachable_iff.mp
      change Connected 2 omega (x + t) (e.symm z + t)
      have he : e.symm z + t = z := e.apply_symm_apply z
      rwa [he]
  change (cluster 2 (translateConfig t omega) x).Infinite ↔
    (cluster 2 omega (e x)).Infinite
  rw [← himage]
  exact (Set.infinite_image_iff e.injective.injOn).symm

theorem zfk_connectedWithin_translate_iff
    (a b c d : ℤ) (t : Site 2) (omega : ConfigSpace (Sym2 (Site 2)))
    (x y : Site 2) (hx : x ∈ rect a b c d) (hy : y ∈ rect a b c d) :
    ConnectedWithin 2 (translateConfig t omega) (rect a b c d)
        ⟨x, hx⟩ ⟨y, hy⟩ ↔
      ConnectedWithin 2 omega
        (rect (a + t 0) (b + t 0) (c + t 1) (d + t 1))
        ⟨x + t, (cti_mem_rect_translate a b c d t x).mp hx⟩
        ⟨y + t, (cti_mem_rect_translate a b c d t y).mp hy⟩ := by
  constructor
  · intro h
    exact h.map (cti_inducedHom a b c d t omega)
  · intro h
    have hm := h.map (cti_inducedHomInv a b c d t omega)
    convert hm using 1 <;> apply Subtype.ext <;> simp [cti_inducedHomInv]


def zfk_rightCentralBox (k : ℕ) : Set (Site 2) :=
  {x | x - ![1, 0] ∈ box 2 k}


def zfk_leftSquare (N : ℕ) : Set (Site 2) :=
  rect (-(N : ℤ)) N (-(N : ℤ)) N


def zfk_rightSquare (N : ℕ) : Set (Site 2) :=
  rect (-(N : ℤ) + 1) (N + 1) (-(N : ℤ)) N

theorem zfk_shift_mem_rightSquare_iff (N : ℕ) (x : Site 2) :
    x ∈ zfk_leftSquare N ↔ x + (![1, 0] : Site 2) ∈ zfk_rightSquare N := by
  have hR : rect (-(N : ℤ) + (![1, 0] : Site 2) 0)
        ((N : ℤ) + (![1, 0] : Site 2) 0)
        (-(N : ℤ) + (![1, 0] : Site 2) 1)
        ((N : ℤ) + (![1, 0] : Site 2) 1) = zfk_rightSquare N := by
    congr 1 <;> norm_num [zfk_rightSquare]
  rw [zfk_leftSquare, ← hR]
  exact cti_mem_rect_translate (-(N : ℤ)) N (-(N : ℤ)) N ![1, 0] x

noncomputable def zfk_shiftRightHom (N : ℕ)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    openSubgraphInduce 2 (translateConfig (![1, 0] : Site 2) omega)
        (zfk_leftSquare N) →g
      openSubgraphInduce 2 omega (zfk_rightSquare N) where
  toFun := fun x => ⟨(x : Site 2) + ![1, 0],
    (zfk_shift_mem_rightSquare_iff N x).mp x.2⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy ⊢
    exact (cti_isOpenEdge_translate (![1, 0] : Site 2) omega x y).mp hxy

noncomputable def zfk_shiftRightHomInv (N : ℕ)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    openSubgraphInduce 2 omega (zfk_rightSquare N) →g
      openSubgraphInduce 2 (translateConfig (![1, 0] : Site 2) omega)
        (zfk_leftSquare N) where
  toFun := fun x => ⟨(x : Site 2) - ![1, 0], by
    rw [zfk_shift_mem_rightSquare_iff N]
    simpa only [sub_add_cancel] using x.2⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy ⊢
    apply (cti_isOpenEdge_translate (![1, 0] : Site 2) omega
      ((x : Site 2) - ![1, 0]) ((y : Site 2) - ![1, 0])).mpr
    simpa only [sub_add_cancel] using hxy

theorem zfk_connectedWithin_shiftRight_iff
    (omega : ConfigSpace (Sym2 (Site 2))) (N : ℕ) (x y : Site 2)
    (hx : x ∈ zfk_leftSquare N) (hy : y ∈ zfk_leftSquare N) :
    ConnectedWithin 2 (translateConfig (![1, 0] : Site 2) omega)
        (zfk_leftSquare N) ⟨x, hx⟩ ⟨y, hy⟩ ↔
      ConnectedWithin 2 omega (zfk_rightSquare N)
        ⟨x + ![1, 0], (zfk_shift_mem_rightSquare_iff N x).mp hx⟩
        ⟨y + ![1, 0], (zfk_shift_mem_rightSquare_iff N y).mp hy⟩ := by
  constructor
  · intro h
    exact h.map (zfk_shiftRightHom N omega)
  · intro h
    have hm := h.map (zfk_shiftRightHomInv N omega)
    convert hm using 1 <;> apply Subtype.ext <;> simp [zfk_shiftRightHomInv] <;>
      apply funext <;> intro i <;> fin_cases i <;> rfl



def zfk_matchedRect (N : ℕ) : Set (Site 2) :=
  rect (-(N : ℤ)) (N + 1) (-(N : ℤ)) N



def zfk_LeftArmFrom (omega : ConfigSpace (Sym2 (Site 2))) (x : Site 2) (N : ℕ) : Prop :=
  ∃ (hx : x ∈ zfk_leftSquare N)
      (a : StatMech.RSW.Box.leftSide
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)),
    ConnectedWithin 2 omega (zfk_leftSquare N)
      ⟨(a : Site 2), StatMech.RSW.Box.leftSide_subset a.2⟩ ⟨x, hx⟩



def zfk_RightArmFrom (omega : ConfigSpace (Sym2 (Site 2))) (y : Site 2) (N : ℕ) : Prop :=
  ∃ (hy : y ∈ zfk_rightSquare N)
      (b : StatMech.RSW.Box.rightSide
        (-(N : ℤ) + 1) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)),
    ConnectedWithin 2 omega (zfk_rightSquare N)
      ⟨y, hy⟩ ⟨(b : Site 2), StatMech.RSW.Box.rightSide_subset b.2⟩



def zfk_ArmPairEvent (k N : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | ∃ x ∈ box 2 k, ∃ y ∈ zfk_rightCentralBox k,
    (cluster 2 omega x).Infinite ∧ (cluster 2 omega y).Infinite ∧
      zfk_LeftArmFrom omega x N ∧ zfk_RightArmFrom omega y N}

def zfk_LeftArmEvent (k N : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | ∃ x ∈ box 2 k,
    (cluster 2 omega x).Infinite ∧ zfk_LeftArmFrom omega x N}

def zfk_RightArmEvent (k N : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | ∃ y ∈ zfk_rightCentralBox k,
    (cluster 2 omega y).Infinite ∧ zfk_RightArmFrom omega y N}


def zfk_TopArmEvent (k N : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | ∃ x ∈ box 2 k, (cluster 2 omega x).Infinite ∧
    ∃ (hx : x ∈ zfk_leftSquare N)
      (a : StatMech.RSW.Box.topSide
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)),
      ConnectedWithin 2 omega (zfk_leftSquare N)
        ⟨(a : Site 2), StatMech.RSW.Box.topSide_subset a.2⟩ ⟨x, hx⟩}

def zfk_CenteredRightArmEvent (k N : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | ∃ x ∈ box 2 k, (cluster 2 omega x).Infinite ∧
    ∃ (hx : x ∈ zfk_leftSquare N)
      (a : StatMech.RSW.Box.rightSide
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)),
      ConnectedWithin 2 omega (zfk_leftSquare N)
        ⟨(a : Site 2), StatMech.RSW.Box.rightSide_subset a.2⟩ ⟨x, hx⟩}

def zfk_BottomArmEvent (k N : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | ∃ x ∈ box 2 k, (cluster 2 omega x).Infinite ∧
    ∃ (hx : x ∈ zfk_leftSquare N)
      (a : StatMech.RSW.Box.bottomSide
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)),
      ConnectedWithin 2 omega (zfk_leftSquare N)
        ⟨(a : Site 2), StatMech.RSW.Box.bottomSide_subset a.2⟩ ⟨x, hx⟩}

theorem zfk_rotInv_mem_leftSquare (N : ℕ) {x : Site 2}
    (hx : x ∈ zfk_leftSquare N) : rot90Inv x ∈ zfk_leftSquare N := by
  have hxB : x ∈ box 2 N := by
    exact (zbd_mem_box_iff_rect N x).mpr (by simpa [zfk_leftSquare] using hx)
  have hrB := rot90Inv_mem_box N hxB
  simpa [zfk_leftSquare] using (zbd_mem_box_iff_rect N (rot90Inv x)).mp hrB

theorem zfk_rotFun_mem_leftSquare (N : ℕ) {x : Site 2}
    (hx : x ∈ zfk_leftSquare N) : rot90Fun x ∈ zfk_leftSquare N := by
  have hxB : x ∈ box 2 N := by
    exact (zbd_mem_box_iff_rect N x).mpr (by simpa [zfk_leftSquare] using hx)
  have hrB := rot90Fun_mem_box N hxB
  simpa [zfk_leftSquare] using (zbd_mem_box_iff_rect N (rot90Fun x)).mp hrB

theorem zfk_rotInv_leftSide_mem_topSide (N : ℕ)
    (a : StatMech.RSW.Box.leftSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)) :
    rot90Inv a ∈ StatMech.RSW.Box.topSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) := by
  rw [StatMech.RSW.Box.mem_topSide]
  refine ⟨zfk_rotInv_mem_leftSquare N
    (StatMech.RSW.Box.leftSide_subset a.2), ?_⟩
  have ha := a.2.2
  simp [rot90Inv, ha]

theorem zfk_rotFun_topSide_mem_leftSide (N : ℕ)
    (a : StatMech.RSW.Box.topSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)) :
    rot90Fun a ∈ StatMech.RSW.Box.leftSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) := by
  rw [StatMech.RSW.Box.mem_leftSide]
  refine ⟨zfk_rotFun_mem_leftSquare N
    (StatMech.RSW.Box.topSide_subset a.2), ?_⟩
  have ha := a.2.2
  simp [rot90Fun, ha]

theorem zfk_rotInv_topSide_mem_rightSide (N : ℕ)
    (a : StatMech.RSW.Box.topSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)) :
    rot90Inv a ∈ StatMech.RSW.Box.rightSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) := by
  rw [StatMech.RSW.Box.mem_rightSide]
  refine ⟨zfk_rotInv_mem_leftSquare N
    (StatMech.RSW.Box.topSide_subset a.2), ?_⟩
  have ha := a.2.2
  simp [rot90Inv, ha]

theorem zfk_rotFun_rightSide_mem_topSide (N : ℕ)
    (a : StatMech.RSW.Box.rightSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)) :
    rot90Fun a ∈ StatMech.RSW.Box.topSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) := by
  rw [StatMech.RSW.Box.mem_topSide]
  refine ⟨zfk_rotFun_mem_leftSquare N
    (StatMech.RSW.Box.rightSide_subset a.2), ?_⟩
  have ha := a.2.2
  simp [rot90Fun, ha]

theorem zfk_rotInv_rightSide_mem_bottomSide (N : ℕ)
    (a : StatMech.RSW.Box.rightSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)) :
    rot90Inv a ∈ StatMech.RSW.Box.bottomSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) := by
  rw [StatMech.RSW.Box.mem_bottomSide]
  refine ⟨zfk_rotInv_mem_leftSquare N
    (StatMech.RSW.Box.rightSide_subset a.2), ?_⟩
  have ha := a.2.2
  simp [rot90Inv, ha]

theorem zfk_rotFun_bottomSide_mem_rightSide (N : ℕ)
    (a : StatMech.RSW.Box.bottomSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)) :
    rot90Fun a ∈ StatMech.RSW.Box.rightSide
      (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) := by
  rw [StatMech.RSW.Box.mem_rightSide]
  refine ⟨zfk_rotFun_mem_leftSquare N
    (StatMech.RSW.Box.bottomSide_subset a.2), ?_⟩
  have ha := a.2.2
  simp [rot90Fun, ha]

theorem zfk_rot_connectedWithin_leftSquare_iff
    (omega : ConfigSpace (Sym2 (Site 2))) (N : ℕ)
    {x y : Site 2} (hx : x ∈ zfk_leftSquare N) (hy : y ∈ zfk_leftSquare N) :
    ConnectedWithin 2 (kdi_rotConfig omega) (zfk_leftSquare N) ⟨x, hx⟩ ⟨y, hy⟩ ↔
      ConnectedWithin 2 omega (zfk_leftSquare N)
        ⟨rot90Inv x, zfk_rotInv_mem_leftSquare N hx⟩
        ⟨rot90Inv y, zfk_rotInv_mem_leftSquare N hy⟩ := by
  have hto : zfk_leftSquare N ⊆ box 2 N := by
    intro z hz
    exact (zbd_mem_box_iff_rect N z).mpr (by simpa [zfk_leftSquare] using hz)
  have hfrom : box 2 N ⊆ zfk_leftSquare N := by
    intro z hz
    simpa [zfk_leftSquare] using (zbd_mem_box_iff_rect N z).mp hz
  constructor
  · intro h
    have hb := StatMech.RSW.Strip.connectedWithin_mono_set
      (kdi_rotConfig omega) hto h
    have hr := (zfk_rot_connectedWithin_box_iff omega N
      ⟨x, hto hx⟩ ⟨y, hto hy⟩).mp hb
    exact StatMech.RSW.Strip.connectedWithin_mono_set omega hfrom hr
  · intro h
    have hb := StatMech.RSW.Strip.connectedWithin_mono_set omega hto h
    have hr := (zfk_rot_connectedWithin_box_iff omega N
      ⟨x, hto hx⟩ ⟨y, hto hy⟩).mpr hb
    exact StatMech.RSW.Strip.connectedWithin_mono_set
      (kdi_rotConfig omega) hfrom hr

theorem zfk_rot_leftArmEvent_eq_top (k N : ℕ) :
    zrs_rot (zfk_LeftArmEvent k N) = zfk_TopArmEvent k N := by
  ext omega
  change kdi_rotConfig omega ∈ zfk_LeftArmEvent k N ↔ _
  constructor
  · rintro ⟨x, hxK, hxInf, hxS, a, hax⟩
    let x' : Site 2 := rot90Inv x
    let a' : StatMech.RSW.Box.topSide
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) :=
      ⟨rot90Inv a, zfk_rotInv_leftSide_mem_topSide N a⟩
    refine ⟨x', rot90Inv_mem_box k hxK,
      (zbd_rot_clusterInfinite_iff omega x).mp hxInf,
      zfk_rotInv_mem_leftSquare N hxS, a', ?_⟩
    exact (zfk_rot_connectedWithin_leftSquare_iff omega N
      (StatMech.RSW.Box.leftSide_subset a.2) hxS).mp hax
  · rintro ⟨x, hxK, hxInf, hxS, a, hax⟩
    let x' : Site 2 := rot90Fun x
    let a' : StatMech.RSW.Box.leftSide
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) :=
      ⟨rot90Fun a, zfk_rotFun_topSide_mem_leftSide N a⟩
    refine ⟨x', rot90Fun_mem_box k hxK, ?_,
      zfk_rotFun_mem_leftSquare N hxS, a', ?_⟩
    · apply (zbd_rot_clusterInfinite_iff omega x').mpr
      have hix : rot90Inv x' = x := by
        exact Equiv.symm_apply_apply rot90Equiv x
      rwa [hix]
    · apply (zfk_rot_connectedWithin_leftSquare_iff omega N
        (StatMech.RSW.Box.leftSide_subset a'.2)
        (zfk_rotFun_mem_leftSquare N hxS)).mpr
      have hix : rot90Inv x' = x := Equiv.symm_apply_apply rot90Equiv x
      have hia : rot90Inv (a' : Site 2) = (a : Site 2) :=
        Equiv.symm_apply_apply rot90Equiv a
      convert hax using 1 <;> apply Subtype.ext
      · exact hia
      · exact hix

theorem zfk_rot_topArmEvent_eq_right (k N : ℕ) :
    zrs_rot (zfk_TopArmEvent k N) = zfk_CenteredRightArmEvent k N := by
  ext omega
  change kdi_rotConfig omega ∈ zfk_TopArmEvent k N ↔ _
  constructor
  · rintro ⟨x, hxK, hxInf, hxS, a, hax⟩
    let x' : Site 2 := rot90Inv x
    let a' : StatMech.RSW.Box.rightSide
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) :=
      ⟨rot90Inv a, zfk_rotInv_topSide_mem_rightSide N a⟩
    refine ⟨x', rot90Inv_mem_box k hxK,
      (zbd_rot_clusterInfinite_iff omega x).mp hxInf,
      zfk_rotInv_mem_leftSquare N hxS, a', ?_⟩
    exact (zfk_rot_connectedWithin_leftSquare_iff omega N
      (StatMech.RSW.Box.topSide_subset a.2) hxS).mp hax
  · rintro ⟨x, hxK, hxInf, hxS, a, hax⟩
    let x' : Site 2 := rot90Fun x
    let a' : StatMech.RSW.Box.topSide
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) :=
      ⟨rot90Fun a, zfk_rotFun_rightSide_mem_topSide N a⟩
    refine ⟨x', rot90Fun_mem_box k hxK, ?_,
      zfk_rotFun_mem_leftSquare N hxS, a', ?_⟩
    · apply (zbd_rot_clusterInfinite_iff omega x').mpr
      have hix : rot90Inv x' = x := Equiv.symm_apply_apply rot90Equiv x
      rwa [hix]
    · apply (zfk_rot_connectedWithin_leftSquare_iff omega N
        (StatMech.RSW.Box.topSide_subset a'.2)
        (zfk_rotFun_mem_leftSquare N hxS)).mpr
      have hix : rot90Inv x' = x := Equiv.symm_apply_apply rot90Equiv x
      have hia : rot90Inv (a' : Site 2) = (a : Site 2) :=
        Equiv.symm_apply_apply rot90Equiv a
      convert hax using 1 <;> apply Subtype.ext
      · exact hia
      · exact hix

theorem zfk_rot_rightArmEvent_eq_bottom (k N : ℕ) :
    zrs_rot (zfk_CenteredRightArmEvent k N) = zfk_BottomArmEvent k N := by
  ext omega
  change kdi_rotConfig omega ∈ zfk_CenteredRightArmEvent k N ↔ _
  constructor
  · rintro ⟨x, hxK, hxInf, hxS, a, hax⟩
    let x' : Site 2 := rot90Inv x
    let a' : StatMech.RSW.Box.bottomSide
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) :=
      ⟨rot90Inv a, zfk_rotInv_rightSide_mem_bottomSide N a⟩
    refine ⟨x', rot90Inv_mem_box k hxK,
      (zbd_rot_clusterInfinite_iff omega x).mp hxInf,
      zfk_rotInv_mem_leftSquare N hxS, a', ?_⟩
    exact (zfk_rot_connectedWithin_leftSquare_iff omega N
      (StatMech.RSW.Box.rightSide_subset a.2) hxS).mp hax
  · rintro ⟨x, hxK, hxInf, hxS, a, hax⟩
    let x' : Site 2 := rot90Fun x
    let a' : StatMech.RSW.Box.rightSide
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) :=
      ⟨rot90Fun a, zfk_rotFun_bottomSide_mem_rightSide N a⟩
    refine ⟨x', rot90Fun_mem_box k hxK, ?_,
      zfk_rotFun_mem_leftSquare N hxS, a', ?_⟩
    · apply (zbd_rot_clusterInfinite_iff omega x').mpr
      have hix : rot90Inv x' = x := Equiv.symm_apply_apply rot90Equiv x
      rwa [hix]
    · apply (zfk_rot_connectedWithin_leftSquare_iff omega N
        (StatMech.RSW.Box.rightSide_subset a'.2)
        (zfk_rotFun_mem_leftSquare N hxS)).mpr
      have hix : rot90Inv x' = x := Equiv.symm_apply_apply rot90Equiv x
      have hia : rot90Inv (a' : Site 2) = (a : Site 2) :=
        Equiv.symm_apply_apply rot90Equiv a
      convert hax using 1 <;> apply Subtype.ext
      · exact hia
      · exact hix



theorem zfk_boxHitsInfinite_subset_armUnion (k N : ℕ) (hkN : k ≤ N) :
    zbd_boxHitsInfinite k ⊆
      zrs_sideFamily (zfk_LeftArmEvent k N) 0 ∪
        zrs_sideFamily (zfk_LeftArmEvent k N) 1 ∪
        zrs_sideFamily (zfk_LeftArmEvent k N) 2 ∪
        zrs_sideFamily (zfk_LeftArmEvent k N) 3 := by
  intro omega
  rintro ⟨x, hxK, hxInf⟩
  obtain ⟨y, hyOutside, hxy⟩ := (cluster_infinite_iff omega x).mp hxInf N
  rcases hxy with ⟨w⟩
  classical
  let P : ℕ → Prop := fun m => w.getVert m ∉ box 2 N
  have hPend : P w.length := by simpa [P] using hyOutside
  let j := Nat.find ⟨w.length, hPend⟩
  have hjP : w.getVert j ∉ box 2 N := Nat.find_spec ⟨w.length, hPend⟩
  have hjle : j ≤ w.length := Nat.find_le hPend
  have hxN : x ∈ box 2 N := box_mono 2 hkN hxK
  have hj0 : j ≠ 0 := by
    intro hj
    rw [hj, w.getVert_zero] at hjP
    exact hjP hxN
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hmlt : m < w.length := by omega
  have hmnotP : ¬ P m := Nat.find_min ⟨w.length, hPend⟩ (by omega)
  have hmBox : w.getVert m ∈ box 2 N := by simpa [P] using hmnotP
  have hmRect : w.getVert m ∈ zfk_leftSquare N := by
    simpa [zfk_leftSquare] using (zbd_mem_box_iff_rect N (w.getVert m)).mp hmBox
  have hprefixSupp : ∀ z ∈ (w.take m).support, z ∈ box 2 N := by
    intro z hz
    rw [SimpleGraph.Walk.take_support_eq_support_take_succ] at hz
    obtain ⟨r, hrlt, hrz⟩ := List.mem_iff_getElem.mp hz
    rw [List.length_take] at hrlt
    have hrle : r ≤ m := by omega
    have hrw : z = w.getVert r := by
      have hrlen : r ≤ w.length := by omega
      rw [List.getElem_take] at hrz
      rw [← hrz, ← SimpleGraph.Walk.getVert_eq_support_getElem w hrlen]
    rw [hrw]
    by_contra hrout
    have : P r := by simpa [P] using hrout
    exact (Nat.find_min ⟨w.length, hPend⟩ (by omega)) this
  have hxm : ConnectedWithin 2 omega (box 2 N)
      ⟨x, hxN⟩ ⟨w.getVert m, hmBox⟩ :=
    ⟨(w.take m).induce (box 2 N) hprefixSupp⟩
  have hxmRect : ConnectedWithin 2 omega (zfk_leftSquare N)
      ⟨x, by simpa [zfk_leftSquare] using
        (zbd_mem_box_iff_rect N x).mp hxN⟩ ⟨w.getVert m, hmRect⟩ := by
    have hsub : box 2 N ⊆ zfk_leftSquare N := by
      intro z hz
      simpa [zfk_leftSquare] using (zbd_mem_box_iff_rect N z).mp hz
    exact StatMech.RSW.Strip.connectedWithin_mono_set omega hsub hxm
  have hnextOutside : w.getVert (m + 1) ∉ box 2 N := by
    simpa [hm] using hjP
  have hadj := w.adj_getVert_succ hmlt
  rw [mem_box] at hnextOutside
  push Not at hnextOutside
  obtain ⟨i, hiOutside⟩ := hnextOutside
  have hmLe : ((w.getVert m) i).natAbs ≤ N := by
    rw [mem_box] at hmBox
    exact hmBox i
  have hdiff : (((w.getVert (m + 1)) i) - ((w.getVert m) i)).natAbs ≤ 1 := by
    have h := bxa_adj_coord_diff_le hadj.1 i
    rw [show (w.getVert (m + 1)) i - (w.getVert m) i =
      -((w.getVert m) i - (w.getVert (m + 1)) i) by ring, Int.natAbs_neg]
    exact h
  have htri : ((w.getVert (m + 1)) i).natAbs ≤
      (((w.getVert (m + 1)) i) - ((w.getVert m) i)).natAbs +
        ((w.getVert m) i).natAbs := by
    have h := Int.natAbs_add_le
      (((w.getVert (m + 1)) i) - ((w.getVert m) i)) ((w.getVert m) i)
    rw [show ((w.getVert (m + 1)) i - (w.getVert m) i) + (w.getVert m) i =
      (w.getVert (m + 1)) i by ring] at h
    exact h
  have hmEq : ((w.getVert m) i).natAbs = N := by omega
  change omega ∈ zfk_LeftArmEvent k N ∪
    zrs_rot (zrs_rot (zfk_LeftArmEvent k N)) ∪
    zrs_rot (zfk_LeftArmEvent k N) ∪
    zrs_rot (zrs_rot (zrs_rot (zfk_LeftArmEvent k N)))
  rw [zfk_rot_leftArmEvent_eq_top, zfk_rot_topArmEvent_eq_right,
    zfk_rot_rightArmEvent_eq_bottom]
  have hsign := Int.natAbs_eq ((w.getVert m) i)
  fin_cases i
  · rcases hsign with hpos | hneg
    · change (w.getVert m 0).natAbs = N at hmEq
      change w.getVert m 0 = ((w.getVert m 0).natAbs : ℤ) at hpos
      exact Or.inl (Or.inl (Or.inr ⟨x, hxK, hxInf,
        by simpa [zfk_leftSquare] using (zbd_mem_box_iff_rect N x).mp hxN,
        ⟨w.getVert m, hmRect, by rw [hpos, hmEq]⟩, hxmRect.symm⟩))
    · change (w.getVert m 0).natAbs = N at hmEq
      change w.getVert m 0 = -((w.getVert m 0).natAbs : ℤ) at hneg
      exact Or.inl (Or.inl (Or.inl ⟨x, hxK, hxInf,
        by simpa [zfk_leftSquare] using (zbd_mem_box_iff_rect N x).mp hxN,
        ⟨w.getVert m, hmRect, by rw [hneg, hmEq]⟩, hxmRect.symm⟩))
  · rcases hsign with hpos | hneg
    · change (w.getVert m 1).natAbs = N at hmEq
      change w.getVert m 1 = ((w.getVert m 1).natAbs : ℤ) at hpos
      exact Or.inl (Or.inr ⟨x, hxK, hxInf,
        by simpa [zfk_leftSquare] using (zbd_mem_box_iff_rect N x).mp hxN,
        ⟨w.getVert m, hmRect, by rw [hpos, hmEq]⟩, hxmRect.symm⟩)
    · change (w.getVert m 1).natAbs = N at hmEq
      change w.getVert m 1 = -((w.getVert m 1).natAbs : ℤ) at hneg
      exact Or.inr ⟨x, hxK, hxInf,
        by simpa [zfk_leftSquare] using (zbd_mem_box_iff_rect N x).mp hxN,
        ⟨w.getVert m, hmRect, by rw [hneg, hmEq]⟩, hxmRect.symm⟩

theorem zfk_armPair_eq_inter (k N : ℕ) :
    zfk_ArmPairEvent k N = zfk_LeftArmEvent k N ∩ zfk_RightArmEvent k N := by
  ext omega
  constructor
  · rintro ⟨x, hx, y, hy, hxInf, hyInf, hxArm, hyArm⟩
    exact ⟨⟨x, hx, hxInf, hxArm⟩, ⟨y, hy, hyInf, hyArm⟩⟩
  · rintro ⟨⟨x, hx, hxInf, hxArm⟩, ⟨y, hy, hyInf, hyArm⟩⟩
    exact ⟨x, hx, y, hy, hxInf, hyInf, hxArm, hyArm⟩

theorem zfk_LeftArmEvent_isIncreasing (k N : ℕ) :
    IsIncreasing (zfk_LeftArmEvent k N) := by
  intro omega omega' hle
  rintro ⟨x, hx, hxInf, hxS, a, hax⟩
  refine ⟨x, hx, hxInf.mono (cluster_mono hle x), hxS, a, ?_⟩
  exact StatMech.TwoDim.connectedWithin_mono hle hax

theorem zfk_RightArmEvent_isIncreasing (k N : ℕ) :
    IsIncreasing (zfk_RightArmEvent k N) := by
  intro omega omega' hle
  rintro ⟨y, hy, hyInf, hyS, b, hyb⟩
  refine ⟨y, hy, hyInf.mono (cluster_mono hle y), hyS, b, ?_⟩
  exact StatMech.TwoDim.connectedWithin_mono hle hyb

theorem zfk_LeftArmEvent_measurableSet (k N : ℕ) :
    MeasurableSet (zfk_LeftArmEvent k N) := by
  have heq : zfk_LeftArmEvent k N =
      ⋃ x : Site 2, ⋃ (_hx : x ∈ box 2 k),
        {omega | (cluster 2 omega x).Infinite} ∩
          ⋃ (hxS : x ∈ zfk_leftSquare N),
            ⋃ a : StatMech.RSW.Box.leftSide
              (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ),
              {omega | ConnectedWithin 2 omega (zfk_leftSquare N)
                ⟨(a : Site 2), StatMech.RSW.Box.leftSide_subset a.2⟩ ⟨x, hxS⟩} := by
    ext omega
    constructor
    · rintro ⟨x, hx, hxInf, hxS, a, hax⟩
      exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx,
        ⟨hxInf, Set.mem_iUnion.mpr ⟨hxS, Set.mem_iUnion.mpr ⟨a, hax⟩⟩⟩⟩⟩
    · intro h
      obtain ⟨x, hxrest⟩ := Set.mem_iUnion.mp h
      obtain ⟨hx, hxrest⟩ := Set.mem_iUnion.mp hxrest
      obtain ⟨hxInf, hxrest⟩ := hxrest
      obtain ⟨hxS, hxrest⟩ := Set.mem_iUnion.mp hxrest
      obtain ⟨a, hax⟩ := Set.mem_iUnion.mp hxrest
      exact ⟨x, hx, hxInf, hxS, a, hax⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro x
  apply MeasurableSet.iUnion
  intro hx
  apply (measurableSet_clusterInfinite x).inter
  apply MeasurableSet.iUnion
  intro hxS
  apply MeasurableSet.iUnion
  intro a
  exact zbd_measurableSet_connectedWithin (zfk_leftSquare N)
    ⟨(a : Site 2), StatMech.RSW.Box.leftSide_subset a.2⟩ ⟨x, hxS⟩

theorem zfk_RightArmEvent_measurableSet (k N : ℕ) :
    MeasurableSet (zfk_RightArmEvent k N) := by
  have heq : zfk_RightArmEvent k N =
      ⋃ y : Site 2, ⋃ (_hy : y ∈ zfk_rightCentralBox k),
        {omega | (cluster 2 omega y).Infinite} ∩
          ⋃ (hyS : y ∈ zfk_rightSquare N),
            ⋃ b : StatMech.RSW.Box.rightSide
              (-(N : ℤ) + 1) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ),
              {omega | ConnectedWithin 2 omega (zfk_rightSquare N)
                ⟨y, hyS⟩
                ⟨(b : Site 2), StatMech.RSW.Box.rightSide_subset b.2⟩} := by
    ext omega
    constructor
    · rintro ⟨y, hy, hyInf, hyS, b, hyb⟩
      exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy,
        ⟨hyInf, Set.mem_iUnion.mpr ⟨hyS, Set.mem_iUnion.mpr ⟨b, hyb⟩⟩⟩⟩⟩
    · intro h
      obtain ⟨y, hyrest⟩ := Set.mem_iUnion.mp h
      obtain ⟨hy, hyrest⟩ := Set.mem_iUnion.mp hyrest
      obtain ⟨hyInf, hyrest⟩ := hyrest
      obtain ⟨hyS, hyrest⟩ := Set.mem_iUnion.mp hyrest
      obtain ⟨b, hyb⟩ := Set.mem_iUnion.mp hyrest
      exact ⟨y, hy, hyInf, hyS, b, hyb⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro y
  apply MeasurableSet.iUnion
  intro hy
  apply (measurableSet_clusterInfinite y).inter
  apply MeasurableSet.iUnion
  intro hyS
  apply MeasurableSet.iUnion
  intro b
  exact zbd_measurableSet_connectedWithin (zfk_rightSquare N) ⟨y, hyS⟩
    ⟨(b : Site 2), StatMech.RSW.Box.rightSide_subset b.2⟩


def zfk_MergedArmPairEvent (k N : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | ∃ x ∈ box 2 k, ∃ y ∈ zfk_rightCentralBox k,
    (cluster 2 omega x).Infinite ∧ (cluster 2 omega y).Infinite ∧
      zfk_LeftArmFrom omega x N ∧ zfk_RightArmFrom omega y N ∧
        omega ∈ zbd_connectedWithinBox x y N}

theorem zfk_leftSquare_subset_matched (N : ℕ) :
    zfk_leftSquare N ⊆ zfk_matchedRect N := by
  intro z hz
  simp only [zfk_leftSquare, zfk_matchedRect, mem_rect] at hz ⊢
  omega

theorem zfk_rightSquare_subset_matched (N : ℕ) :
    zfk_rightSquare N ⊆ zfk_matchedRect N := by
  intro z hz
  simp only [zfk_rightSquare, zfk_matchedRect, mem_rect] at hz ⊢
  omega

theorem zfk_box_subset_matched (N : ℕ) :
    box 2 N ⊆ zfk_matchedRect N := by
  intro z hz
  rw [zfk_matchedRect, mem_rect]
  have hz' := (zbd_mem_box_iff_rect N z).mp hz
  rw [mem_rect] at hz'
  omega



theorem zfk_mergedArmPair_subset_horizontalCrossing (k N : ℕ) :
    zfk_MergedArmPairEvent k N ⊆
      StatMech.RSW.Box.horizontalCrossingEvent (-(N : ℤ)) ((N : ℤ) + 1)
        (-(N : ℤ)) (N : ℤ) := by
  intro omega h
  obtain ⟨x, _hxK, y, _hyK, _hxInf, _hyInf, hxArm, hyArm, hxy⟩ := h
  obtain ⟨hxL, a, hax⟩ := hxArm
  obtain ⟨hyR, b, hyb⟩ := hyArm
  obtain ⟨hxB, hyB, hxyB⟩ := hxy
  have hax' : ConnectedWithin 2 omega (zfk_matchedRect N)
      ⟨(a : Site 2), zfk_leftSquare_subset_matched N
        (StatMech.RSW.Box.leftSide_subset a.2)⟩
      ⟨x, zfk_leftSquare_subset_matched N hxL⟩ :=
    StatMech.RSW.Strip.connectedWithin_mono_set omega
      (zfk_leftSquare_subset_matched N) hax
  have hxy' : ConnectedWithin 2 omega (zfk_matchedRect N)
      ⟨x, zfk_box_subset_matched N hxB⟩
      ⟨y, zfk_box_subset_matched N hyB⟩ :=
    StatMech.RSW.Strip.connectedWithin_mono_set omega
      (zfk_box_subset_matched N) hxyB
  have hyb' : ConnectedWithin 2 omega (zfk_matchedRect N)
      ⟨y, zfk_rightSquare_subset_matched N hyR⟩
      ⟨(b : Site 2), zfk_rightSquare_subset_matched N
        (StatMech.RSW.Box.rightSide_subset b.2)⟩ :=
    StatMech.RSW.Strip.connectedWithin_mono_set omega
      (zfk_rightSquare_subset_matched N) hyb
  let a' : StatMech.RSW.Box.leftSide
      (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ) :=
    ⟨a, zfk_leftSquare_subset_matched N
      (StatMech.RSW.Box.leftSide_subset a.2), a.2.2⟩
  let b' : StatMech.RSW.Box.rightSide
      (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ) :=
    ⟨b, zfk_rightSquare_subset_matched N
      (StatMech.RSW.Box.rightSide_subset b.2), b.2.2⟩
  refine ⟨a', b', ?_⟩
  exact hax'.trans (hxy'.trans hyb')





def zfk_pairError (x y : Site 2) (N : ℕ) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  ({omega | (cluster 2 omega x).Infinite} ∩
    {omega | (cluster 2 omega y).Infinite}) \ zbd_connectedWithinBox x y N

theorem zfk_pairError_measurableSet (x y : Site 2) (N : ℕ) :
    MeasurableSet (zfk_pairError x y N) :=
  ((measurableSet_clusterInfinite x).inter
    (measurableSet_clusterInfinite y)).diff
      (zbd_connectedWithinBox_measurableSet x y N)

theorem zfk_pairError_antitone (x y : Site 2) :
    Antitone (zfk_pairError x y) := by
  intro n m hnm omega herror
  exact ⟨herror.1, fun hm => herror.2 (zbd_connectedWithinBox_mono x y hnm hm)⟩

theorem zfk_iInter_pairError_subset_atLeastTwo (x y : Site 2) :
    (⋂ N, zfk_pairError x y N) ⊆ atLeastTwoInfinite 2 := by
  intro omega herror
  have hzero := Set.mem_iInter.mp herror 0
  have hxinf := hzero.1.1
  have hyinf := hzero.1.2
  have hnconn : ¬ Connected 2 omega x y := by
    intro hxy
    obtain ⟨N, hxN, hyN, hwithin⟩ :=
      zbd_connectedWithin_box_of_connected omega hxy
    exact (Set.mem_iInter.mp herror N).2 ⟨hxN, hyN, hwithin⟩
  have hcx : cluster 2 omega x ∈ infiniteClusters 2 omega := ⟨hxinf, x, rfl⟩
  have hcy : cluster 2 omega y ∈ infiniteClusters 2 omega := ⟨hyinf, y, rfl⟩
  have hcne : cluster 2 omega x ≠ cluster 2 omega y := by
    intro heq
    have : y ∈ cluster 2 omega x := heq ▸ self_mem_cluster omega y
    exact hnconn this
  have hnt : (infiniteClusters 2 omega).Nontrivial :=
    ⟨_, hcx, _, hcy, hcne⟩
  have hone : (1 : ℕ∞) < (infiniteClusters 2 omega).encard :=
    Set.one_lt_encard_iff_nontrivial.mpr hnt
  show 2 ≤ numInfiniteClusters 2 omega
  rw [numInfiniteClusters, ← one_add_one_eq_two,
    ENat.add_one_le_iff ENat.one_ne_top]
  exact hone


theorem zfk_pairError_tendsto_zero (x y : Site 2) :
    Tendsto (fun N => halfMeasure.real (zfk_pairError x y N)) atTop (nhds 0) := by
  have hlim : Tendsto (fun N : ℕ => halfMeasure (zfk_pairError x y N)) atTop
      (nhds (halfMeasure (⋂ N, zfk_pairError x y N))) :=
    tendsto_measure_iInter_atTop
      (μ := halfMeasure)
      (fun N => (zfk_pairError_measurableSet x y N).nullMeasurableSet)
      (zfk_pairError_antitone x y)
      ⟨0, measure_ne_top halfMeasure _⟩
  have hinter : halfMeasure (⋂ N, zfk_pairError x y N) = 0 :=
    measure_mono_null (zfk_iInter_pairError_subset_atLeastTwo x y)
      zbd_atLeastTwo_halfMeasure_zero
  rw [hinter] at hlim
  exact (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hlim


theorem zfk_rightCentralBox_finite (k : ℕ) :
    (zfk_rightCentralBox k).Finite := by
  have hinj : Function.Injective (fun x : Site 2 => x - ![1, 0]) := by
    intro x y hxy
    funext i
    have hi := congrFun hxy i
    simp only [Pi.sub_apply] at hi
    omega
  exact Set.Finite.preimage hinj.injOn (box_finite 2 k)

noncomputable def zfk_leftCentralFinset (k : ℕ) : Finset (Site 2) :=
  (box_finite 2 k).toFinset

noncomputable def zfk_rightCentralFinset (k : ℕ) : Finset (Site 2) :=
  (zfk_rightCentralBox_finite k).toFinset

@[simp] theorem zfk_mem_leftCentralFinset {k : ℕ} {x : Site 2} :
    x ∈ zfk_leftCentralFinset k ↔ x ∈ box 2 k := by
  rw [zfk_leftCentralFinset, Set.Finite.mem_toFinset]

@[simp] theorem zfk_mem_rightCentralFinset {k : ℕ} {x : Site 2} :
    x ∈ zfk_rightCentralFinset k ↔ x ∈ zfk_rightCentralBox k := by
  rw [zfk_rightCentralFinset, Set.Finite.mem_toFinset]



def zfk_pairErrorUnion (k N : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  ⋃ x ∈ zfk_leftCentralFinset k, ⋃ y ∈ zfk_rightCentralFinset k,
    zfk_pairError x y N

theorem zfk_armPair_diff_merged_subset_errorUnion (k N : ℕ) :
    zfk_ArmPairEvent k N \ zfk_MergedArmPairEvent k N ⊆
      zfk_pairErrorUnion k N := by
  intro omega h
  obtain ⟨x, hxK, y, hyK, hxInf, hyInf, hxArm, hyArm⟩ := h.1
  have hnotConn : omega ∉ zbd_connectedWithinBox x y N := by
    intro hxy
    exact h.2 ⟨x, hxK, y, hyK, hxInf, hyInf, hxArm, hyArm, hxy⟩
  apply Set.mem_iUnion.mpr
  refine ⟨x, Set.mem_iUnion.mpr ⟨?_, Set.mem_iUnion.mpr ⟨y,
    Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩⟩⟩
  · simpa using hxK
  · simpa using hyK
  · exact ⟨⟨hxInf, hyInf⟩, hnotConn⟩



theorem zfk_pairErrorUnion_tendsto_zero (k : ℕ) :
    Tendsto (fun N => halfMeasure.real (zfk_pairErrorUnion k N))
      atTop (nhds 0) := by
  let F : ℕ → ℝ := fun N =>
    ∑ x ∈ zfk_leftCentralFinset k, ∑ y ∈ zfk_rightCentralFinset k,
      halfMeasure.real (zfk_pairError x y N)
  have hF : Tendsto F atTop (nhds 0) := by
    dsimp [F]
    convert tendsto_finset_sum (zfk_leftCentralFinset k) (fun x _ =>
      tendsto_finset_sum (zfk_rightCentralFinset k) (fun y _ =>
        zfk_pairError_tendsto_zero x y)) using 1 <;> simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hF
  · intro N
    exact measureReal_nonneg
  · intro N
    exact le_trans (measureReal_biUnion_finset_le _ _)
      (Finset.sum_le_sum fun x _ => measureReal_biUnion_finset_le _ _)



theorem zfk_armPair_subset_crossing_union_error (k N : ℕ) :
    zfk_ArmPairEvent k N ⊆
      StatMech.RSW.Box.horizontalCrossingEvent
          (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ) ∪
        zfk_pairErrorUnion k N := by
  intro omega harms
  by_cases hmerge : omega ∈ zfk_MergedArmPairEvent k N
  · exact Or.inl (zfk_mergedArmPair_subset_horizontalCrossing k N hmerge)
  · exact Or.inr (zfk_armPair_diff_merged_subset_errorUnion k N ⟨harms, hmerge⟩)

theorem zfk_armPair_probability_le_crossing_add_error (k N : ℕ) :
    halfMeasure.real (zfk_ArmPairEvent k N) ≤
      halfMeasure.real
          (StatMech.RSW.Box.horizontalCrossingEvent
            (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) +
        halfMeasure.real (zfk_pairErrorUnion k N) := by
  calc
    halfMeasure.real (zfk_ArmPairEvent k N) ≤
        halfMeasure.real
          (StatMech.RSW.Box.horizontalCrossingEvent
              (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ) ∪
            zfk_pairErrorUnion k N) :=
      measureReal_mono (zfk_armPair_subset_crossing_union_error k N)
        (measure_ne_top _ _)
    _ ≤ _ := measureReal_union_le _ _



theorem zfk_armPair_fkg
    (hpa : PositivelyAssociated halfMeasure) (k N : ℕ) :
    halfMeasure.real (zfk_LeftArmEvent k N) *
        halfMeasure.real (zfk_RightArmEvent k N) ≤
      halfMeasure.real (zfk_ArmPairEvent k N) := by
  rw [zfk_armPair_eq_inter]
  exact hpa _ _ (zfk_LeftArmEvent_isIncreasing k N)
    (zfk_RightArmEvent_isIncreasing k N)





theorem zfk_fixedK_contradiction
    (hpa : PositivelyAssociated halfMeasure)
    (q : ℕ → ℝ) (hq : Tendsto q atTop (nhds 1))
    (hqnonneg : ∀ k, 0 ≤ q k)
    (hleft : ∀ k N, k + 1 ≤ N →
      q k ≤ halfMeasure.real (zfk_LeftArmEvent k N))
    (hright : ∀ k N, k + 1 ≤ N →
      q k ≤ halfMeasure.real (zfk_RightArmEvent k N))
    (hhalf : ∀ N : ℕ,
      halfMeasure.real
        (StatMech.RSW.Box.horizontalCrossingEvent
          (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2) :
    False := by
  have hk : ∀ k, q k * q k ≤ (1 : ℝ) / 2 := by
    intro k
    have hpoint : ∀ N, k + 1 ≤ N →
        q k * q k ≤ (1 : ℝ) / 2 +
          halfMeasure.real (zfk_pairErrorUnion k N) := by
      intro N hkN
      calc
        q k * q k ≤
            halfMeasure.real (zfk_LeftArmEvent k N) *
              halfMeasure.real (zfk_RightArmEvent k N) := by
          exact mul_le_mul (hleft k N hkN) (hright k N hkN)
            (hqnonneg k) measureReal_nonneg
        _ ≤ halfMeasure.real (zfk_ArmPairEvent k N) :=
          zfk_armPair_fkg hpa k N
        _ ≤ halfMeasure.real
              (StatMech.RSW.Box.horizontalCrossingEvent
                (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) +
              halfMeasure.real (zfk_pairErrorUnion k N) :=
          zfk_armPair_probability_le_crossing_add_error k N
        _ ≤ (1 : ℝ) / 2 + halfMeasure.real (zfk_pairErrorUnion k N) := by
          gcongr
          exact hhalf N
    have hlim : Tendsto
        (fun N => (1 : ℝ) / 2 + halfMeasure.real (zfk_pairErrorUnion k N))
        atTop (nhds ((1 : ℝ) / 2)) := by
      simpa using tendsto_const_nhds.add (zfk_pairErrorUnion_tendsto_zero k)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      ((eventually_ge_atTop (k + 1)).mono fun N hN => hpoint N hN)
  have hqq : Tendsto (fun k => q k * q k) atTop (nhds 1) := by
    have := hq.mul hq
    simpa using this
  have hbad : (1 : ℝ) ≤ (1 : ℝ) / 2 :=
    le_of_tendsto_of_tendsto hqq tendsto_const_nhds
      (Filter.Eventually.of_forall hk)
  norm_num at hbad



noncomputable def zfk_armLower (k : ℕ) : ℝ :=
  1 - (1 - halfMeasure.real (zbd_boxHitsInfinite k)) ^ ((1 : ℝ) / 4)

theorem zfk_armLower_nonneg (k : ℕ) : 0 ≤ zfk_armLower k := by
  have hbase0 : 0 ≤ 1 - halfMeasure.real (zbd_boxHitsInfinite k) := by
    linarith [measureReal_le_one (μ := halfMeasure)
      (s := zbd_boxHitsInfinite k)]
  have hbase1 : 1 - halfMeasure.real (zbd_boxHitsInfinite k) ≤ 1 := by
    linarith [measureReal_nonneg (μ := halfMeasure)
      (s := zbd_boxHitsInfinite k)]
  have hr := Real.rpow_le_one hbase0 hbase1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
  unfold zfk_armLower
  linarith

theorem zfk_armLower_tendsto_one
    (hpos : 0 < halfMeasure.real (Universality.percolationEvent 2)) :
    Tendsto zfk_armLower atTop (nhds 1) := by
  exact zhg_oneSubRpow_tendsto_one (zbd_boxHitsInfinite_tendsto_one hpos)



theorem zfk_armLower_le_left
    (hpa : PositivelyAssociated halfMeasure) (k N : ℕ) (hkN : k ≤ N) :
    zfk_armLower k ≤ halfMeasure.real (zfk_LeftArmEvent k N) := by
  let S := zrs_sideFamily (zfk_LeftArmEvent k N)
  have hinc : ∀ i : Fin 4, IsIncreasing (S i) := fun i =>
    zrs_sideFamily_isIncreasing (zfk_LeftArmEvent_isIncreasing k N) i
  have hmeas : ∀ i : Fin 4, MeasurableSet (S i) := fun i =>
    zrs_sideFamily_measurableSet (zfk_LeftArmEvent_measurableSet k N) i
  have hsym : ∀ i : Fin 4,
      halfMeasure.real (S i) = halfMeasure.real (S 0) := fun i =>
    zrs_side_symmetry (zfk_LeftArmEvent_measurableSet k N) i
  have hsqrt := zhg_sqrt_trick_four halfMeasure hpa
    (hinc 0) (hinc 1) (hinc 2) (hinc 3)
    (hmeas 0) (hmeas 1) (hmeas 2) (hmeas 3)
    (hsym 1).symm (hsym 2).symm (hsym 3).symm
  have hmono : halfMeasure.real (zbd_boxHitsInfinite k) ≤
      halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3) :=
    measureReal_mono (zfk_boxHitsInfinite_subset_armUnion k N hkN)
      (measure_ne_top _ _)
  have hU0 : 0 ≤ 1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3) := by
    linarith [measureReal_le_one (μ := halfMeasure)
      (s := S 0 ∪ S 1 ∪ S 2 ∪ S 3)]
  have hcomp : 1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3) ≤
      1 - halfMeasure.real (zbd_boxHitsInfinite k) := by linarith
  have hrpow := Real.rpow_le_rpow hU0 hcomp
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  change 1 - (1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3)) ^
      ((1 : ℝ) / 4) ≤ halfMeasure.real (S 0) at hsqrt
  change (1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3)) ^
      ((1 : ℝ) / 4) ≤
    (1 - halfMeasure.real (zbd_boxHitsInfinite k)) ^ ((1 : ℝ) / 4) at hrpow
  have hfinal : 1 - (1 - halfMeasure.real (zbd_boxHitsInfinite k)) ^
      ((1 : ℝ) / 4) ≤ halfMeasure.real (S 0) := by linarith
  simpa [zfk_armLower, S] using hfinal

theorem zfk_centeredRight_eq_rot2 (k N : ℕ) :
    zfk_CenteredRightArmEvent k N =
      zrs_rot (zrs_rot (zfk_LeftArmEvent k N)) := by
  rw [zfk_rot_leftArmEvent_eq_top, zfk_rot_topArmEvent_eq_right]

theorem zfk_CenteredRightArmEvent_measurableSet (k N : ℕ) :
    MeasurableSet (zfk_CenteredRightArmEvent k N) := by
  rw [zfk_centeredRight_eq_rot2]
  exact zrs_rotPreimage_measurableSet
    (zrs_rotPreimage_measurableSet (zfk_LeftArmEvent_measurableSet k N))

theorem zfk_centeredRight_prob_eq_left (k N : ℕ) :
    halfMeasure.real (zfk_CenteredRightArmEvent k N) =
      halfMeasure.real (zfk_LeftArmEvent k N) := by
  rw [zfk_centeredRight_eq_rot2]
  exact zrs_side_symmetry (zfk_LeftArmEvent_measurableSet k N) 1



theorem zfk_rightArmEvent_eq_translate_preimage (k N : ℕ) :
    zfk_RightArmEvent k N =
      translateConfig (![1, 0] : Site 2) ⁻¹' zfk_CenteredRightArmEvent k N := by
  ext omega
  change (∃ y ∈ zfk_rightCentralBox k,
      (cluster 2 omega y).Infinite ∧ zfk_RightArmFrom omega y N) ↔
    ∃ x ∈ box 2 k, (cluster 2 (translateConfig ![1, 0] omega) x).Infinite ∧
      ∃ (hx : x ∈ zfk_leftSquare N)
        (a : StatMech.RSW.Box.rightSide
          (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)),
        ConnectedWithin 2 (translateConfig ![1, 0] omega) (zfk_leftSquare N)
          ⟨(a : Site 2), StatMech.RSW.Box.rightSide_subset a.2⟩ ⟨x, hx⟩
  constructor
  · rintro ⟨y, hyK, hyInf, hyS, b, hyb⟩
    let x : Site 2 := y - ![1, 0]
    have hxK : x ∈ box 2 k := hyK
    have hxS : x ∈ zfk_leftSquare N := by
      simpa [zfk_leftSquare, zfk_rightSquare, mem_rect, x] using hyS
    let a : StatMech.RSW.Box.rightSide
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) :=
      ⟨(b : Site 2) - ![1, 0], by
        rcases b.2 with ⟨⟨hl, hr, hb, ht⟩, heq⟩
        refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
          simp only [Pi.sub_apply] <;> norm_num at * <;> omega⟩
    refine ⟨x, hxK, ?_, hxS, a, ?_⟩
    · apply (zfk_translate_clusterInfinite_iff (![1, 0] : Site 2) omega x).mpr
      have hxy : x + (![1, 0] : Site 2) = y := by
        change (y - (![1, 0] : Site 2)) + ![1, 0] = y
        exact sub_add_cancel y ![1, 0]
      rwa [hxy]
    · have hxy : x + (![1, 0] : Site 2) = y := by
        change (y - (![1, 0] : Site 2)) + ![1, 0] = y
        exact sub_add_cancel y ![1, 0]
      have hab : (a : Site 2) + (![1, 0] : Site 2) = (b : Site 2) := by
        dsimp [a]
        exact sub_add_cancel (b : Site 2) (![1, 0] : Site 2)
      have htranslated : ConnectedWithin 2 omega (zfk_rightSquare N)
          ⟨(a : Site 2) + ![1, 0], (zfk_shift_mem_rightSquare_iff N _).mp
            (StatMech.RSW.Box.rightSide_subset a.2)⟩
          ⟨x + ![1, 0], (zfk_shift_mem_rightSquare_iff N _).mp hxS⟩ := by
        convert hyb.symm using 1 <;> apply Subtype.ext
        · exact hab
        · exact hxy
      have hmap := (zfk_connectedWithin_shiftRight_iff omega N (a : Site 2) x
          (StatMech.RSW.Box.rightSide_subset a.2) hxS).mpr htranslated
      simpa [zfk_leftSquare, x, a] using hmap
  · rintro ⟨x, hxK, hxInf, hxS, a, hax⟩
    let y : Site 2 := x + ![1, 0]
    have hyK : y ∈ zfk_rightCentralBox k := by
      simpa [zfk_rightCentralBox, y] using hxK
    have hyS : y ∈ zfk_rightSquare N := by
      rw [zfk_rightSquare]
      simpa [y] using (cti_mem_rect_translate
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)
        (![1, 0] : Site 2) x).mp (by simpa [zfk_leftSquare] using hxS)
    let b : StatMech.RSW.Box.rightSide
        (-(N : ℤ) + 1) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ) :=
      ⟨(a : Site 2) + ![1, 0], by
        simpa using (cti_mem_rightSide_translate
          (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)
          (![1, 0] : Site 2) a).mp a.2⟩
    refine ⟨y, hyK, ?_, hyS, b, ?_⟩
    · exact (zfk_translate_clusterInfinite_iff (![1, 0] : Site 2) omega x).mp hxInf
    · have hmap := (zfk_connectedWithin_shiftRight_iff omega N (a : Site 2) x
          (StatMech.RSW.Box.rightSide_subset a.2) hxS).mp hax
      exact hmap.symm

theorem zfk_right_prob_eq_left (k N : ℕ) :
    halfMeasure.real (zfk_RightArmEvent k N) =
      halfMeasure.real (zfk_LeftArmEvent k N) := by
  rw [zfk_rightArmEvent_eq_translate_preimage]
  calc
    halfMeasure.real
        (translateConfig (![1, 0] : Site 2) ⁻¹' zfk_CenteredRightArmEvent k N) =
        halfMeasure.real (zfk_CenteredRightArmEvent k N) :=
      (cti_selfDual_shift_invariant (![1, 0] : Site 2)).measureReal_preimage
        (zfk_CenteredRightArmEvent_measurableSet k N).nullMeasurableSet
    _ = halfMeasure.real (zfk_LeftArmEvent k N) :=
      zfk_centeredRight_prob_eq_left k N

theorem zfk_armLower_le_right
    (hpa : PositivelyAssociated halfMeasure) (k N : ℕ) (hkN : k ≤ N) :
    zfk_armLower k ≤ halfMeasure.real (zfk_RightArmEvent k N) := by
  rw [zfk_right_prob_eq_left]
  exact zfk_armLower_le_left hpa k N hkN




def zfk_FaceVerticalEvent (N : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  StatMech.RSW.Box.verticalCrossingEvent
    (-(N : ℤ)) (N : ℤ) (-(N : ℤ) - 1) (N : ℤ)

def zfk_FaithfulDualVerticalEvent (N : ℕ) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  fci_faceDualConfig ⁻¹' zfk_FaceVerticalEvent N

theorem zfk_FaithfulDualVerticalEvent_measurableSet (N : ℕ) :
    MeasurableSet (zfk_FaithfulDualVerticalEvent N) := by
  exact (rlc_verticalCrossingEvent_measurableSet _ _ _ _).preimage
    fci_faceDualConfig_measurePreserving.measurable




theorem zfk_faithfulDualVertical_prob_eq_matched (N : ℕ) :
    halfMeasure.real (zfk_FaithfulDualVerticalEvent N) =
      halfMeasure.real
        (StatMech.RSW.Box.horizontalCrossingEvent
          (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) := by
  have hmeasSwap : MeasurableSet
      (StatMech.RSW.Box.horizontalCrossingEvent
        (-(N : ℤ) - 1) (N : ℤ) (-(N : ℤ)) (N : ℤ)) :=
    rlc_horizontalCrossingEvent_measurableSet _ _ _ _
  calc
    halfMeasure.real (zfk_FaithfulDualVerticalEvent N) =
        halfMeasure.real (zfk_FaceVerticalEvent N) := by
      exact fci_faceDualConfig_measurePreserving.measureReal_preimage
        (rlc_verticalCrossingEvent_measurableSet _ _ _ _).nullMeasurableSet
    _ = halfMeasure.real
        (StatMech.RSW.Box.horizontalCrossingEvent
          (-(N : ℤ) - 1) (N : ℤ) (-(N : ℤ)) (N : ℤ)) := by
      exact crf_verticalCrossing_eq_horizontal_swap
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ) - 1) (N : ℤ) hmeasSwap
    _ = halfMeasure.real
        (StatMech.RSW.Box.horizontalCrossingEvent
          (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) := by
      symm
      simpa using cti_horizontalCrossing_translation_invariant
        (-(N : ℤ) - 1) (N : ℤ) (-(N : ℤ)) (N : ℤ)
        (![1, 0] : Site 2) hmeasSwap




def zfk_FaithfulMatchedExclusive (N : ℕ) : Prop :=
  Disjoint
    (StatMech.RSW.Box.horizontalCrossingEvent
      (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ))
    (zfk_FaithfulDualVerticalEvent N)

theorem zfk_matched_half_of_faithful_exclusive (N : ℕ)
    (hexcl : zfk_FaithfulMatchedExclusive N) :
    halfMeasure.real
      (StatMech.RSW.Box.horizontalCrossingEvent
        (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2 := by
  have hu := measureReal_le_one (μ := halfMeasure)
    (s := StatMech.RSW.Box.horizontalCrossingEvent
      (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ) ∪
        zfk_FaithfulDualVerticalEvent N)
  rw [measureReal_union hexcl (zfk_FaithfulDualVerticalEvent_measurableSet N),
    zfk_faithfulDualVertical_prob_eq_matched] at hu
  linarith




theorem zfk_thetaReal_zero_of_matched_half
    (hpa : PositivelyAssociated halfMeasure)
    (hhalf : ∀ N : ℕ,
      halfMeasure.real
        (StatMech.RSW.Box.horizontalCrossingEvent
          (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2) :
    halfMeasure.real (Universality.percolationEvent 2) = 0 := by
  by_contra hne
  have hpos : 0 < halfMeasure.real (Universality.percolationEvent 2) :=
    lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
  exact zfk_fixedK_contradiction hpa zfk_armLower
    (zfk_armLower_tendsto_one hpos) zfk_armLower_nonneg
    (fun k N hkN => zfk_armLower_le_left hpa k N (by omega))
    (fun k N hkN => zfk_armLower_le_right hpa k N (by omega)) hhalf


theorem zfk_percolationProbability_zero_of_matched_half
    (hpa : PositivelyAssociated halfMeasure)
    (hhalf : ∀ N : ℕ,
      halfMeasure.real
        (StatMech.RSW.Box.horizontalCrossingEvent
          (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2) :
    Universality.percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 := by
  unfold Universality.percolationProbability
  have hr := zfk_thetaReal_zero_of_matched_half hpa hhalf
  have hle : halfMeasure (Universality.percolationEvent 2) ≤ 1 :=
    le_trans (measure_mono (subset_univ _)) (by simp [measure_univ])
  have hfin : halfMeasure (Universality.percolationEvent 2) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hle
  exact (ENNReal.toReal_eq_zero_iff _).mp hr |>.resolve_right hfin

theorem zfk_percolationProbability_zero_of_faithful_exclusive
    (hpa : PositivelyAssociated halfMeasure)
    (hexcl : ∀ N : ℕ, zfk_FaithfulMatchedExclusive N) :
    Universality.percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 :=
  zfk_percolationProbability_zero_of_matched_half hpa
    (fun N => zfk_matched_half_of_faithful_exclusive N (hexcl N))




theorem zfk_criticalProbability_eq_half_of_faithful_exclusive
    (hpa : PositivelyAssociated halfMeasure)
    (hexcl : ∀ N : ℕ, zfk_FaithfulMatchedExclusive N)
    (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (StatMech.RSW.Box.horizontalCrossingEvent 0 a 0 b))
    (hmeasFace : ∀ n : ℤ, 0 < n →
      MeasurableSet (crr_FaceRectVerticalEvent n))
    (hmeasThin : ∀ n : ℤ, 0 < n →
      MeasurableSet
        (StatMech.RSW.Box.horizontalCrossingEvent (-1) n 0 (n - 1))) :
    criticalProbability 2 = (1 : ℝ) / 2 := by
  have hzero := zfk_percolationProbability_zero_of_faithful_exclusive hpa hexcl
  have hge : (1 : ℝ) / 2 ≤ criticalProbability 2 :=
    half_le_criticalProbability_of_subcritical hzero
  have hle : criticalProbability 2 ≤ (1 : ℝ) / 2 :=
    kbw_criticalProbability_le_half_square_faithful
      hmeasGenH hmeasFace hmeasThin
  linarith

end StatMech.TwoDim
