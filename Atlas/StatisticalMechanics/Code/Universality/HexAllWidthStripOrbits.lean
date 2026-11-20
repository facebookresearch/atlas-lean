/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















import Code.Universality.HexAllWidthStripGeometry
import Code.Universality.HexMirrorOrbitBoundary

namespace StatMech.Universality

open Complex HexWalk Set
open scoped BigOperators

noncomputable section




noncomputable def hexAWObservable (T L : ℕ) (hT : 0 < T) (z : ℂ) : ℂ :=
  parafObservable (hexAWFiniteRegion T L hT).inRegion
    (hexAWFiniteRegion T L hT).start 1 z (5 / 8) hexChi



def HexAWLocalRelation (T L : ℕ) (hT : 0 < T) : Prop :=
  ∀ v : HexAWVertex T L,
    ∑ j : Fin 3,
      (hexAWMid v.1 j - hexAWPos v.1) *
        hexAWObservable T L hT (hexAWMid v.1 j) = 0




noncomputable def hexAWDomain (T L : ℕ) (hT : 0 < T)
    (hlocal : HexAWLocalRelation T L hT) :
    HexDomain (HexAWVertex T L) where
  interiorVertices := Finset.univ
  pos v := hexAWPos v.1
  mid v j := hexAWMid v.1 j
  obs := hexAWObservable T L hT
  relation := by
    intro v _
    exact hlocal v

@[simp] theorem hexAWDomain_interiorVertices (T L : ℕ) (hT : 0 < T)
    (hlocal : HexAWLocalRelation T L hT) :
    (hexAWDomain T L hT hlocal).interiorVertices = Finset.univ := rfl

@[simp] theorem hexAWDomain_pos (T L : ℕ) (hT : 0 < T)
    (hlocal : HexAWLocalRelation T L hT) (v : HexAWVertex T L) :
    (hexAWDomain T L hT hlocal).pos v = hexAWPos v.1 := rfl

@[simp] theorem hexAWDomain_mid (T L : ℕ) (hT : 0 < T)
    (hlocal : HexAWLocalRelation T L hT) (v : HexAWVertex T L)
    (j : Fin 3) :
    (hexAWDomain T L hT hlocal).mid v j = hexAWMid v.1 j := rfl

@[simp] theorem hexAWDomain_obs (T L : ℕ) (hT : 0 < T)
    (hlocal : HexAWLocalRelation T L hT) (z : ℂ) :
    (hexAWDomain T L hT hlocal).obs z = hexAWObservable T L hT z := rfl



def hexAWDomainInteriorPairing (T L : ℕ) (hT : 0 < T)
    (hlocal : HexAWLocalRelation T L hT) :
    (hexAWDomain T L hT hlocal).InteriorPairing :=
  hexAWInteriorPairingOfDomain (hexAWDomain T L hT hlocal)
    (fun _ => rfl) (fun _ _ => rfl)

@[simp] theorem hexAWDomainInteriorPairing_interior
    (T L : ℕ) (hT : 0 < T)
    (hlocal : HexAWLocalRelation T L hT) :
    (hexAWDomainInteriorPairing T L hT hlocal).interior =
      hexAWInteriorIncidences T L := rfl

theorem hexAWDomainInteriorPairing_interior_sub
    (T L : ℕ) (hT : 0 < T)
    (hlocal : HexAWLocalRelation T L hT) :
    (hexAWDomainInteriorPairing T L hT hlocal).interior ⊆
      (hexAWDomain T L hT hlocal).incidences := by
  apply hexAWInteriorPairingOfDomain_interior_sub
  intro v
  simp



noncomputable instance hexAWVertex_fintype (T L : ℕ) :
    Fintype (HexAWVertex T L) := Fintype.ofFinite _


def hexAWIncidenceEquiv (T L : ℕ) :
    (HexAWVertex T L × Fin 3) ≃ HexAWIncidence T L where
  toFun p := ⟨p.1, p.2⟩
  invFun e := (e.vtx, e.edge)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance hexAWIncidence_fintype (T L : ℕ) :
    Fintype (HexAWIncidence T L) :=
  Fintype.ofEquiv (HexAWVertex T L × Fin 3) (hexAWIncidenceEquiv T L)


noncomputable def hexAWIncidenceRank {T L : ℕ}
    (e : HexAWIncidence T L) : ℕ :=
  (Fintype.equivFin (HexAWIncidence T L) e).val

theorem hexAWIncidenceRank_injective {T L : ℕ} :
    Function.Injective (@hexAWIncidenceRank T L) := by
  intro e f h
  exact (Fintype.equivFin (HexAWIncidence T L)).injective (Fin.ext h)


abbrev HexAWPairIndex (T L : ℕ) :=
  {e : HexAWIncidence T L //
    e ∈ hexAWBoundaryIncidences T L ∧
      hexAWIncidenceRank e <
        hexAWIncidenceRank (hexAWReflectIncidence e)}




abbrev HexAWFixedIndex (T L : ℕ) (hT : 0 < T) :=
  {e : HexAWIncidence T L //
    e ∈ hexAWBoundaryIncidences T L ∧
      hexAWReflectIncidence e = e ∧
      e ≠ hexAWStartIncidence T L hT}

noncomputable instance hexAWPairIndex_fintype (T L : ℕ) :
    Fintype (HexAWPairIndex T L) := Fintype.ofFinite _

noncomputable instance hexAWFixedIndex_fintype (T L : ℕ) (hT : 0 < T) :
    Fintype (HexAWFixedIndex T L hT) := Fintype.ofFinite _

instance hexAWPairIndex_decidableEq (T L : ℕ) :
    DecidableEq (HexAWPairIndex T L) := inferInstance

instance hexAWFixedIndex_decidableEq (T L : ℕ) (hT : 0 < T) :
    DecidableEq (HexAWFixedIndex T L hT) := inferInstance


def hexAWPairPiece {T L : ℕ} (i : HexAWPairIndex T L) :
    Finset (HexAWIncidence T L) :=
  {i.1, hexAWReflectIncidence i.1}


def hexAWFixedPiece {T L : ℕ} {hT : 0 < T}
    (k : HexAWFixedIndex T L hT) : Finset (HexAWIncidence T L) :=
  {k.1}


def hexAWOrbitPiece {T L : ℕ} {hT : 0 < T}
    (o : HexAWPairIndex T L ⊕ HexAWFixedIndex T L hT) :
    Finset (HexAWIncidence T L) :=
  match o with
  | .inl i => hexAWPairPiece i
  | .inr k => hexAWFixedPiece k

theorem hexAWOrbitPiece_eq_raw {T L : ℕ} {hT : 0 < T} :
    (hexAWOrbitPiece (T := T) (L := L) (hT := hT)) =
      fun o : HexAWPairIndex T L ⊕ HexAWFixedIndex T L hT =>
        match o with
        | .inl i => ({i.1, hexAWReflectIncidence i.1} :
            Finset (HexAWIncidence T L))
        | .inr k => {k.1} := by
  funext o
  cases o <;> rfl

theorem hexAWPairIndex_ne_reflect {T L : ℕ} (i : HexAWPairIndex T L) :
    i.1 ≠ hexAWReflectIncidence i.1 := by
  intro h
  exact (Nat.ne_of_lt i.2.2) (congrArg hexAWIncidenceRank h)

theorem hexAWPairIndex_reflect_mem_boundary {T L : ℕ}
    (i : HexAWPairIndex T L) :
    hexAWReflectIncidence i.1 ∈ hexAWBoundaryIncidences T L :=
  (hexAWReflectIncidence_mem_boundary_iff i.1).2 i.2.1

theorem hexAWPairPiece_mem_boundary {T L : ℕ} (i : HexAWPairIndex T L)
    {e : HexAWIncidence T L} (he : e ∈ hexAWPairPiece i) :
    e ∈ hexAWBoundaryIncidences T L := by
  simp only [hexAWPairPiece, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact i.2.1
  · exact hexAWPairIndex_reflect_mem_boundary i

theorem hexAWPairPiece_not_start {T L : ℕ} (hT : 0 < T)
    (i : HexAWPairIndex T L) {e : HexAWIncidence T L}
    (he : e ∈ hexAWPairPiece i) :
    e ≠ hexAWStartIncidence T L hT := by
  intro hs
  simp only [hexAWPairPiece, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with he | he
  · have hi : i.1 = hexAWStartIncidence T L hT := he.symm.trans hs
    apply hexAWPairIndex_ne_reflect i
    calc
      i.1 = hexAWStartIncidence T L hT := hi
      _ = hexAWReflectIncidence (hexAWStartIncidence T L hT) :=
        (hexAWStartIncidence_reflect T L hT).symm
      _ = hexAWReflectIncidence i.1 := congrArg hexAWReflectIncidence hi.symm
  · have hr : hexAWReflectIncidence i.1 =
        hexAWStartIncidence T L hT := he.symm.trans hs
    have hi : i.1 = hexAWStartIncidence T L hT := by
      calc
        i.1 = hexAWReflectIncidence (hexAWReflectIncidence i.1) :=
          (hexAWReflectIncidence_invol i.1).symm
        _ = hexAWReflectIncidence (hexAWStartIncidence T L hT) :=
          congrArg hexAWReflectIncidence hr
        _ = hexAWStartIncidence T L hT :=
          hexAWStartIncidence_reflect T L hT
    apply hexAWPairIndex_ne_reflect i
    exact hi.trans hr.symm

theorem hexAWFixedPiece_mem_boundary {T L : ℕ} {hT : 0 < T}
    (k : HexAWFixedIndex T L hT) {e : HexAWIncidence T L}
    (he : e ∈ hexAWFixedPiece k) :
    e ∈ hexAWBoundaryIncidences T L := by
  have heq : e = k.1 := by simpa [hexAWFixedPiece] using he
  subst e
  exact k.2.1

theorem hexAWFixedPiece_not_start {T L : ℕ} {hT : 0 < T}
    (k : HexAWFixedIndex T L hT) {e : HexAWIncidence T L}
    (he : e ∈ hexAWFixedPiece k) :
    e ≠ hexAWStartIncidence T L hT := by
  have heq : e = k.1 := by simpa [hexAWFixedPiece] using he
  subst e
  exact k.2.2.2




theorem hexAW_mem_orbit_biUnion_iff {T L : ℕ} (hT : 0 < T)
    (e : HexAWIncidence T L) :
    e ∈ (Finset.univ.biUnion
      (hexAWOrbitPiece (T := T) (L := L) (hT := hT))) ↔
      e ∈ hexAWBoundaryIncidences T L ∧
        e ≠ hexAWStartIncidence T L hT := by
  constructor
  · intro he
    rw [Finset.mem_biUnion] at he
    obtain ⟨o, _, heo⟩ := he
    cases o with
    | inl i =>
        exact ⟨hexAWPairPiece_mem_boundary i heo,
          hexAWPairPiece_not_start hT i heo⟩
    | inr k =>
        exact ⟨hexAWFixedPiece_mem_boundary k heo,
          hexAWFixedPiece_not_start k heo⟩
  · rintro ⟨heBoundary, heStart⟩
    by_cases hfixed : hexAWReflectIncidence e = e
    · rw [Finset.mem_biUnion]
      let k : HexAWFixedIndex T L hT :=
        ⟨e, heBoundary, hfixed, heStart⟩
      refine ⟨Sum.inr k, Finset.mem_univ _, ?_⟩
      simp [hexAWOrbitPiece, hexAWFixedPiece, k]
    · have hrank :
          hexAWIncidenceRank e <
              hexAWIncidenceRank (hexAWReflectIncidence e) ∨
            hexAWIncidenceRank (hexAWReflectIncidence e) <
              hexAWIncidenceRank e := by
        rcases lt_trichotomy (hexAWIncidenceRank e)
            (hexAWIncidenceRank (hexAWReflectIncidence e)) with h | h | h
        · exact Or.inl h
        · exfalso
          exact hfixed (hexAWIncidenceRank_injective h.symm)
        · exact Or.inr h
      rw [Finset.mem_biUnion]
      cases hrank with
      | inl hlt =>
          let i : HexAWPairIndex T L := ⟨e, heBoundary, hlt⟩
          refine ⟨Sum.inl i, Finset.mem_univ _, ?_⟩
          simp [hexAWOrbitPiece, hexAWPairPiece, i]
      | inr hlt =>
          let er := hexAWReflectIncidence e
          have herBoundary : er ∈ hexAWBoundaryIncidences T L :=
            (hexAWReflectIncidence_mem_boundary_iff e).2 heBoundary
          have herlt :
              hexAWIncidenceRank er <
                hexAWIncidenceRank (hexAWReflectIncidence er) := by
            simpa [er] using hlt
          let i : HexAWPairIndex T L := ⟨er, herBoundary, herlt⟩
          refine ⟨Sum.inl i, Finset.mem_univ _, ?_⟩
          simp [hexAWOrbitPiece, hexAWPairPiece, i, er]



theorem hexAW_boundary_orbit_partition (T L : ℕ) (hT : 0 < T) :
    hexAWBoundaryIncidences T L =
      {hexAWStartIncidence T L hT} ∪
        Finset.univ.biUnion
          (hexAWOrbitPiece (T := T) (L := L) (hT := hT)) := by
  ext e
  rw [Finset.mem_union, Finset.mem_singleton,
    hexAW_mem_orbit_biUnion_iff]
  constructor
  · intro he
    by_cases hs : e = hexAWStartIncidence T L hT
    · exact Or.inl hs
    · exact Or.inr ⟨he, hs⟩
  · rintro (rfl | ⟨he, _⟩)
    · exact hexAWStartIncidence_mem_boundary T L hT
    · exact he

theorem hexAW_start_orbits_disjoint (T L : ℕ) (hT : 0 < T) :
    Disjoint ({hexAWStartIncidence T L hT} :
      Finset (HexAWIncidence T L))
      (Finset.univ.biUnion
        (hexAWOrbitPiece (T := T) (L := L) (hT := hT))) := by
  rw [Finset.disjoint_left]
  intro e heStart heOrbit
  have hs : e = hexAWStartIncidence T L hT := by simpa using heStart
  exact (hexAW_mem_orbit_biUnion_iff hT e).1 heOrbit |>.2 hs

private theorem hexAW_pairPieces_disjoint {T L : ℕ}
    (i j : HexAWPairIndex T L) (hij : i ≠ j) :
    Disjoint (hexAWPairPiece i) (hexAWPairPiece j) := by
  rw [Finset.disjoint_left]
  intro e hei hej
  simp only [hexAWPairPiece, Finset.mem_insert, Finset.mem_singleton] at hei hej
  rcases hei with hi | hi <;> rcases hej with hj | hj
  · apply hij
    apply Subtype.ext
    exact hi.symm.trans hj
  · have hcross : i.1 = hexAWReflectIncidence j.1 := hi.symm.trans hj
    have hcross' : hexAWReflectIncidence i.1 = j.1 := by
      have := congrArg hexAWReflectIncidence hcross
      simpa using this
    have hlt := i.2.2
    rw [hcross'] at hlt
    have hgt := j.2.2
    rw [← hcross] at hgt
    omega
  · have hcross : hexAWReflectIncidence i.1 = j.1 := hi.symm.trans hj
    have hcross' : i.1 = hexAWReflectIncidence j.1 := by
      have := congrArg hexAWReflectIncidence hcross
      simpa using this
    have hlt := j.2.2
    rw [← hcross'] at hlt
    have hgt := i.2.2
    rw [hcross] at hgt
    omega
  · apply hij
    apply Subtype.ext
    have hreflect :
        hexAWReflectIncidence i.1 = hexAWReflectIncidence j.1 :=
      hi.symm.trans hj
    have := congrArg hexAWReflectIncidence hreflect
    simpa using this

private theorem hexAW_pair_fixed_disjoint {T L : ℕ} {hT : 0 < T}
    (i : HexAWPairIndex T L) (k : HexAWFixedIndex T L hT) :
    Disjoint (hexAWPairPiece i) (hexAWFixedPiece k) := by
  rw [Finset.disjoint_left]
  intro e hei hek
  have heq : e = k.1 := by simpa [hexAWFixedPiece] using hek
  subst e
  simp only [hexAWPairPiece, Finset.mem_insert, Finset.mem_singleton] at hei
  rcases hei with hi | hi
  · have hfix : hexAWReflectIncidence i.1 = i.1 := by
      calc
        hexAWReflectIncidence i.1 = hexAWReflectIncidence k.1 :=
          congrArg hexAWReflectIncidence hi.symm
        _ = k.1 := k.2.2.1
        _ = i.1 := hi
    exact hexAWPairIndex_ne_reflect i hfix.symm
  · have hfix : hexAWReflectIncidence i.1 = i.1 := by
      calc
        hexAWReflectIncidence i.1 = k.1 := hi.symm
        _ = hexAWReflectIncidence k.1 := k.2.2.1.symm
        _ = hexAWReflectIncidence (hexAWReflectIncidence i.1) := by rw [hi]
        _ = i.1 := hexAWReflectIncidence_invol i.1
    exact hexAWPairIndex_ne_reflect i hfix.symm

private theorem hexAW_fixedPieces_disjoint {T L : ℕ} {hT : 0 < T}
    (k l : HexAWFixedIndex T L hT) (hkl : k ≠ l) :
    Disjoint (hexAWFixedPiece k) (hexAWFixedPiece l) := by
  rw [Finset.disjoint_left]
  intro e hek hel
  apply hkl
  apply Subtype.ext
  have hk : e = k.1 := by simpa [hexAWFixedPiece] using hek
  have hl : e = l.1 := by simpa [hexAWFixedPiece] using hel
  exact hk.symm.trans hl


theorem hexAW_orbitPieces_pairwiseDisjoint (T L : ℕ) (hT : 0 < T) :
    ((Finset.univ : Finset
      (HexAWPairIndex T L ⊕ HexAWFixedIndex T L hT)) :
        Set (HexAWPairIndex T L ⊕ HexAWFixedIndex T L hT)).PairwiseDisjoint
      (hexAWOrbitPiece (T := T) (L := L) (hT := hT)) := by
  intro o _ p _ hop
  cases o with
  | inl i =>
      cases p with
      | inl j =>
          exact hexAW_pairPieces_disjoint i j (fun hij => hop (congrArg Sum.inl hij))
      | inr k =>
          exact hexAW_pair_fixed_disjoint i k
  | inr k =>
      cases p with
      | inl i =>
          exact (hexAW_pair_fixed_disjoint i k).symm
      | inr l =>
          exact hexAW_fixedPieces_disjoint k l
            (fun hkl => hop (congrArg Sum.inr hkl))





structure HexFiniteStripGeometricOrbitData
    {I K V : Type*} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K] [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    (P : D.InteriorPairing) where
  heading : V → Fin 3 → ℤ
  hgeom : ∀ v j,
    D.mid v j - D.pos v = (1 / 2 : ℂ) * hexUnit (heading v j)
  startIncidence : HexIncidence V
  start_mid : D.mid startIncidence.vtx startIncidence.edge = R.start
  start_heading : heading startIncidence.vtx startIncidence.edge = 4
  neg : I → HexIncidence V
  pos : I → HexIncidence V
  pair_ne : ∀ i, neg i ≠ pos i
  midpoint_reflect : ∀ i,
    D.mid (pos i).vtx (pos i).edge =
      hsc_refl R.start h0 (D.mid (neg i).vtx (neg i).edge)
  fixed : K → HexIncidence V
  fixed_reflect : ∀ k,
    D.mid (fixed k).vtx (fixed k).edge =
      hsc_refl R.start h0 (D.mid (fixed k).vtx (fixed k).edge)
  orbitPiece : I ⊕ K → Finset (HexIncidence V)
  pair_piece : ∀ i, orbitPiece (.inl i) = {neg i, pos i}
  fixed_piece : ∀ k, orbitPiece (.inr k) = {fixed k}
  boundary_partition :
    D.incidences \ P.interior =
      {startIncidence} ∪ Finset.univ.biUnion orbitPiece
  start_orbits_disjoint :
    Disjoint ({startIncidence} : Finset (HexIncidence V))
      (Finset.univ.biUnion orbitPiece)
  orbits_disjoint :
    ((Finset.univ : Finset (I ⊕ K)) : Set (I ⊕ K)).PairwiseDisjoint
      orbitPiece



noncomputable def hexAWGeometricOrbitData (T L : ℕ) (hT : 0 < T)
    (hlocal : HexAWLocalRelation T L hT) :
    HexFiniteStripGeometricOrbitData
      (I := HexAWPairIndex T L) (K := HexAWFixedIndex T L hT)
      (R := hexAWFiniteRegion T L hT) (h0 := 1)
      (hexAWDomainInteriorPairing T L hT hlocal) where
  heading v j := hexAWHeading v.1 j
  hgeom := by
    intro v j
    exact hexAWMid_sub_pos v.1 j
  startIncidence := hexAWStartIncidence T L hT
  start_mid := hexAWStartIncidence_mid T L hT
  start_heading := hexAWStartIncidence_heading T L hT
  neg i := i.1
  pos i := hexAWReflectIncidence i.1
  pair_ne := hexAWPairIndex_ne_reflect
  midpoint_reflect := by
    intro i
    change hexAWMid (hexAWReflectIncidence i.1).vtx.1
        (hexAWReflectIncidence i.1).edge =
      hsc_refl hexAWStart 1 (hexAWMid i.1.vtx.1 i.1.edge)
    rw [hexAW_refl_one_eq_four]
    exact hexAWReflectIncidence_mid i.1
  fixed k := k.1
  fixed_reflect := by
    intro k
    change hexAWMid k.1.vtx.1 k.1.edge =
      hsc_refl hexAWStart 1 (hexAWMid k.1.vtx.1 k.1.edge)
    rw [hexAW_refl_one_eq_four, ← hexAWReflectIncidence_mid,
      k.2.2.1]
  orbitPiece := hexAWOrbitPiece
  pair_piece := by intro i; rfl
  fixed_piece := by intro k; rfl
  boundary_partition := by
    rw [hexAWDomainInteriorPairing_interior]
    have hinc :
        (hexAWDomain T L hT hlocal).incidences =
          hexAWIncidences T L := by
      ext e
      simp [HexDomain.incidences]
    rw [hinc]
    simpa only [hexAWBoundaryIncidences] using
      hexAW_boundary_orbit_partition T L hT
  start_orbits_disjoint := hexAW_start_orbits_disjoint T L hT
  orbits_disjoint := hexAW_orbitPieces_pairwiseDisjoint T L hT





theorem hexAWFixedIndex_eq_right {T L : ℕ} {hT : 0 < T}
    (k : HexAWFixedIndex T L hT) :
    ∃ n : ℕ, 0 < n ∧ T = 2 * n ∧
      k.1.vtx.1 = hexAWRightFixedCoord n ∧ k.1.edge = 0 := by
  obtain hstart | ⟨n, hTn, hcoord, hedge⟩ :=
    hexAW_fixed_boundary_classification k.1 k.2.1 k.2.2.1
  · exfalso
    apply k.2.2.2
    rw [HexIncidence.mk.injEq]
    exact ⟨Subtype.ext hstart.1, hstart.2⟩
  · have hn : 0 < n := by omega
    exact ⟨n, hn, hTn, hcoord, hedge⟩


theorem hexAWFixedIndex_isEmpty_of_odd {T L : ℕ} {hT : 0 < T}
    (hodd : Odd T) : IsEmpty (HexAWFixedIndex T L hT) := by
  constructor
  intro k
  obtain ⟨n, _, hTn, _⟩ := hexAWFixedIndex_eq_right k
  obtain ⟨m, hm⟩ := hodd
  omega



def hexAWRightFixedIndex (n L : ℕ) (hn : 0 < n) :
    HexAWFixedIndex (2 * n) L (by omega) :=
  ⟨hexAWRightFixedIncidence n L hn,
    hexAWRightFixedIncidence_mem_boundary n L hn,
    hexAWRightFixedIncidence_reflect n L hn,
    by
      intro h
      have hv := congrArg (fun e => e.vtx.1.color) h
      simp [hexAWRightFixedIncidence, hexAWRightFixedCoord,
        hexAWStartIncidence, hexAWOrigin, hexAWOriginCoord] at hv⟩



theorem hexAWFixedIndex_subsingleton_even (n L : ℕ) (hn : 0 < n) :
    ∀ k : HexAWFixedIndex (2 * n) L (by omega),
      k = hexAWRightFixedIndex n L hn := by
  intro k
  obtain ⟨m, hm, hwidth, hcoord, hedge⟩ := hexAWFixedIndex_eq_right k
  have hmn : m = n := by omega
  subst m
  apply Subtype.ext
  rw [HexIncidence.mk.injEq]
  exact ⟨Subtype.ext hcoord, hedge⟩

end

end StatMech.Universality
