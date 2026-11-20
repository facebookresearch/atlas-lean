/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.Universality.HexCorrectedStripGeometry

namespace StatMech.Universality

open Complex HexWalk Set
open scoped BigOperators

noncomputable section



noncomputable instance hexCSVertex_fintype (T L : ℕ) :
    Fintype (HexCSVertex T L) := Fintype.ofFinite _

def hexCSMids (T L : ℕ) : Finset ℂ :=
  (Finset.univ : Finset (HexCSVertex T L)).biUnion
    (fun v => (Finset.univ : Finset (Fin 3)).image
      (fun e => hexAWMid v.1 e))

@[simp] theorem hexAWStart_mem_hexCSMids (T L : ℕ) (hT : 0 < T) :
    hexAWStart ∈ hexCSMids T L := by
  rw [hexCSMids, Finset.mem_biUnion]
  refine ⟨hexCSOrigin T L hT, Finset.mem_univ _, ?_⟩
  rw [Finset.mem_image]
  exact ⟨0, Finset.mem_univ _, hexAWMid_origin_zero⟩

def hexCSFiniteRegion (T L : ℕ) (hT : 0 < T) : HexFiniteRegion :=
  hexStrip_finiteRegion (hexCSMids T L) hexAWStart
    (hexAWStart_mem_hexCSMids T L hT)

@[simp] theorem hexCSFiniteRegion_start (T L : ℕ) (hT : 0 < T) :
    (hexCSFiniteRegion T L hT).start = hexAWStart := rfl

@[simp] theorem hexCSFiniteRegion_mids (T L : ℕ) (hT : 0 < T) :
    (hexCSFiniteRegion T L hT).mids = hexCSMids T L := rfl

theorem hexCSMids_reflect {T L : ℕ} {z : ℂ}
    (hz : z ∈ hexCSMids T L) :
    hsc_refl hexAWStart 1 z ∈ hexCSMids T L := by
  rw [hexCSMids, Finset.mem_biUnion] at hz ⊢
  obtain ⟨v, _, hv⟩ := hz
  rw [Finset.mem_image] at hv
  obtain ⟨e, _, rfl⟩ := hv
  refine ⟨hexCSReflectVertex v, Finset.mem_univ _, ?_⟩
  rw [Finset.mem_image]
  refine ⟨hexAWReflectEdge e, Finset.mem_univ _, ?_⟩
  rw [hexAW_refl_one_eq_four]
  exact (hexAWMid_reflect v.1 e).symm

theorem hexCSFiniteRegion_reflect {T L : ℕ} (hT : 0 < T) (z : ℂ)
    (hz : (hexCSFiniteRegion T L hT).inRegion z) :
    (hexCSFiniteRegion T L hT).inRegion (hsc_refl hexAWStart 1 z) := by
  change z ∈ hexCSMids T L at hz
  change hsc_refl hexAWStart 1 z ∈ hexCSMids T L
  exact hexCSMids_reflect hz







def HexCSCanonicalWindingLaw (T L : ℕ) (hT : 0 < T) : Prop :=
  ∀ (e : HexCSIncidence T L) (ts : List ℤ),
    e ∈ hexCSBoundaryIncidences T L →
    e ≠ hexCSStartIncidence T L hT →
    (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
        (ofTurns hexAWStart 1 ts).StaysIn
          (hexCSFiniteRegion T L hT).inRegion ∧
        (ofTurns hexAWStart 1 ts).EndsAt
          (hexAWMid e.vtx.1 e.edge) →
      hexInfra_headAccum 1 ts = hexCSCanonicalHeading e

theorem hexCS_deterministic_winding_of_law {T L : ℕ} {hT : 0 < T}
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (e : HexCSIncidence T L) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (ts : List ℤ)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    (ofTurns hexAWStart 1 ts).turning = hexCSCanonicalWinding e := by
  unfold hexCSCanonicalWinding
  simpa only [Int.cast_one] using
    (hexInfra_turning_const_of_finalHeading hexAWStart 1 ts
      (hexCSCanonicalHeading e) (hlaw e ts he hne hadm))



abbrev HexCSInteriorIncidence (T L : ℕ) :=
  {e : HexCSIncidence T L // hexCSIsInterior e}

def hexCSInteriorMate {T L : ℕ}
    (e : HexCSInteriorIncidence T L) : HexCSInteriorIncidence T L := by
  let v' : HexCSVertex T L :=
    ⟨hexAWNeighbor e.1.vtx.1 e.1.edge, e.2⟩
  let e' : HexCSIncidence T L := ⟨v', e.1.edge⟩
  refine ⟨e', ?_⟩
  change hexAWNeighbor v'.1 e.1.edge ∈ hexCSVertexSet T L
  simp [v']

@[simp] theorem hexCSInteriorMate_edge {T L : ℕ}
    (e : HexCSInteriorIncidence T L) :
    (hexCSInteriorMate e).1.edge = e.1.edge := rfl

@[simp] theorem hexCSInteriorMate_vtx {T L : ℕ}
    (e : HexCSInteriorIncidence T L) :
    (hexCSInteriorMate e).1.vtx.1 =
      hexAWNeighbor e.1.vtx.1 e.1.edge := rfl

@[simp] theorem hexCSInteriorMate_invol {T L : ℕ}
    (e : HexCSInteriorIncidence T L) :
    hexCSInteriorMate (hexCSInteriorMate e) = e := by
  apply Subtype.ext
  cases e with
  | mk e he =>
      cases e with
      | mk v edge =>
          rw [HexIncidence.mk.injEq]
          exact ⟨Subtype.ext (hexAWNeighbor_invol v.1 edge), rfl⟩

theorem hexCSInteriorMate_ne {T L : ℕ}
    (e : HexCSInteriorIncidence T L) :
    hexCSInteriorMate e ≠ e := by
  intro h
  have hv : (hexCSInteriorMate e).1.vtx.1 = e.1.vtx.1 :=
    congrArg (fun q => q.1.vtx.1) h
  rw [hexCSInteriorMate_vtx] at hv
  exact hexAWNeighbor_ne e.1.vtx.1 e.1.edge hv

@[simp] theorem hexCSInteriorMate_mid {T L : ℕ}
    (e : HexCSInteriorIncidence T L) :
    hexAWMid (hexCSInteriorMate e).1.vtx.1
        (hexCSInteriorMate e).1.edge =
      hexAWMid e.1.vtx.1 e.1.edge := by
  rw [hexCSInteriorMate_edge, hexCSInteriorMate_vtx, hexAWMid_neighbor]

theorem hexCSInteriorMate_opposite {T L : ℕ}
    (e : HexCSInteriorIncidence T L) :
    hexAWMid (hexCSInteriorMate e).1.vtx.1
          (hexCSInteriorMate e).1.edge -
        hexAWPos (hexCSInteriorMate e).1.vtx.1 =
      -(hexAWMid e.1.vtx.1 e.1.edge - hexAWPos e.1.vtx.1) := by
  rw [hexCSInteriorMate_edge, hexCSInteriorMate_vtx,
    hexAWMid_sub_pos_neighbor]

def hexCSPairIncidence {T L : ℕ} (e : HexCSIncidence T L) :
    HexCSIncidence T L :=
  if h : hexCSIsInterior e then (hexCSInteriorMate ⟨e, h⟩).1 else e

theorem hexCSPairIncidence_eq_mate {T L : ℕ} (e : HexCSIncidence T L)
    (he : hexCSIsInterior e) :
    hexCSPairIncidence e = (hexCSInteriorMate ⟨e, he⟩).1 := by
  simp [hexCSPairIncidence, he]



noncomputable def hexCSObservable (T L : ℕ) (hT : 0 < T) (z : ℂ) : ℂ :=
  endpointParafObservable (hexCSFiniteRegion T L hT).inRegion
    (hexCSFiniteRegion T L hT).start 1 z (5 / 8) hexChi

def HexCSLocalRelation (T L : ℕ) (hT : 0 < T) : Prop :=
  ∀ v : HexCSVertex T L,
    ∑ j : Fin 3,
      (hexAWMid v.1 j - hexAWPos v.1) *
        hexCSObservable T L hT (hexAWMid v.1 j) = 0

noncomputable def hexCSDomain (T L : ℕ) (hT : 0 < T)
    (hlocal : HexCSLocalRelation T L hT) :
    HexDomain (HexCSVertex T L) where
  interiorVertices := Finset.univ
  pos v := hexAWPos v.1
  mid v j := hexAWMid v.1 j
  obs := hexCSObservable T L hT
  relation := by
    intro v _
    exact hlocal v

def hexCSDomainInteriorPairing (T L : ℕ) (hT : 0 < T)
    (hlocal : HexCSLocalRelation T L hT) :
    (hexCSDomain T L hT hlocal).InteriorPairing where
  interior := hexCSInteriorIncidences T L
  pair := hexCSPairIncidence
  pair_mem := by
    intro e he
    rw [hexCS_mem_interior_iff] at he ⊢
    rw [hexCSPairIncidence_eq_mate e he]
    exact (hexCSInteriorMate ⟨e, he⟩).2
  pair_invol := by
    intro e he
    rw [hexCS_mem_interior_iff] at he
    have hm := (hexCSInteriorMate ⟨e, he⟩).2
    rw [hexCSPairIncidence_eq_mate e he,
      hexCSPairIncidence_eq_mate _ hm]
    exact congrArg Subtype.val (hexCSInteriorMate_invol ⟨e, he⟩)
  pair_ne := by
    intro e he
    rw [hexCS_mem_interior_iff] at he
    rw [hexCSPairIncidence_eq_mate e he]
    exact fun h => hexCSInteriorMate_ne ⟨e, he⟩ (Subtype.ext h)
  cancel := by
    intro e he
    rw [hexCS_mem_interior_iff] at he
    rw [hexCSPairIncidence_eq_mate e he]
    unfold HexDomain.incTerm
    change (hexAWMid e.vtx.1 e.edge - hexAWPos e.vtx.1) *
          hexCSObservable T L hT (hexAWMid e.vtx.1 e.edge) =
      -((hexAWMid (hexCSInteriorMate ⟨e, he⟩).1.vtx.1
            (hexCSInteriorMate ⟨e, he⟩).1.edge -
          hexAWPos (hexCSInteriorMate ⟨e, he⟩).1.vtx.1) *
            hexCSObservable T L hT
              (hexAWMid (hexCSInteriorMate ⟨e, he⟩).1.vtx.1
                (hexCSInteriorMate ⟨e, he⟩).1.edge))
    rw [hexCSInteriorMate_opposite, hexCSInteriorMate_mid]
    ring

theorem hexCSDomainInteriorPairing_interior_sub
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT) :
    (hexCSDomainInteriorPairing T L hT hlocal).interior ⊆
      (hexCSDomain T L hT hlocal).incidences := by
  intro e he
  unfold HexDomain.incidences
  rw [Finset.mem_image]
  exact ⟨(e.vtx, e.edge), by simp [hexCSDomain], rfl⟩

theorem hexCSDomain_incidences_eq
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT) :
    (hexCSDomain T L hT hlocal).incidences = hexCSIncidences T L := by
  ext e
  simp [HexDomain.incidences, hexCSIncidences, hexCSDomain]



def hexCSIncidenceEquiv (T L : ℕ) :
    (HexCSVertex T L × Fin 3) ≃ HexCSIncidence T L where
  toFun p := ⟨p.1, p.2⟩
  invFun e := (e.vtx, e.edge)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance hexCSIncidence_fintype (T L : ℕ) :
    Fintype (HexCSIncidence T L) :=
  Fintype.ofEquiv (HexCSVertex T L × Fin 3) (hexCSIncidenceEquiv T L)

noncomputable def hexCSIncidenceRank {T L : ℕ}
    (e : HexCSIncidence T L) : ℕ :=
  (Fintype.equivFin (HexCSIncidence T L) e).val

theorem hexCSIncidenceRank_injective {T L : ℕ} :
    Function.Injective (@hexCSIncidenceRank T L) := by
  intro e f h
  exact (Fintype.equivFin (HexCSIncidence T L)).injective (Fin.ext h)

abbrev HexCSPairIndex (T L : ℕ) :=
  {e : HexCSIncidence T L //
    e ∈ hexCSBoundaryIncidences T L ∧
      hexCSIncidenceRank e < hexCSIncidenceRank (hexCSReflectIncidence e)}

abbrev HexCSFixedIndex (T L : ℕ) (hT : 0 < T) :=
  {e : HexCSIncidence T L //
    e ∈ hexCSBoundaryIncidences T L ∧
      hexCSReflectIncidence e = e ∧
      e ≠ hexCSStartIncidence T L hT}

noncomputable instance hexCSPairIndex_fintype (T L : ℕ) :
    Fintype (HexCSPairIndex T L) := Fintype.ofFinite _

noncomputable instance hexCSFixedIndex_fintype (T L : ℕ) (hT : 0 < T) :
    Fintype (HexCSFixedIndex T L hT) := Fintype.ofFinite _

instance hexCSPairIndex_decidableEq (T L : ℕ) :
    DecidableEq (HexCSPairIndex T L) := inferInstance

instance hexCSFixedIndex_decidableEq (T L : ℕ) (hT : 0 < T) :
    DecidableEq (HexCSFixedIndex T L hT) := inferInstance

def hexCSPairPiece {T L : ℕ} (i : HexCSPairIndex T L) :
    Finset (HexCSIncidence T L) :=
  {i.1, hexCSReflectIncidence i.1}

def hexCSFixedPiece {T L : ℕ} {hT : 0 < T}
    (k : HexCSFixedIndex T L hT) : Finset (HexCSIncidence T L) :=
  {k.1}

def hexCSOrbitPiece {T L : ℕ} {hT : 0 < T}
    (o : HexCSPairIndex T L ⊕ HexCSFixedIndex T L hT) :
    Finset (HexCSIncidence T L) :=
  match o with
  | .inl i => hexCSPairPiece i
  | .inr k => hexCSFixedPiece k

theorem hexCSPairIndex_ne_reflect {T L : ℕ} (i : HexCSPairIndex T L) :
    i.1 ≠ hexCSReflectIncidence i.1 := by
  intro h
  exact (Nat.ne_of_lt i.2.2) (congrArg hexCSIncidenceRank h)

theorem hexCSStartIncidence_reflect (T L : ℕ) (hT : 0 < T) :
    hexCSReflectIncidence (hexCSStartIncidence T L hT) =
      hexCSStartIncidence T L hT := by
  rw [hexCSReflectIncidence, hexCSStartIncidence, HexIncidence.mk.injEq]
  exact ⟨by apply Subtype.ext; rfl, rfl⟩




theorem hexCS_mem_orbit_biUnion_iff {T L : ℕ} (hT : 0 < T)
    (e : HexCSIncidence T L) :
    e ∈ Finset.univ.biUnion
        (hexCSOrbitPiece (T := T) (L := L) (hT := hT)) ↔
      e ∈ hexCSBoundaryIncidences T L ∧
        e ≠ hexCSStartIncidence T L hT := by
  constructor
  · intro he
    rw [Finset.mem_biUnion] at he
    obtain ⟨o, _, heo⟩ := he
    cases o with
    | inl i =>
        simp only [hexCSOrbitPiece, hexCSPairPiece,
          Finset.mem_insert, Finset.mem_singleton] at heo
        rcases heo with rfl | rfl
        · refine ⟨i.2.1, ?_⟩
          intro hs
          apply hexCSPairIndex_ne_reflect i
          calc
            i.1 = hexCSStartIncidence T L hT := hs
            _ = hexCSReflectIncidence (hexCSStartIncidence T L hT) :=
              (hexCSStartIncidence_reflect T L hT).symm
            _ = hexCSReflectIncidence i.1 :=
              congrArg hexCSReflectIncidence hs.symm
        · refine ⟨(hexCSReflectIncidence_mem_boundary_iff i.1).2 i.2.1, ?_⟩
          intro hs
          apply hexCSPairIndex_ne_reflect i
          calc
            i.1 = hexCSReflectIncidence (hexCSReflectIncidence i.1) :=
              (hexCSReflectIncidence_invol i.1).symm
            _ = hexCSReflectIncidence (hexCSStartIncidence T L hT) :=
              congrArg hexCSReflectIncidence hs
            _ = hexCSStartIncidence T L hT :=
              hexCSStartIncidence_reflect T L hT
            _ = hexCSReflectIncidence i.1 := hs.symm
    | inr k =>
        have heq : e = k.1 := by simpa [hexCSOrbitPiece, hexCSFixedPiece] using heo
        subst e
        exact ⟨k.2.1, k.2.2.2⟩
  · rintro ⟨heBoundary, heStart⟩
    by_cases hfixed : hexCSReflectIncidence e = e
    · rw [Finset.mem_biUnion]
      let k : HexCSFixedIndex T L hT := ⟨e, heBoundary, hfixed, heStart⟩
      exact ⟨Sum.inr k, Finset.mem_univ _, by
        simp [hexCSOrbitPiece, hexCSFixedPiece, k]⟩
    · have hrank :
          hexCSIncidenceRank e < hexCSIncidenceRank (hexCSReflectIncidence e) ∨
          hexCSIncidenceRank (hexCSReflectIncidence e) < hexCSIncidenceRank e := by
        rcases lt_trichotomy (hexCSIncidenceRank e)
            (hexCSIncidenceRank (hexCSReflectIncidence e)) with h | h | h
        · exact Or.inl h
        · exact False.elim (hfixed (hexCSIncidenceRank_injective h.symm))
        · exact Or.inr h
      rw [Finset.mem_biUnion]
      cases hrank with
      | inl hlt =>
          let i : HexCSPairIndex T L := ⟨e, heBoundary, hlt⟩
          exact ⟨Sum.inl i, Finset.mem_univ _, by
            simp [hexCSOrbitPiece, hexCSPairPiece, i]⟩
      | inr hlt =>
          let er := hexCSReflectIncidence e
          have herBoundary : er ∈ hexCSBoundaryIncidences T L :=
            (hexCSReflectIncidence_mem_boundary_iff e).2 heBoundary
          have herlt : hexCSIncidenceRank er <
              hexCSIncidenceRank (hexCSReflectIncidence er) := by
            simpa [er] using hlt
          let i : HexCSPairIndex T L := ⟨er, herBoundary, herlt⟩
          exact ⟨Sum.inl i, Finset.mem_univ _, by
            simp [hexCSOrbitPiece, hexCSPairPiece, i, er]⟩

theorem hexCS_boundary_orbit_partition (T L : ℕ) (hT : 0 < T) :
    hexCSBoundaryIncidences T L =
      {hexCSStartIncidence T L hT} ∪
        Finset.univ.biUnion
          (hexCSOrbitPiece (T := T) (L := L) (hT := hT)) := by
  ext e
  rw [Finset.mem_union, Finset.mem_singleton,
    hexCS_mem_orbit_biUnion_iff]
  constructor
  · intro he
    by_cases hs : e = hexCSStartIncidence T L hT
    · exact Or.inl hs
    · exact Or.inr ⟨he, hs⟩
  · rintro (rfl | ⟨he, _⟩)
    · exact hexCSStartIncidence_mem_boundary T L hT
    · exact he

theorem hexCS_start_orbits_disjoint (T L : ℕ) (hT : 0 < T) :
    Disjoint ({hexCSStartIncidence T L hT} : Finset (HexCSIncidence T L))
      (Finset.univ.biUnion
        (hexCSOrbitPiece (T := T) (L := L) (hT := hT))) := by
  rw [Finset.disjoint_left]
  intro e heStart heOrbit
  have hs : e = hexCSStartIncidence T L hT := by simpa using heStart
  exact (hexCS_mem_orbit_biUnion_iff hT e).1 heOrbit |>.2 hs

private theorem hexCS_pairPieces_disjoint {T L : ℕ}
    (i j : HexCSPairIndex T L) (hij : i ≠ j) :
    Disjoint (hexCSPairPiece i) (hexCSPairPiece j) := by
  rw [Finset.disjoint_left]
  intro e hei hej
  simp only [hexCSPairPiece, Finset.mem_insert, Finset.mem_singleton] at hei hej
  rcases hei with hi | hi <;> rcases hej with hj | hj
  · apply hij; apply Subtype.ext; exact hi.symm.trans hj
  · have hcross : i.1 = hexCSReflectIncidence j.1 := hi.symm.trans hj
    have hcross' : hexCSReflectIncidence i.1 = j.1 := by
      have := congrArg hexCSReflectIncidence hcross
      simpa using this
    have hlt := i.2.2
    rw [hcross'] at hlt
    have hgt := j.2.2
    rw [← hcross] at hgt
    omega
  · have hcross : hexCSReflectIncidence i.1 = j.1 := hi.symm.trans hj
    have hcross' : i.1 = hexCSReflectIncidence j.1 := by
      have := congrArg hexCSReflectIncidence hcross
      simpa using this
    have hlt := j.2.2
    rw [← hcross'] at hlt
    have hgt := i.2.2
    rw [hcross] at hgt
    omega
  · apply hij; apply Subtype.ext
    have hreflect : hexCSReflectIncidence i.1 =
        hexCSReflectIncidence j.1 := hi.symm.trans hj
    have := congrArg hexCSReflectIncidence hreflect
    simpa using this

private theorem hexCS_pair_fixed_disjoint {T L : ℕ} {hT : 0 < T}
    (i : HexCSPairIndex T L) (k : HexCSFixedIndex T L hT) :
    Disjoint (hexCSPairPiece i) (hexCSFixedPiece k) := by
  rw [Finset.disjoint_left]
  intro e hei hek
  have heq : e = k.1 := by simpa [hexCSFixedPiece] using hek
  subst e
  simp only [hexCSPairPiece, Finset.mem_insert, Finset.mem_singleton] at hei
  rcases hei with hi | hi
  · apply hexCSPairIndex_ne_reflect i
    calc
      i.1 = k.1 := hi.symm
      _ = hexCSReflectIncidence k.1 := k.2.2.1.symm
      _ = hexCSReflectIncidence i.1 := congrArg hexCSReflectIncidence hi
  · apply hexCSPairIndex_ne_reflect i
    calc
      i.1 = hexCSReflectIncidence (hexCSReflectIncidence i.1) :=
        (hexCSReflectIncidence_invol i.1).symm
      _ = hexCSReflectIncidence k.1 := congrArg hexCSReflectIncidence hi.symm
      _ = k.1 := k.2.2.1
      _ = hexCSReflectIncidence i.1 := hi

private theorem hexCS_fixedPieces_disjoint {T L : ℕ} {hT : 0 < T}
    (k l : HexCSFixedIndex T L hT) (hkl : k ≠ l) :
    Disjoint (hexCSFixedPiece k) (hexCSFixedPiece l) := by
  rw [Finset.disjoint_left]
  intro e hek hel
  apply hkl
  apply Subtype.ext
  have hk : e = k.1 := by simpa [hexCSFixedPiece] using hek
  have hl : e = l.1 := by simpa [hexCSFixedPiece] using hel
  exact hk.symm.trans hl

theorem hexCS_orbitPieces_pairwiseDisjoint (T L : ℕ) (hT : 0 < T) :
    ((Finset.univ : Finset
      (HexCSPairIndex T L ⊕ HexCSFixedIndex T L hT)) :
        Set (HexCSPairIndex T L ⊕ HexCSFixedIndex T L hT)).PairwiseDisjoint
      (hexCSOrbitPiece (T := T) (L := L) (hT := hT)) := by
  intro o _ p _ hop
  cases o with
  | inl i =>
      cases p with
      | inl j =>
          exact hexCS_pairPieces_disjoint i j
            (fun hij => hop (congrArg Sum.inl hij))
      | inr k =>
          exact hexCS_pair_fixed_disjoint i k
  | inr k =>
      cases p with
      | inl i =>
          exact (hexCS_pair_fixed_disjoint i k).symm
      | inr l =>
          exact hexCS_fixedPieces_disjoint k l
            (fun hkl => hop (congrArg Sum.inr hkl))





def hexCSHeading {T L : ℕ} (v : HexCSVertex T L) (e : Fin 3) : ℤ :=
  hexCSCanonicalHeading ⟨v, e⟩

theorem hexCSHeading_geometry {T L : ℕ} (v : HexCSVertex T L)
    (e : Fin 3) :
    hexAWMid v.1 e - hexAWPos v.1 =
      (1 / 2 : ℂ) * hexUnit (hexCSHeading v e) := by
  rw [hexCSHeading, hexCSCanonicalHeading_unit]
  exact hexAWMid_sub_pos v.1 e

theorem hexCSPairIndex_ne_start {T L : ℕ} {hT : 0 < T}
    (i : HexCSPairIndex T L) :
    i.1 ≠ hexCSStartIncidence T L hT := by
  intro hs
  apply hexCSPairIndex_ne_reflect i
  calc
    i.1 = hexCSStartIncidence T L hT := hs
    _ = hexCSReflectIncidence (hexCSStartIncidence T L hT) :=
      (hexCSStartIncidence_reflect T L hT).symm
    _ = hexCSReflectIncidence i.1 :=
      congrArg hexCSReflectIncidence hs.symm

theorem hexCSReflectIncidence_mid {T L : ℕ}
    (e : HexCSIncidence T L) :
    hexAWMid (hexCSReflectIncidence e).vtx.1
        (hexCSReflectIncidence e).edge =
      hsc_refl hexAWStart 1 (hexAWMid e.vtx.1 e.edge) := by
  exact (hexAWMid_reflect_one e.vtx.1 e.edge).symm



noncomputable def hexCSBoundaryPair
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (i : HexCSPairIndex T L) :
    HexMirrorBoundaryPair (hexCSDomain T L hT hlocal)
      (@hexCSHeading T L) :=
  endpointMirrorBoundaryPair_of_reflection
    (@hexCSHeading T L)
    (fun _ => rfl)
    i.1 (hexCSReflectIncidence i.1)
    (hexCSPairIndex_ne_reflect i)
    (hexCSCanonicalHeading i.1)
    (hexCSCanonicalHeading (hexCSReflectIncidence i.1))
    rfl rfl
    (hexCSReflectIncidence_mid i.1)
    (hexCSFiniteRegion_reflect hT)
    (hexCSCanonicalWinding i.1)
    (fun ts hadm => hexCS_deterministic_winding_of_law hlaw i.1 i.2.1
      (hexCSPairIndex_ne_start (hT := hT) i) ts hadm)
    (by
      rw [hexCSCanonicalHeading_reflect i.1 i.2.1
        (hexCSPairIndex_ne_start (hT := hT) i)]
      exact hexPhase_sideTilt_reflect_one _)

@[simp] theorem hexCSBoundaryPair_piece
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (i : HexCSPairIndex T L) :
    (hexCSBoundaryPair T L hT hlocal hlaw i).piece = hexCSPairPiece i := by
  simp [hexCSBoundaryPair, HexMirrorBoundaryPair.piece, hexCSPairPiece,
    endpointMirrorBoundaryPair_of_reflection]

theorem hexCSBoundaryPair_mass_nonneg
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (i : HexCSPairIndex T L) :
    0 ≤ (hexCSBoundaryPair T L hT hlocal hlaw i).mass := by
  apply endpointMirrorBoundaryPair_mass_nonneg



theorem hexCSFixedIndex_heading_one {T L : ℕ} {hT : 0 < T}
    (k : HexCSFixedIndex T L hT) :
    hexCSCanonicalHeading k.1 = 1 := by
  have hedge : k.1.edge = 0 := by
    have he := congrArg (fun e : HexCSIncidence T L => e.edge) k.2.2.1
    change hexAWReflectEdge k.1.edge = k.1.edge at he
    exact (hexAWReflectEdge_fixed_iff k.1.edge).mp he
  have hcoord : hexAWReflectCoord k.1.vtx.1 = k.1.vtx.1 := by
    have hv := congrArg (fun e : HexCSIncidence T L => e.vtx.1) k.2.2.1
    simpa [hexCSReflectIncidence, hexCSReflectVertex] using hv
  have hij : k.1.vtx.1.i = k.1.vtx.1.j := by
    have hi := congrArg HexAWCoord.i hcoord
    symm
    simpa [hexAWReflectCoord] using hi
  obtain hleft | hright | hupp | hlow :=
    hexCS_boundary_classification k.1 k.2.1
  · exfalso
    apply k.2.2.2
    have hcoordOrigin : k.1.vtx.1 = hexAWOriginCoord := by
      have hzero : ∀ c : HexAWCoord,
          c.color = .black → c.i = c.j → hexAWDepth c = 0 →
            c = hexAWOriginCoord := by
        intro c hcolor hcij hdepth
        rcases c with ⟨i, j, color⟩
        simp only at hcolor hcij
        change -(i + j) = 0 at hdepth
        have hi : i = 0 := by omega
        have hj : j = 0 := by omega
        simp [hexAWOriginCoord, hi, hj, hcolor]
      exact hzero k.1.vtx.1 hleft.1 hij hleft.2.2
    rw [HexIncidence.mk.injEq]
    exact ⟨Subtype.ext hcoordOrigin, hedge⟩
  · rcases hright with ⟨hcolor, _, _⟩
    simp [hexCSCanonicalHeading, hcolor, hedge]
  · exact False.elim (by omega)
  · exact False.elim (by omega)

theorem hexCSFixedIndex_winding_zero {T L : ℕ} {hT : 0 < T}
    (k : HexCSFixedIndex T L hT) :
    hexCSCanonicalWinding k.1 = 0 := by
  rw [hexCSCanonicalWinding, hexCSFixedIndex_heading_one k]
  norm_num



noncomputable def hexCSBoundaryFixed
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (k : HexCSFixedIndex T L hT) :
    HexFixedBoundaryPoint (hexCSDomain T L hT hlocal)
      (@hexCSHeading T L) :=
  endpointFixedBoundaryPoint_of_winding
    (@hexCSHeading T L) (fun _ => rfl) k.1
    (hexCSCanonicalHeading k.1) rfl
    (hexCSCanonicalWinding k.1)
    (fun ts hadm => hexCS_deterministic_winding_of_law hlaw k.1 k.2.1
      k.2.2.2 ts hadm)
    (by
      rw [hexCSFixedIndex_heading_one k, hexCSFixedIndex_winding_zero k]
      simp [hexPhase_sideTilt])

@[simp] theorem hexCSBoundaryFixed_piece
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (k : HexCSFixedIndex T L hT) :
    (hexCSBoundaryFixed T L hT hlocal hlaw k).piece = hexCSFixedPiece k := by
  simp [hexCSBoundaryFixed, HexFixedBoundaryPoint.piece, hexCSFixedPiece,
    endpointFixedBoundaryPoint_of_winding]






def HexCSStartReturnLaw (T L : ℕ) (hT : 0 < T) : Prop :=
  ∀ ts : List ℤ,
    (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
        (ofTurns hexAWStart 1 ts).StaysIn
          (hexCSFiniteRegion T L hT).inRegion ∧
        (ofTurns hexAWStart 1 ts).EndsAt hexAWStart →
      ts = []



theorem endpointParafObservable_start_eq_one_of_unique
    (R : HexFiniteRegion) (h0 : ℤ)
    (hunique : ∀ ts : List ℤ,
      (ofTurns R.start h0 ts).EndpointIsLegalSAW ∧
          (ofTurns R.start h0 ts).StaysIn R.inRegion ∧
          (ofTurns R.start h0 ts).EndsAt R.start →
        ts = []) :
    endpointParafObservable R.inRegion R.start h0 R.start
      (5 / 8) hexChi = 1 := by
  unfold endpointParafObservable
  calc
    (∑' ts : List ℤ,
        endpointParafSummand R.inRegion R.start h0 R.start
          (5 / 8) hexChi ts) =
        endpointParafSummand R.inRegion R.start h0 R.start
          (5 / 8) hexChi [] := by
      apply tsum_eq_single
      intro ts hts
      by_cases hguard :
          (ofTurns R.start h0 ts).EndpointIsLegalSAW ∧
            (ofTurns R.start h0 ts).StaysIn R.inRegion ∧
            (ofTurns R.start h0 ts).EndsAt R.start
      · exact (hts (hunique ts hguard)).elim
      · unfold endpointParafSummand
        rw [if_neg hguard]
    _ = 1 := endpointParafSummand_nil R.inRegion R.start h0
      (5 / 8) hexChi R.start_mem

noncomputable def hexCSEndpointBoundaryCore
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hstart : HexCSStartReturnLaw T L hT) :
    HexEndpointBoundaryCore (hexCSFiniteRegion T L hT) 1
      (hexCSDomain T L hT hlocal)
      (hexCSDomainInteriorPairing T L hT hlocal) where
  interior_sub := hexCSDomainInteriorPairing_interior_sub T L hT hlocal
  obs_eq := fun _ => rfl
  start_value := by
    exact endpointParafObservable_start_eq_one_of_unique
      (hexCSFiniteRegion T L hT) 1 hstart



noncomputable def hexCSEndpointMirrorOrbitData
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (hstart : HexCSStartReturnLaw T L hT) :
    HexEndpointMirrorOrbitData
      (I := HexCSPairIndex T L) (K := HexCSFixedIndex T L hT)
      (hexCSEndpointBoundaryCore T L hT hlocal hstart) where
  heading := @hexCSHeading T L
  hgeom := hexCSHeading_geometry
  startIncidence := hexCSStartIncidence T L hT
  start_mid := hexCSStartIncidence_mid T L hT
  start_heading := by
    simp [hexCSHeading, hexCSStartIncidence, hexCSCanonicalHeading,
      hexCSOrigin, hexAWOriginCoord, hexAWTrans]
  pairs := hexCSBoundaryPair T L hT hlocal hlaw
  fixed := hexCSBoundaryFixed T L hT hlocal hlaw
  boundary_partition := by
    rw [hexCSDomain_incidences_eq]
    change hexCSIncidences T L \ hexCSInteriorIncidences T L = _
    simp only [hexCSBoundaryPair_piece T L hT hlocal hlaw,
      hexCSBoundaryFixed_piece T L hT hlocal hlaw]
    ext e
    simp only [Finset.mem_sdiff, hexCS_mem_incidences, true_and,
      hexCS_mem_interior_iff, Finset.mem_union, Finset.mem_singleton]
    constructor
    · intro hinterior
      by_cases hs : e = hexCSStartIncidence T L hT
      · exact Or.inl hs
      · right
        have heBoundary : e ∈ hexCSBoundaryIncidences T L :=
          (hexCS_mem_boundary_iff e).2 hinterior
        rw [Finset.mem_biUnion]
        by_cases hfixed : hexCSReflectIncidence e = e
        · let k : HexCSFixedIndex T L hT :=
            ⟨e, heBoundary, hfixed, hs⟩
          exact ⟨Sum.inr k, Finset.mem_univ _, by
            simp [hexCSFixedPiece, k]⟩
        · have hrank :
              hexCSIncidenceRank e <
                  hexCSIncidenceRank (hexCSReflectIncidence e) ∨
                hexCSIncidenceRank (hexCSReflectIncidence e) <
                  hexCSIncidenceRank e := by
            rcases lt_trichotomy (hexCSIncidenceRank e)
                (hexCSIncidenceRank (hexCSReflectIncidence e)) with h | h | h
            · exact Or.inl h
            · exact False.elim
                (hfixed (hexCSIncidenceRank_injective h.symm))
            · exact Or.inr h
          cases hrank with
          | inl hlt =>
              let i : HexCSPairIndex T L := ⟨e, heBoundary, hlt⟩
              exact ⟨Sum.inl i, Finset.mem_univ _, by
                simp [hexCSPairPiece, i]⟩
          | inr hlt =>
              let er := hexCSReflectIncidence e
              have herBoundary : er ∈ hexCSBoundaryIncidences T L :=
                (hexCSReflectIncidence_mem_boundary_iff e).2 heBoundary
              have herlt : hexCSIncidenceRank er <
                  hexCSIncidenceRank (hexCSReflectIncidence er) := by
                simpa [er] using hlt
              let i : HexCSPairIndex T L := ⟨er, herBoundary, herlt⟩
              exact ⟨Sum.inl i, Finset.mem_univ _, by
                simp [hexCSPairPiece, i, er]⟩
    · rintro (rfl | he)
      · exact (hexCS_mem_boundary_iff _).1
          (hexCSStartIncidence_mem_boundary T L hT)
      · rw [Finset.mem_biUnion] at he
        obtain ⟨o, _, heo⟩ := he
        cases o with
        | inl i =>
            simp only [hexCSPairPiece, Finset.mem_insert,
              Finset.mem_singleton] at heo
            rcases heo with rfl | rfl
            · exact (hexCS_mem_boundary_iff _).1 i.2.1
            · exact (hexCS_mem_boundary_iff _).1
                ((hexCSReflectIncidence_mem_boundary_iff i.1).2 i.2.1)
        | inr k =>
            have heq : e = k.1 := by
              simpa [hexCSFixedPiece] using heo
            subst e
            exact (hexCS_mem_boundary_iff _).1 k.2.1
  start_orbits_disjoint := by
    simpa [hexCSBoundaryPair_piece, hexCSBoundaryFixed_piece] using
      (hexCS_start_orbits_disjoint T L hT)
  orbits_disjoint := by
    simp only [hexCSBoundaryPair_piece, hexCSBoundaryFixed_piece]
    intro o _ p _ hop
    cases o with
    | inl i =>
        cases p with
        | inl j =>
            exact hexCS_pairPieces_disjoint i j
              (fun hij => hop (congrArg Sum.inl hij))
        | inr k =>
            exact hexCS_pair_fixed_disjoint i k
    | inr k =>
        cases p with
        | inl i =>
            exact (hexCS_pair_fixed_disjoint i k).symm
        | inr l =>
            exact hexCS_fixedPieces_disjoint k l
              (fun hkl => hop (congrArg Sum.inr hkl))

noncomputable def hexCSDCSClassification
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (hstart : HexCSStartReturnLaw T L hT) :
    (hexCSEndpointMirrorOrbitData T L hT hlocal hlaw hstart).DCSClassification where
  classOf i := hexCSBoundaryClass i.1
  cos_angle := by
    intro i
    simpa [hexCSEndpointMirrorOrbitData, hexCSBoundaryPair,
      endpointMirrorBoundaryPair_of_reflection] using
        (hexCS_boundary_cosine i.1 i.2.1)



theorem hexCS_endpoint_normalized_dcs_identity
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (hstart : HexCSStartReturnLaw T L hT) :
    let H := hexCSEndpointMirrorOrbitData T L hT hlocal hlaw hstart
    let Kc := hexCSDCSClassification T L hT hlocal hlaw hstart
    hexCl * H.dcsLam Kc + hexCt * H.dcsTau Kc + H.dcsUps Kc = 1 := by
  dsimp only
  exact HexEndpointMirrorOrbitData.normalized_dcs_identity _ _





noncomputable def hexCSA (T L : ℕ) (hT : 0 < T) : ℝ :=
  ∑ i : HexCSPairIndex T L,
    if hexCSBoundaryClass i.1 = .side then
      2 * endpointCountObservable
        (hexCSFiniteRegion T L hT).inRegion hexAWStart 1
        (hexAWMid i.1.vtx.1 i.1.edge) hexChi
    else 0



noncomputable def hexCSE (T L : ℕ) (hT : 0 < T) : ℝ :=
  ∑ i : HexCSPairIndex T L,
    if hexCSBoundaryClass i.1 = .slant then
      2 * endpointCountObservable
        (hexCSFiniteRegion T L hT).inRegion hexAWStart 1
        (hexAWMid i.1.vtx.1 i.1.edge) hexChi
    else 0



noncomputable def hexCSB (T L : ℕ) (hT : 0 < T) : ℝ :=
  (∑ i : HexCSPairIndex T L,
      if hexCSBoundaryClass i.1 = .top then
        2 * endpointCountObservable
          (hexCSFiniteRegion T L hT).inRegion hexAWStart 1
          (hexAWMid i.1.vtx.1 i.1.edge) hexChi
      else 0) +
    ∑ k : HexCSFixedIndex T L hT,
      endpointCountObservable
        (hexCSFiniteRegion T L hT).inRegion hexAWStart 1
        (hexAWMid k.1.vtx.1 k.1.edge) hexChi

theorem hexCS_dcsLam_eq_A
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (hstart : HexCSStartReturnLaw T L hT) :
    let H := hexCSEndpointMirrorOrbitData T L hT hlocal hlaw hstart
    let Kc := hexCSDCSClassification T L hT hlocal hlaw hstart
    H.dcsLam Kc = hexCSA T L hT := by
  rfl

theorem hexCS_dcsTau_eq_E
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (hstart : HexCSStartReturnLaw T L hT) :
    let H := hexCSEndpointMirrorOrbitData T L hT hlocal hlaw hstart
    let Kc := hexCSDCSClassification T L hT hlocal hlaw hstart
    H.dcsTau Kc = hexCSE T L hT := by
  rfl

theorem hexCS_dcsUps_eq_B
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (hstart : HexCSStartReturnLaw T L hT) :
    let H := hexCSEndpointMirrorOrbitData T L hT hlocal hlaw hstart
    let Kc := hexCSDCSClassification T L hT hlocal hlaw hstart
    H.dcsUps Kc = hexCSB T L hT := by
  rfl



theorem hexCS_finite_strip_identity
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (hstart : HexCSStartReturnLaw T L hT) :
    hexCl * hexCSA T L hT + hexCt * hexCSE T L hT +
      hexCSB T L hT = 1 := by
  have h := hexCS_endpoint_normalized_dcs_identity
    T L hT hlocal hlaw hstart
  dsimp only at h
  rw [hexCS_dcsLam_eq_A T L hT hlocal hlaw hstart,
    hexCS_dcsTau_eq_E T L hT hlocal hlaw hstart,
    hexCS_dcsUps_eq_B T L hT hlocal hlaw hstart] at h
  exact h

theorem hexCS_boundary_masses_nonneg
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (hstart : HexCSStartReturnLaw T L hT) :
    0 ≤ hexCSA T L hT ∧ 0 ≤ hexCSE T L hT ∧
      0 ≤ hexCSB T L hT := by
  let H := hexCSEndpointMirrorOrbitData T L hT hlocal hlaw hstart
  let Kc := hexCSDCSClassification T L hT hlocal hlaw hstart
  have hnonneg : ∀ i, 0 ≤ (H.pairs i).mass := by
    intro i
    exact hexCSBoundaryPair_mass_nonneg T L hT hlocal hlaw i
  have h := H.dcs_values_nonneg Kc hnonneg
  simpa [H, Kc, hexCS_dcsLam_eq_A, hexCS_dcsTau_eq_E,
    hexCS_dcsUps_eq_B] using h

end

end StatMech.Universality
