/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.Z2GaugeCubicalDualGeometry

open scoped symmDiff
open Finset

namespace StatMech.FrontierA

noncomputable section

local instance cubicalDualEquivPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def cubicalLowerXYTrace {a b c : Nat}
    (A : Finset (CubicalPlaquette a b c)) : Finset (CubicalCell a b c) :=
  Finset.univ.filter fun q =>
    CubicalPlaquette.xy q.x q.y q.z.castSucc ∈ A

abbrev ClosedCubicalSurface (a b c : Nat) :=
  {A : Finset (CubicalPlaquette a b c) //
    A ∈ gaugeClosedSurfaceFamily cubicalPlaquetteIncidence}

theorem cubicalLowerXYTrace_injective {a b c : Nat}
    (hb : 0 < b) (hc : 0 < c) :
    Function.Injective (fun A : ClosedCubicalSurface a b c =>
      cubicalLowerXYTrace A.1) := by
  intro A B htrace
  have hA : IsClosedPlaquetteSet cubicalPlaquetteIncidence A.1 :=
    (mem_gaugeClosedSurfaceFamily_iff cubicalPlaquetteIncidence A.1).mp A.2
  have hB : IsClosedPlaquetteSet cubicalPlaquetteIncidence B.1 :=
    (mem_gaugeClosedSurfaceFamily_iff cubicalPlaquetteIncidence B.1).mp B.2
  have hclosed : IsClosedPlaquetteSet cubicalPlaquetteIncidence (A.1 ∆ B.1) := by
    intro e
    apply (even_plaquetteIncidenceCount_symmDiff_iff
      cubicalPlaquetteIncidence A.1 B.1 e).mpr
    exact ⟨fun _ => hB e, fun _ => hA e⟩
  have hxy : ∀ (i : Fin a) (j : Fin b) (k : Fin c),
      CubicalPlaquette.xy i j k.castSucc ∉ A.1 ∆ B.1 := by
    intro i j k
    have hmem := Finset.ext_iff.mp htrace ⟨i, j, k⟩
    simp only [cubicalLowerXYTrace, mem_filter, mem_univ, true_and] at hmem
    simp [mem_symmDiff, hmem]
  have hempty := closed_eq_empty_of_lowerXY_not_mem hb hc
    (A.1 ∆ B.1) hclosed hxy
  apply Subtype.ext
  exact Finset.symmDiff_eq_empty.mp hempty

def cubicalVolumeSurface {a b c : Nat} (S : Finset (CubicalCell a b c)) :
    ClosedCubicalSurface a b c :=
  ⟨cubicalVolumeBoundary S,
    (mem_gaugeClosedSurfaceFamily_iff cubicalPlaquetteIncidence _).mpr
      (cubicalVolumeBoundary_isClosed S)⟩

theorem cubicalVolumeSurface_injective {a b c : Nat} (hc : 0 < c) :
    Function.Injective (cubicalVolumeSurface (a := a) (b := b) (c := c)) := by
  intro S T hst
  have hval := congrArg Subtype.val hst
  change cubicalVolumeBoundary S = cubicalVolumeBoundary T at hval
  have hboundary : cubicalVolumeBoundary (S ∆ T) = ∅ := by
    rw [cubicalVolumeBoundary, gaugeSurfaceBoundary_symmDiff]
    change cubicalVolumeBoundary S ∆ cubicalVolumeBoundary T = ∅
    rw [hval]
    simp
  have hxy : ∀ (i : Fin a) (j : Fin b) (k : Fin c),
      CubicalPlaquette.xy i j k.castSucc ∉ cubicalVolumeBoundary (S ∆ T) := by
    intro i j k
    rw [hboundary]
    simp
  have hempty := volume_eq_empty_of_lowerXY_boundary_not_mem hc (S ∆ T) hxy
  exact Finset.symmDiff_eq_empty.mp hempty

theorem card_closedCubicalSurface_eq_card_cellFinset
    {a b c : Nat} (hb : 0 < b) (hc : 0 < c) :
    Fintype.card (ClosedCubicalSurface a b c) =
      Fintype.card (Finset (CubicalCell a b c)) := by
  apply le_antisymm
  · exact Fintype.card_le_of_injective _
      (cubicalLowerXYTrace_injective hb hc)
  · exact Fintype.card_le_of_injective _
      (cubicalVolumeSurface_injective hc)

noncomputable def cubicalVolumeSurfaceEquiv
    {a b c : Nat} (hb : 0 < b) (hc : 0 < c) :
    Finset (CubicalCell a b c) ≃ ClosedCubicalSurface a b c :=
  Equiv.ofBijective cubicalVolumeSurface
    ((Fintype.bijective_iff_injective_and_card cubicalVolumeSurface).mpr
      ⟨cubicalVolumeSurface_injective hc,
        (card_closedCubicalSurface_eq_card_cellFinset hb hc).symm⟩)

@[simp] theorem cubicalVolumeSurfaceEquiv_apply
    {a b c : Nat} (hb : 0 < b) (hc : 0 < c)
    (S : Finset (CubicalCell a b c)) :
    (cubicalVolumeSurfaceEquiv hb hc S).1 = cubicalVolumeBoundary S :=
  rfl



def cellFinsetAnchoredEquiv {a b c : Nat} :
    Finset (CubicalCell a b c) ≃
      AnchoredConfig (Option (CubicalCell a b c)) none where
  toFun S := ⟨fun q => match q with
    | none => false
    | some x => decide (x ∈ S), rfl⟩
  invFun s := Finset.univ.filter fun q => s.1 (some q) = true
  left_inv S := by
    ext q
    simp
  right_inv s := by
    apply Subtype.ext
    funext q
    cases q with
    | none => exact s.2.symm
    | some q =>
        cases h : s.1 (some q) <;> simp [h]


def finBackward {n : Nat} (k : Fin (n + 1)) : Option (Fin n) :=
  Fin.cases none some k


def finForward {n : Nat} (k : Fin (n + 1)) : Option (Fin n) :=
  Fin.lastCases none some k

@[simp] theorem finBackward_eq_some_iff {n : Nat}
    (f : Fin (n + 1)) (k : Fin n) :
    finBackward f = some k ↔ f = k.succ := by
  refine Fin.cases ?_ (fun z => ?_) f
  · simp only [finBackward, Fin.cases_zero]
    constructor
    · intro h
      simp at h
    · intro h
      have hv := congrArg Fin.val h
      simp at hv
  · simp [finBackward]

@[simp] theorem finForward_eq_some_iff {n : Nat}
    (f : Fin (n + 1)) (k : Fin n) :
    finForward f = some k ↔ f = k.castSucc := by
  refine Fin.lastCases ?_ (fun z => ?_) f
  · simp only [finForward, Fin.lastCases_last]
    constructor
    · intro h
      simp at h
    · intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
  · simp [finForward]



abbrev CubicalDualVertex (a b c : Nat) := Option (CubicalCell a b c)



def cubicalDualEnds {a b c : Nat} :
    CubicalPlaquette a b c →
      CubicalDualVertex a b c × CubicalDualVertex a b c
  | .xy i j k =>
      ((finBackward k).map fun z => ⟨i, j, z⟩,
        (finForward k).map fun z => ⟨i, j, z⟩)
  | .xz i j k =>
      ((finBackward j).map fun y => ⟨i, y, k⟩,
        (finForward j).map fun y => ⟨i, y, k⟩)
  | .yz i j k =>
      ((finBackward i).map fun x => ⟨x, j, k⟩,
        (finForward i).map fun x => ⟨x, j, k⟩)


def cubicalPlaquetteCells {a b c : Nat} (p : CubicalPlaquette a b c) :
    Finset (CubicalCell a b c) :=
  (cubicalDualEnds p).1.toFinset ∪ (cubicalDualEnds p).2.toFinset

theorem mem_cubicalPlaquetteCells_iff_mem_cellFaces
    {a b c : Nat} (q : CubicalCell a b c) (p : CubicalPlaquette a b c) :
    q ∈ cubicalPlaquetteCells p ↔ p ∈ cubicalCellFaces q := by
  rcases q with ⟨i, j, k⟩
  cases p <;>
    simp [cubicalPlaquetteCells, cubicalDualEnds, cubicalCellFaces] <;> tauto

theorem plaquetteIncidenceCount_cellFaces_eq
    {a b c : Nat} (S : Finset (CubicalCell a b c))
    (p : CubicalPlaquette a b c) :
    plaquetteIncidenceCount cubicalCellFaces S p =
      (S.filter fun q => q ∈ cubicalPlaquetteCells p).card := by
  rw [plaquetteIncidenceCount_eq_filter_card]
  congr 1
  ext q
  simp only [mem_filter]
  rw [mem_cubicalPlaquetteCells_iff_mem_cellFaces]


def selectedOptionSpin {α : Type*} [DecidableEq α] (S : Finset α) :
    Option α → Bool
  | none => false
  | some q => decide (q ∈ S)



theorem selectedOptionSpin_ne_iff_not_even
    {α : Type*} [DecidableEq α] (S : Finset α)
    {u v : Option α} (huv : u ≠ v) :
    selectedOptionSpin S u ≠ selectedOptionSpin S v ↔
      ¬ Even ((S.filter fun q => q ∈ u.toFinset ∪ v.toFinset).card) := by
  cases u with
  | none =>
      cases v with
      | none => exact False.elim (huv rfl)
      | some y =>
          simp only [selectedOptionSpin, Option.toFinset_none,
            Option.toFinset_some, empty_union, mem_singleton]
          rw [Finset.filter_eq' S y]
          by_cases hy : y ∈ S <;> simp [hy]
  | some x =>
      cases v with
      | none =>
          simp only [selectedOptionSpin, Option.toFinset_none,
            Option.toFinset_some, union_empty, mem_singleton]
          rw [Finset.filter_eq' S x]
          by_cases hx : x ∈ S <;> simp [hx]
      | some y =>
          have hxy : x ≠ y := by
            intro h
            exact huv (by simp [h])
          simp only [selectedOptionSpin, Option.toFinset_some,
            mem_union, mem_singleton]
          rw [Finset.filter_or, Finset.filter_eq' S x,
            Finset.filter_eq' S y]
          by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;>
            simp [hx, hy, hxy]

@[simp] theorem finBackward_eq_none_iff {n : Nat} (f : Fin (n + 1)) :
    finBackward f = none ↔ f = 0 := by
  refine Fin.cases ?_ (fun z => ?_) f
  · simp [finBackward]
  · simp [finBackward]

theorem finBackward_ne_finForward {n : Nat} (hn : 0 < n)
    (f : Fin (n + 1)) :
    finBackward f ≠ finForward f := by
  intro h
  cases hb : finBackward f with
  | none =>
      have hf : f = 0 := (finBackward_eq_none_iff f).mp hb
      subst f
      let z : Fin n := ⟨0, hn⟩
      have hforward : finForward (0 : Fin (n + 1)) = some z :=
        (finForward_eq_some_iff 0 z).mpr (Fin.ext (by simp [z]))
      simp [hb, hforward] at h
  | some k =>
      have hforward : finForward f = some k := by
        rw [← h]
        exact hb
      have hsucc : f = k.succ := (finBackward_eq_some_iff f k).mp hb
      have hcast : f = k.castSucc :=
        (finForward_eq_some_iff f k).mp hforward
      have hv := congrArg Fin.val (hsucc.symm.trans hcast)
      simp at hv

theorem cubicalDualEnds_ne {a b c : Nat}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (p : CubicalPlaquette a b c) :
    (cubicalDualEnds p).1 ≠ (cubicalDualEnds p).2 := by
  cases p with
  | xy i j k =>
      intro h
      apply finBackward_ne_finForward hc k
      exact Option.map_injective (fun _ _ h => congrArg CubicalCell.z h) h
  | xz i j k =>
      intro h
      apply finBackward_ne_finForward hb j
      exact Option.map_injective (fun _ _ h => congrArg CubicalCell.y h) h
  | yz i j k =>
      intro h
      apply finBackward_ne_finForward ha i
      exact Option.map_injective (fun _ _ h => congrArg CubicalCell.x h) h

@[simp] theorem cellFinsetAnchoredEquiv_apply
    {a b c : Nat} (S : Finset (CubicalCell a b c))
    (q : Option (CubicalCell a b c)) :
    (cellFinsetAnchoredEquiv S).1 q = selectedOptionSpin S q := by
  cases q <;> rfl



theorem multibondCut_cellFinsetAnchored_eq_volumeBoundary
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (S : Finset (CubicalCell a b c)) :
    multibondCut cubicalDualEnds (cellFinsetAnchoredEquiv S).1 =
      cubicalVolumeBoundary S := by
  ext p
  rw [mem_multibondCut, cubicalVolumeBoundary, mem_gaugeSurfaceBoundary,
    plaquetteIncidenceCount_cellFaces_eq]
  simpa [cubicalPlaquetteCells] using
    (selectedOptionSpin_ne_iff_not_even S (cubicalDualEnds_ne ha hb hc p))



noncomputable def cubicalClosedSurfaceAnchoredEquiv
    {a b c : Nat} (hb : 0 < b) (hc : 0 < c) :
    ClosedCubicalSurface a b c ≃
      AnchoredConfig (CubicalDualVertex a b c) none :=
  (cubicalVolumeSurfaceEquiv hb hc).symm.trans cellFinsetAnchoredEquiv

theorem multibondCut_cubicalClosedSurfaceAnchoredEquiv
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (A : ClosedCubicalSurface a b c) :
    multibondCut cubicalDualEnds
        (cubicalClosedSurfaceAnchoredEquiv hb hc A).1 = A.1 := by
  change multibondCut cubicalDualEnds
      (cellFinsetAnchoredEquiv ((cubicalVolumeSurfaceEquiv hb hc).symm A)).1 = A.1
  rw [multibondCut_cellFinsetAnchored_eq_volumeBoundary ha hb hc]
  have h := congrArg Subtype.val
    ((cubicalVolumeSurfaceEquiv hb hc).apply_symm_apply A)
  exact h



theorem cubical_gaugePartition_isingDuality
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (K : CubicalPlaquette a b c → Real) (hK : ∀ p, 0 < K p) :
    (Real.exp (∑ p : CubicalPlaquette a b c,
        gaugeDualCoupling (K p)) * 2) *
        gaugePartition cubicalPlaquetteIncidence K =
      ((2 : Real) ^ Fintype.card (CubicalEdge a b c) *
        ∏ p : CubicalPlaquette a b c, Real.cosh (K p)) *
        multibondIsingPartition cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) := by
  apply gaugePartition_multibondIsingDuality
    cubicalPlaquetteIncidence K hK none cubicalDualEnds
    (cubicalClosedSurfaceAnchoredEquiv hb hc)
  exact multibondCut_cubicalClosedSurfaceAnchoredEquiv ha hb hc



theorem cubicalXYWilsonExpectation_eq_typedDisorderRatio
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (K : CubicalPlaquette a b c → Real)
    (hK : ∀ p, 0 < K p) :
    gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) =
      (∑ s : AnchoredConfig (CubicalDualVertex a b c) none,
          ∏ p ∈ multibondCut cubicalDualEnds s.1 ∆ cubicalXYSheet k,
            Real.exp (-2 * gaugeDualCoupling (K p))) /
        (∑ s : AnchoredConfig (CubicalDualVertex a b c) none,
          ∏ p ∈ multibondCut cubicalDualEnds s.1,
            Real.exp (-2 * gaugeDualCoupling (K p))) := by
  apply gaugeWilsonExpectation_eq_multibondDisorderRatio_of_sheet
    cubicalPlaquetteIncidence K hK (cubicalXYLoop k) (cubicalXYSheet k)
    (cubicalXYSheet_hasWilsonBoundary k) none cubicalDualEnds
    (cubicalClosedSurfaceAnchoredEquiv hb hc)
  exact multibondCut_cubicalClosedSurfaceAnchoredEquiv ha hb hc

end

end StatMech.FrontierA
