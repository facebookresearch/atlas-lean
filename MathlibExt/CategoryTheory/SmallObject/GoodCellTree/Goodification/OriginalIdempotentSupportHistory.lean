/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tsutomu Okano, Codex
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalIdempotentLowerSupport
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.IdempotentIntersection
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalCellWellOrderEnumeration

/-!
# Exhaustive original idempotent lower-support histories

The original lower objects and maps carry endpoint-compatible idempotents.
At a limit their actual union colimit constructs the idempotent. At a birth
the bounded original intersection construction and the actual union pushout
construct the next support. The original whole label carrier is retained.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe w t u v uI vI

namespace CategoryTheory.SmallObject.OriginalIdempotentSupportHistory

open CategoryTheory.Limits OriginalIdempotentLowerSupport

variable {C : Type u} [Category.{v} C] {X : C}
  {P : Type w} [PartialOrder P] {alpha : Type t} {s : alpha → Arrow C}
  (T : CellTree s X (P := P)) (L : LowerSetColimitData T.diagram)
  (q : T.endpointObj ⟶ T.endpointObj)

/-- The actual original inclusions form the category of stable lower supports. -/
instance : Category (State T L q) where
  Hom A B := State.Inclusion A B
  id A := State.Inclusion.identity A
  comp a b := State.Inclusion.comp a b
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

/-- Forget only the idempotent, retaining the original lower label support. -/
abbrev supportFunctor : State T L q ⥤ LowerSet P where
  obj A := A.support
  map {A B} f := homOfLE (State.Inclusion.le (f : State.Inclusion A B))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

variable {T L q} {I : Type uI} [Category.{vI} I]
  (F : I ⥤ State T L q)

/-- The literal original selected lower-object diagram. -/
abbrev originalDiagram : I ⥤ Under X :=
  L.filteredDiagram (F ⋙ supportFunctor T L q)

/-- The given actual lower idempotents are natural on the original diagram. -/
def diagramIdempotent : originalDiagram F ⟶ originalDiagram F where
  app a := (F.obj a).e
  naturality _ _ f := (F.map f).commutes.symm

variable [IsFiltered I]

/-- The actual original union endomorphism is induced by the same selected colimit UP. -/
def filteredEndomorphism :
    L.obj (LowerSetColimitData.filteredUnion (F ⋙ supportFunctor T L q)) ⟶
      L.obj (LowerSetColimitData.filteredUnion (F ⋙ supportFunctor T L q)) :=
  (L.isColimitFilteredCocone (B := F ⋙ supportFunctor T L q)).map
    (L.filteredCocone (F ⋙ supportFunctor T L q)) (diagramIdempotent F)

theorem map_filteredEndomorphism (a : I) :
    L.map (le_iSup (fun j => (F.obj j).support) a) ≫ filteredEndomorphism F =
      (F.obj a).e ≫ L.map (le_iSup (fun j => (F.obj j).support) a) :=
  (L.isColimitFilteredCocone (B := F ⋙ supportFunctor T L q)).ι_map
    (L.filteredCocone (F ⋙ supportFunctor T L q)) (diagramIdempotent F) a

/-- A genuine filtered original union has its constructed endpoint-compatible idempotent. -/
def filteredUnionState : State T L q where
  support := LowerSetColimitData.filteredUnion (F ⋙ supportFunctor T L q)
  e := filteredEndomorphism F
  idempotent := by
    apply (L.isColimitFilteredCocone (B := F ⋙ supportFunctor T L q)).hom_ext
    intro a
    change L.map (le_iSup (fun j => (F.obj j).support) a) ≫
        (filteredEndomorphism F ≫ filteredEndomorphism F) =
      L.map (le_iSup (fun j => (F.obj j).support) a) ≫ filteredEndomorphism F
    rw [← Category.assoc, map_filteredEndomorphism, Category.assoc,
      map_filteredEndomorphism, ← Category.assoc, (F.obj a).idempotent]
  endpoint := by
    apply (L.isColimitFilteredCocone (B := F ⋙ supportFunctor T L q)).hom_ext
    intro a
    change L.map (le_iSup (fun j => (F.obj j).support) a) ≫
        (filteredEndomorphism F ≫ endpointLeg T L _) =
      L.map (le_iSup (fun j => (F.obj j).support) a) ≫ (endpointLeg T L _ ≫ q)
    rw [← Category.assoc, map_filteredEndomorphism]
    change ((F.obj a).e ≫ L.map (le_iSup (fun j => (F.obj j).support) a)) ≫
        endpointLeg T L (⨆ j, (F.obj j).support) =
      L.map (le_iSup (fun j => (F.obj j).support) a) ≫
        (endpointLeg T L (⨆ j, (F.obj j).support) ≫ q)
    rw [Category.assoc, map_endpointLeg T L (le_iSup (fun j => (F.obj j).support) a),
      (F.obj a).endpoint, ← Category.assoc,
      map_endpointLeg T L (le_iSup (fun j => (F.obj j).support) a)]

/-- Every earlier actual idempotent and original inclusion survives the limit union. -/
def filteredUnionInclusion (a : I) : State.Inclusion (F.obj a) (filteredUnionState F) where
  le := le_iSup (fun j => (F.obj j).support) a
  commutes := (map_filteredEndomorphism F a).symm

variable (T L q)

/-- A constructed bounded birth retains its literal overlap and all original squares. -/
structure BoundedBirth (A : State T L q) (chi : Cardinal.{w}) (seed : Set P) where
  /-- The bounded original lower piece carrying the endpoint-compatible idempotent. -/
  piece : State T L q
  /-- The idempotent and inclusion squares on the literal BEFORE-piece intersection. -/
  overlap : Intersection A piece
  contains : seed ⊆ piece.support
  bounded : HasCardinalLT (piece.support : Set P) chi
  overlap_bounded : HasCardinalLT ((A.support ⊓ piece.support : LowerSet P) : Set P) chi

namespace BoundedBirth

variable {T L q} {A : State T L q} {chi : Cardinal.{w}} {seed : Set P}
  (B : BoundedBirth T L q A chi seed)

/-- The AFTER idempotent is the actual original lower-union pushout descender. -/
abbrev after : State T L q := B.overlap.union

/-- The original BEFORE map and idempotent square survive the birth. -/
abbrev beforeInclusion : State.Inclusion A B.after := B.overlap.leftInclusion

/-- The original bounded-piece map and idempotent square survive the birth. -/
abbrev pieceInclusion : State.Inclusion B.piece B.after := B.overlap.rightInclusion

/-- The actual added labels are a subset of the constructed bounded piece. -/
theorem difference_bounded : HasCardinalLT
    (((B.after.support : Set P) \ (A.support : Set P)) : Set P) chi := by
  refine B.bounded.of_injective
    (fun p : {p : P // p ∈ B.after.support ∧ p ∉ A.support} =>
      (⟨p.1, ?_⟩ : (B.piece.support : Set P)))
    (fun _ _ h => Subtype.ext
      (congrArg (fun z : {p : P // p ∈ B.piece.support} => z.1) h))
  have hp := p.2.1
  change p.1 ∈ A.support ⊔ B.piece.support at hp
  exact (LowerSet.mem_sup_iff.mp hp).resolve_left p.2.2

end BoundedBirth

variable [LocallySmall.{w} C] [HasBinaryCoproducts C]
  (hq : q ≫ q = q) (chi : Cardinal.{w}) [Fact chi.IsRegular]
  (hUncountable : Cardinal.aleph0 < chi) (good : T.IsGood chi)

include hq hUncountable good in
/-- The finite-idempotent intersection theorem constructs the bounded piece and overlap. -/
theorem existsBoundedBirth (A : State T L q) (seed : Set P)
    (hseed : HasCardinalLT seed chi) : Nonempty (BoundedBirth T L q A chi seed) := by
  obtain ⟨U, hcontains, hU, hBU, eU, eBU, heU, heBU, hleft, hright, hend, _⟩ :=
    IdempotentIntersection.existsIdempotentIntersection T L q hq chi
      hUncountable good A.support A.e A.idempotent A.endpoint seed hseed
  exact ⟨
    { piece := { support := U, e := eU, idempotent := heU, endpoint := hend }
      overlap := { e := eBU, idempotent := heBU, left := hleft, right := hright }
      contains := hcontains
      bounded := hU
      overlap_bounded := hBU }⟩

/-- The actual chosen bounded birth is produced from the original maps, not supplied. -/
def boundedBirth (A : State T L q) (seed : Set P)
    (hseed : HasCardinalLT seed chi) : BoundedBirth T L q A chi seed :=
  Classical.choice (existsBoundedBirth T L q hq chi hUncountable good A seed hseed)

variable [WellFoundedLT P]

omit [LocallySmall.{w} C] [HasBinaryCoproducts C] in
/-- Missing labels are measured in the well-order extension of the same original carrier. -/
def missingLabels (A : State T L q) :
    Set (OriginalCellWellOrderEnumeration.Index (P := P)) :=
  {a | OriginalCellWellOrderEnumeration.labels.symm a ∉ A.support}

omit [LocallySmall.{w} C] [HasBinaryCoproducts C] in
/-- A birth seeds exactly the least missing original label, or no label after exhaustion. -/
def nextSeed (A : State T L q) : Set P := by
  classical
  exact if h : (missingLabels T L q A).Nonempty then
    {OriginalCellWellOrderEnumeration.labels.symm
      (WellFoundedLT.min (missingLabels T L q A) h)}
  else ∅

omit [LocallySmall.{w} C] [HasBinaryCoproducts C] in
theorem nextSeed_finite (A : State T L q) : (nextSeed T L q A).Finite := by
  classical
  unfold nextSeed
  split
  · exact Set.finite_singleton _
  · exact Set.finite_empty

/-- The empty original support and every later original state admit the actual next birth. -/
def nextBirth (A : State T L q) : BoundedBirth T L q A chi (nextSeed T L q A) := by
  letI : Finite (nextSeed T L q A) := (nextSeed_finite T L q A).to_subtype
  exact boundedBirth T L q hq chi hUncountable good A (nextSeed T L q A)
    (hasCardinalLT_of_finite _ chi hUncountable.le)

include hq hUncountable good in
/-- Capturing all preceding original labels forces the actual birth to capture this label. -/
theorem nextBirth_captures (A : State T L q) (a : P)
    (hbefore : ∀ b : P, OriginalCellWellOrderEnumeration.labels b <
      OriginalCellWellOrderEnumeration.labels a → b ∈ A.support) :
    a ∈ (nextBirth T L q hq chi hUncountable good A).after.support := by
  classical
  by_cases ha : a ∈ A.support
  · exact (nextBirth T L q hq chi hUncountable good A).beforeInclusion.le ha
  · let am := OriginalCellWellOrderEnumeration.labels a
    have ham : am ∈ missingLabels T L q A := by simpa [am, missingLabels] using ha
    let hn : (missingLabels T L q A).Nonempty := ⟨am, ham⟩
    let m := WellFoundedLT.min (missingLabels T L q A) hn
    have hm : m ∈ missingLabels T L q A := wellFounded_lt.min_mem _ hn
    have hma : m ≤ am := by
      exact WellFoundedLT.min_le ham
    have ham' : am ≤ m := by
      apply le_of_not_gt
      intro h
      exact hm (hbefore (OriginalCellWellOrderEnumeration.labels.symm m)
        (by simpa [am] using h))
    have heq : m = am := le_antisymm hma ham'
    have hseed : a ∈ nextSeed T L q A := by
      simp only [nextSeed, dite_eq_left hn, Set.mem_singleton_iff]
      change a = OriginalCellWellOrderEnumeration.labels.symm m
      rw [heq]
      exact (OriginalCellWellOrderEnumeration.labels.symm_apply_apply a).symm
    exact (nextBirth T L q hq chi hUncountable good A).pieceInclusion.le
      ((nextBirth T L q hq chi hUncountable good A).contains hseed)

end CategoryTheory.SmallObject.OriginalIdempotentSupportHistory
