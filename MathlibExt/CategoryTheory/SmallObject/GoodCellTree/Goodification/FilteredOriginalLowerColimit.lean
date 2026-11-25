/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalLowerComparisonCocone
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialCoverColimitGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Genuine filtered-limit preservation of original lower-comparison colimits

The whole original lower set is the actual filtered union. Each refining
stage is its literal preimage. Both layers of actual colimit universal
properties construct the whole original lower-comparison colimit, with
the same original selected point and complete original vertex-leg function.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w u v

namespace CategoryTheory.SmallObject.FilteredOriginalLowerColimit

open Limits LowerSetColimits

variable {P Q : Type w} [Preorder P] [Preorder Q]
  {I : Type w} [Category.{w} I] {C : Type u} [Category.{v} C]
  (f : P →o Q) (F : P ⥤ C) (Y : Q ⥤ C)
  (beta : F ⟶ f.monotone.functor ⋙ Y) (L : LowerSetColimitData Y)
  (D : I ⥤ LowerSet Q)

/-- The same actual original filtered union of original lower labels. -/
abbrev union : LowerSet Q := ⨆ i : I, D.obj i

/-- The complete refining carrier is the preimage of that same original union. -/
abbrev wholeCarrier := OriginalLowerComparisonCocone.carrier f (union D)

/-- Every real original stage is its actual preimage inside the whole refining carrier. -/
def stageCarrier (i : I) : LowerSet (wholeCarrier f D) where
  carrier := {p | f p.1 ∈ D.obj i}
  lower' := by
    intro b a hab hb
    exact (D.obj i).lower' (f.monotone hab) hb

/-- The complete actual original preimage-stage order isomorphism retains the literal labels. -/
def stageOrderIso (i : I) :
    stageCarrier f D i ≃o OriginalLowerComparisonCocone.carrier f (D.obj i) where
  toFun p := ⟨p.1.1, p.2⟩
  invFun p := ⟨⟨p.1, (le_iSup (fun j : I => D.obj j) i) p.2⟩, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- All actual original preimage stages and their same original label maps form a functor. -/
abbrev stageFunctor : I ⥤ LowerSet (wholeCarrier f D) where
  obj := stageCarrier f D
  map h := homOfLE (fun _ hp => memOfLE (leOfHom (D.map h)) hp)

/-- The actual whole original vertex diagram restricted to its original preimage carrier. -/
abbrev wholeDiagram := restriction F (wholeCarrier f D)

/-- The actual original stage vertex cocone is the original lower cocone on the same labels. -/
abbrev stageCocone (i : I) :
    Cocone (restriction (wholeDiagram f F D) (stageCarrier f D i)) :=
  (OriginalLowerComparisonCocone.cocone f F Y beta L (D.obj i)).whisker
    (stageOrderIso f D i).equivalence.functor

/-- Each actual original stage leg keeps its original component and original selected lower leg. -/
def legs (i : I) (p : stageCarrier f D i) :
    (wholeDiagram f F D).obj p.1 ⟶ L.obj (D.obj i) :=
  beta.app p.1.1 ≫ L.ι (D.obj i) ⟨f p.1.1, p.2⟩

/-- Every actual original preimage-stage vertex cocone retains its full naturality. -/
theorem legs_natural (i : I) (p q : stageCarrier f D i) (h : p ⟶ q) :
    (wholeDiagram f F D).map (homOfLE (leOfHom h)) ≫ legs f F Y beta L D i q =
      legs f F Y beta L D i p :=
  (stageCocone f F Y beta L D i).w h

/-- The real original lower-stage maps preserve every actual original preimage vertex leg. -/
theorem legs_step (i j : I) (h : i ⟶ j) (p : stageCarrier f D i) :
    legs f F Y beta L D i p ≫ L.map (leOfHom (D.map h)) =
      legs f F Y beta L D j
        ⟨p.1, memOfLE (leOfHom (D.map h)) p.2⟩ :=
  OriginalLowerComparisonCocone.leg_map f F Y beta L
    (leOfHom (D.map h)) ⟨p.1.1, p.2⟩

/-- The actual original filtered union gives the complete original preimage-stage cover. -/
theorem stage_cover (p : wholeCarrier f D) : ∃ i : I, p ∈ stageCarrier f D i := by
  change ∃ i : I, f p.1 ∈ D.obj i
  exact LowerSet.mem_iSup_iff.1 p.2

variable [IsFiltered I]

/-- Both actual colimit layers retain the same original selected lower points. -/
def piecesIsColimit
    (hPieces : ∀ i : I,
      IsColimit (OriginalLowerComparisonCocone.cocone f F Y beta L (D.obj i))) (i : I) :
    IsColimit (InitialCoverColimitGlue.pieceCocone
      (wholeDiagram f F D) (stageFunctor f D) (L.filteredDiagram D)
      (legs f F Y beta L D) (legs_natural f F Y beta L D) i) :=
  (hPieces i).whiskerEquivalence (stageOrderIso f D i).equivalence

omit [IsFiltered I] in
/-- Every whole original cover leg is the same actual original lower-comparison leg. -/
theorem whole_leg (p : wholeCarrier f D) :
    InitialCoverColimitGlue.wholeLeg (wholeDiagram f F D) (stageFunctor f D)
      (L.filteredDiagram D) (legs f F Y beta L D) (stage_cover f D) (L.filteredCocone D) p =
    OriginalLowerComparisonCocone.leg f F Y beta L (union D) p := by
  let i := InitialCoverColimitGlue.index (stageFunctor f D) (stage_cover f D) p
  have hp : p ∈ stageCarrier f D i :=
    InitialCoverColimitGlue.mem_index (stageFunctor f D) (stage_cover f D) p
  change (beta.app p.1 ≫ L.ι (D.obj i) ⟨f p.1, hp⟩) ≫
    L.map (le_iSup (fun j : I => D.obj j) i) =
      beta.app p.1 ≫ L.ι (union D) ⟨f p.1, p.2⟩
  rw [Category.assoc, L.ι_map]

/-- The complete actual cover cocone retains the original selected point and all legs. -/
def wholeCoconeIso :
    InitialCoverColimitGlue.wholeCocone
      (wholeDiagram f F D) (stageFunctor f D) (L.filteredDiagram D)
      (legs f F Y beta L D) (legs_natural f F Y beta L D)
      (legs_step f F Y beta L D) (stage_cover f D) (L.filteredCocone D) ≅
    OriginalLowerComparisonCocone.cocone f F Y beta L (union D) :=
  Cocone.ext (Iso.refl _) (fun p => by
    change InitialCoverColimitGlue.wholeLeg (wholeDiagram f F D) (stageFunctor f D)
      (L.filteredDiagram D) (legs f F Y beta L D) (stage_cover f D) (L.filteredCocone D) p ≫
      𝟙 _ = OriginalLowerComparisonCocone.leg f F Y beta L (union D) p
    rw [Category.comp_id]
    exact whole_leg f F Y beta L D p)

/-- Actual original stage UPs construct the whole original filtered lower-colimit UP. -/
def wholeIsColimit
    (hPieces : ∀ i : I,
      IsColimit (OriginalLowerComparisonCocone.cocone f F Y beta L (D.obj i))) :
    IsColimit (OriginalLowerComparisonCocone.cocone f F Y beta L (union D)) :=
  IsColimit.ofIsoColimit
    (InitialCoverColimitGlue.wholeIsColimit
      (wholeDiagram f F D) (stageFunctor f D) (L.filteredDiagram D)
      (legs f F Y beta L D) (legs_natural f F Y beta L D)
      (legs_step f F Y beta L D) (stage_cover f D) (L.filteredCocone D)
      (piecesIsColimit f F Y beta L D hPieces) (L.isColimitFilteredCocone (B := D)))
    (wholeCoconeIso f F Y beta L D)

end CategoryTheory.SmallObject.FilteredOriginalLowerColimit
