/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# Genuine colimit gluing across actual filtered initial-stage covers

Every whole vertex leg is selected from a real containing stage. Actual
stage-map equations and the original filtered cocone prove its independence
of that choice. The two actual layers of colimit universal properties then
construct the whole colimit, with its complete descender and leg function.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w u v

namespace CategoryTheory.SmallObject.InitialCoverColimitGlue

open Limits LowerSetColimits

variable {P : Type w} [Preorder P] {I : Type w} [Category.{w} I]
  {C : Type u} [Category.{v} C]
  (Y : P ⥤ C) (B : I ⥤ LowerSet P) (H : I ⥤ C)
  (legs : ∀ (i : I) (p : B.obj i), Y.obj p.1 ⟶ H.obj i)
  (hNatural : ∀ (i : I) (p q : B.obj i) (h : p ⟶ q),
    Y.map (homOfLE (leOfHom h)) ≫ legs i q = legs i p)
  (hStep : ∀ (i j : I) (h : i ⟶ j) (p : B.obj i),
    legs i p ≫ H.map h =
      legs j ⟨p.1, memOfLE (leOfHom (B.map h)) p.2⟩)
  (hCover : ∀ p : P, ∃ i : I, p ∈ B.obj i)
  (HC : Cocone H)

/-- The actual stage vertex cocone keeps the given original stage point and leg function. -/
abbrev pieceCocone (i : I) : Cocone (restriction Y (B.obj i)) where
  pt := H.obj i
  ι :=
    { app := legs i
      naturality p q h := by
        change Y.map (homOfLE (leOfHom h)) ≫ legs i q = legs i p ≫ 𝟙 _
        rw [Category.comp_id]
        exact hNatural i p q h }

/-- An actual original stage is chosen for each whole original vertex. -/
def index (p : P) : I := (hCover p).choose

/-- The original vertex is in the actual chosen original stage. -/
theorem mem_index (p : P) : p ∈ B.obj (index B hCover p) := (hCover p).choose_spec

include hStep in
/-- Actual filtered stage equations retain each original vertex leg at any containing stage. -/
theorem leg_overlap [IsFiltered I] (p : P) (i j : I)
    (hi : p ∈ B.obj i) (hj : p ∈ B.obj j) :
    legs i ⟨p, hi⟩ ≫ HC.ι.app i = legs j ⟨p, hj⟩ ≫ HC.ι.app j := by
  let k := IsFiltered.max i j
  let fi := IsFiltered.leftToMax i j
  let fj := IsFiltered.rightToMax i j
  have hfi := (HC.w fi).symm
  have hfj := (HC.w fj).symm
  rw [hfi, hfj, ← Category.assoc, hStep i k fi, ← Category.assoc, hStep j k fj]

/-- The whole original vertex leg uses the actual stage leg and original filtered cocone leg. -/
def wholeLeg (p : P) : Y.obj p ⟶ HC.pt :=
  legs (index B hCover p) ⟨p, mem_index B hCover p⟩ ≫ HC.ι.app (index B hCover p)

include hStep in
/-- The complete actual whole leg is unchanged when any containing original stage is used. -/
theorem wholeLeg_eq [IsFiltered I] (p : P) (i : I) (hp : p ∈ B.obj i) :
    wholeLeg Y B H legs hCover HC p = legs i ⟨p, hp⟩ ≫ HC.ι.app i :=
  leg_overlap Y B H legs hStep HC p (index B hCover p) i (mem_index B hCover p) hp

/-- The actual whole original cocone is constructed from the original filtered stage legs. -/
abbrev wholeCocone [IsFiltered I] : Cocone Y where
  pt := HC.pt
  ι :=
    { app := wholeLeg Y B H legs hCover HC
      naturality p q h := by
        let i := index B hCover q
        have hq : q ∈ B.obj i := mem_index B hCover q
        have hp : p ∈ B.obj i := (B.obj i).lower' (leOfHom h) hq
        change Y.map h ≫ wholeLeg Y B H legs hCover HC q =
          wholeLeg Y B H legs hCover HC p ≫ 𝟙 _
        rw [Category.comp_id, wholeLeg_eq Y B H legs hStep hCover HC q i hq,
          wholeLeg_eq Y B H legs hStep hCover HC p i hp]
        have hn := hNatural i (⟨p, hp⟩ : B.obj i) ⟨q, hq⟩ (homOfLE (leOfHom h))
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (fun m => m ≫ HC.ι.app i) hn) }

variable (hPieces : ∀ i : I, IsColimit (pieceCocone Y B H legs hNatural i))

/-- Each actual stage descender comes from the original local vertex colimit. -/
def stageDesc (s : Cocone Y) (i : I) : H.obj i ⟶ s.pt :=
  (hPieces i).desc (s.whisker (inclusion (B.obj i : Set P)))

/-- The complete stage descender preserves each actual original vertex leg. -/
theorem stageDesc_fac (s : Cocone Y) (i : I) (p : B.obj i) :
    legs i p ≫ stageDesc Y B H legs hNatural hPieces s i = s.ι.app p.1 :=
  (hPieces i).fac (s.whisker (inclusion (B.obj i : Set P))) p

include hStep in
/-- Actual stage-map and local-colimit equations prove the complete stage-descender naturality. -/
theorem stageDesc_naturality (s : Cocone Y) (i j : I) (h : i ⟶ j) :
    H.map h ≫ stageDesc Y B H legs hNatural hPieces s j =
      stageDesc Y B H legs hNatural hPieces s i := by
  apply (hPieces i).hom_ext
  intro p
  change legs i p ≫ (H.map h ≫ stageDesc Y B H legs hNatural hPieces s j) =
    legs i p ≫ stageDesc Y B H legs hNatural hPieces s i
  rw [← Category.assoc, hStep i j h, stageDesc_fac, stageDesc_fac]

/-- The whole actual local-descender function forms a cocone on the original stage diagram. -/
abbrev stageCocone (s : Cocone Y) : Cocone H where
  pt := s.pt
  ι :=
    { app := stageDesc Y B H legs hNatural hPieces s
      naturality i j h := by
        change H.map h ≫ stageDesc Y B H legs hNatural hPieces s j =
          stageDesc Y B H legs hNatural hPieces s i ≫ 𝟙 _
        rw [Category.comp_id]
        exact stageDesc_naturality Y B H legs hNatural hStep hPieces s i j h }

variable (hHC : IsColimit HC)

/-- The actual whole descender is obtained from the original stage-colimit universal property. -/
def wholeDesc (s : Cocone Y) : HC.pt ⟶ s.pt :=
  hHC.desc (stageCocone Y B H legs hNatural hStep hPieces s)

/-- Every actual whole original vertex leg retains its exact whole-descender factor equation. -/
theorem wholeDesc_fac (s : Cocone Y) (p : P) :
    wholeLeg Y B H legs hCover HC p ≫
      wholeDesc Y B H legs hNatural hStep HC hPieces hHC s = s.ι.app p := by
  change (legs (index B hCover p) ⟨p, mem_index B hCover p⟩ ≫
    HC.ι.app (index B hCover p)) ≫ _ = _
  rw [Category.assoc, wholeDesc, hHC.fac]
  exact stageDesc_fac Y B H legs hNatural hPieces s
    (index B hCover p) ⟨p, mem_index B hCover p⟩

include hCover in
/-- The two actual layers of colimit equations prove whole original descender uniqueness. -/
theorem wholeDesc_unique [IsFiltered I] (s : Cocone Y) (m : HC.pt ⟶ s.pt)
    (hm : ∀ p : P, wholeLeg Y B H legs hCover HC p ≫ m = s.ι.app p) :
    m = wholeDesc Y B H legs hNatural hStep HC hPieces hHC s := by
  apply hHC.hom_ext
  intro i
  rw [wholeDesc, hHC.fac]
  apply (hPieces i).hom_ext
  intro p
  change legs i p ≫ (HC.ι.app i ≫ m) =
    legs i p ≫ stageDesc Y B H legs hNatural hPieces s i
  rw [← Category.assoc, ← wholeLeg_eq Y B H legs hStep hCover HC p.1 i p.2,
    hm p.1, stageDesc_fac]

/-- The complete actual original whole cocone is colimit, with its full constructed UP. -/
def wholeIsColimit [IsFiltered I] :
    IsColimit (wholeCocone Y B H legs hNatural hStep hCover HC) where
  desc := wholeDesc Y B H legs hNatural hStep HC hPieces hHC
  fac := wholeDesc_fac Y B H legs hNatural hStep hCover HC hPieces hHC
  uniq := wholeDesc_unique Y B H legs hNatural hStep hCover HC hPieces hHC

end CategoryTheory.SmallObject.InitialCoverColimitGlue
