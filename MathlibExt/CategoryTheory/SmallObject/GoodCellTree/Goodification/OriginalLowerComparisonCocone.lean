/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits

/-!
# Actual cocones comparing refining lower diagrams with original lower pieces

The original order map and actual natural vertex comparison construct each
whole lower cocone into the same original selected lower object. Every
vertex leg and every larger-lower-set map retains its actual original
component and original selected colimit leg.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w u v

namespace CategoryTheory.SmallObject.OriginalLowerComparisonCocone

open Limits LowerSetColimits

variable {P Q : Type w} [Preorder P] [Preorder Q] {C : Type u} [Category.{v} C]
  (f : P →o Q) (F : P ⥤ C) (Y : Q ⥤ C)
  (beta : F ⟶ f.monotone.functor ⋙ Y) (L : LowerSetColimitData Y)

/-- The actual refining lower carrier is the preimage of the same original lower label set. -/
def carrier (B : LowerSet Q) : LowerSet P where
  carrier := {p | f p ∈ B}
  lower' := by
    intro b a hab hb
    exact B.lower' (f.monotone hab) hb

/-- Each actual lower-comparison leg is the original component and selected original lower leg. -/
def leg (B : LowerSet Q) (p : carrier f B) : F.obj p.1 ⟶ L.obj B :=
  beta.app p.1 ≫ L.ι B ⟨f p.1, p.2⟩

/-- Actual original naturality and lower-colimit legs prove the whole lower-comparison cocone. -/
abbrev cocone (B : LowerSet Q) : Cocone (restriction F (carrier f B)) where
  pt := L.obj B
  ι :=
    { app := leg f F Y beta L B
      naturality p q h := by
        change F.map (homOfLE (leOfHom h)) ≫
          (beta.app q.1 ≫ L.ι B ⟨f q.1, q.2⟩) =
          (beta.app p.1 ≫ L.ι B ⟨f p.1, p.2⟩) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc,
          beta.naturality (homOfLE (leOfHom h)), Category.assoc]
        have hn := (L.cocone B).w
          (homOfLE (f.monotone (leOfHom h)) : (⟨f p.1, p.2⟩ : B) ⟶ ⟨f q.1, q.2⟩)
        change Y.map (f.monotone.functor.map (homOfLE (leOfHom h))) ≫
          L.ι B ⟨f q.1, q.2⟩ = L.ι B ⟨f p.1, p.2⟩ at hn
        exact congrArg (fun m => beta.app p.1 ≫ m) hn }

/-- The actual lower comparison keeps the entire original selected point function. -/
theorem cocone_point_function : (fun B : LowerSet Q => (cocone f F Y beta L B).pt) = L.obj :=
  rfl

/-- Every full lower vertex-leg function retains the same original component and original leg. -/
theorem cocone_leg_function (B : LowerSet Q) :
    (fun p : carrier f B => (cocone f F Y beta L B).ι.app p) =
      (fun p : carrier f B => beta.app p.1 ≫ L.ι B ⟨f p.1, p.2⟩) := rfl

/-- The same original larger-lower map retains every actual lower-comparison vertex leg. -/
theorem leg_map {B D : LowerSet Q} (h : B ≤ D) (p : carrier f B) :
    leg f F Y beta L B p ≫ L.map h =
      leg f F Y beta L D ⟨p.1, h p.2⟩ := by
  change (beta.app p.1 ≫ L.ι B ⟨f p.1, p.2⟩) ≫ L.map h =
    beta.app p.1 ≫ L.ι D ⟨f p.1, h p.2⟩
  rw [Category.assoc, L.ι_map]

end CategoryTheory.SmallObject.OriginalLowerComparisonCocone
