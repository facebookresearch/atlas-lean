/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: @toskua
-/

import MathlibExt.Algebra.Category.Grp.ExactnessTransport
import Batteries.Tactic.Lint
import Lean

set_option autoImplicit false
noncomputable section
universe v

open CategoryTheory

namespace MathlibExtTest.GrpExactnessTransport

variable {A₁ A₂ A₃ B₁ B₂ B₃ : GrpCat.{v}}
  (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂) (e₃ : A₃ ≅ B₃)
  (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (f' : B₁ ⟶ B₂) (g' : B₂ ⟶ B₃)
  (h₁ : f ≫ e₂.hom = e₁.hom ≫ f') (h₂ : g ≫ e₃.hom = e₂.hom ≫ g')

example (hexact : Function.MulExact f'.hom g'.hom) :
    Function.MulExact f.hom g.hom :=
  GrpCat.mulExact_of_iso_ladder e₁ e₂ e₃ f g f' g' h₁ h₂ hexact

example (hexact : Function.MulExact f'.hom g'.hom) (x : A₂) :
    g.hom x = 1 ↔ ∃ z : A₁, f.hom z = x :=
  GrpCat.mulExact_of_iso_ladder e₁ e₂ e₃ f g f' g' h₁ h₂ hexact x

example (hexact : Function.MulExact f.hom g.hom) :
    Function.MulExact f'.hom g'.hom := by
  have hi₁ : f' ≫ e₂.inv = e₁.inv ≫ f := by
    apply (cancel_mono e₂.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using congrArg (fun k => e₁.inv ≫ k) h₁.symm
  have hi₂ : g' ≫ e₃.inv = e₂.inv ≫ g := by
    apply (cancel_mono e₃.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using congrArg (fun k => e₂.inv ≫ k) h₂.symm
  exact GrpCat.mulExact_of_iso_ladder e₁.symm e₂.symm e₃.symm
    f' g' f g hi₁ hi₂ hexact

run_cmd do
  let env ← Lean.getEnv
  let n := ``GrpCat.mulExact_of_iso_ladder
  let info ← match env.find? n with
    | some i => pure i
    | none => throwError "missing public group exactness transport"
  let moduleIndex ← match env.getModuleIdx? `MathlibExt.Algebra.Category.Grp.ExactnessTransport with
    | some i => pure i
    | none => throwError "missing canonical group exactness module"
  unless env.getModuleIdxFor? n == some moduleIndex do
    throwError "group exactness transport has wrong source module"
  if info.isUnsafe then throwError "unsafe group exactness transport"
  for ax in (← Lean.collectAxioms n) do
    unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
      throwError "unexpected axiom {ax} in group exactness transport"

#lint only unusedArguments in MathlibExt.Algebra.Category.Grp.ExactnessTransport

end MathlibExtTest.GrpExactnessTransport

universe uC vC

namespace MathlibExtTest.OriginalGroupAdapters

example
    {C : Type uC} [Category.{vC} C] {F G : C ⥤ GrpCat.{v}}
    (e : F ≅ G) {X Y : C} (f : X ⟶ Y) (b : G.obj X) (x : F.obj Y)
    (hb : (G.map f).hom b = (e.hom.app Y).hom x) :
    ∃ y : F.obj X, (F.map f).hom y = x :=
  CategoryTheory.originalGroupNatIso_image e f b x hb

example
    {A B C : GrpCat.{v}} (f : A ⟶ B) (e : B ⟶ C) [IsIso e] (x : A) :
    (f ≫ e).hom x = 1 ↔ f.hom x = 1 :=
  CategoryTheory.originalGroupMap_kernel_post_iso f e x

example
    {A B C D : GrpCat.{v}}
    (r : A ⟶ B) (L R : B ⟶ C) (ρ : A ⟶ D) (s : D ⟶ C) (b : A ⟶ C)
    [IsIso L] [IsIso R] (hL : r ≫ L = ρ ≫ s) (hR : r ≫ R = b) (x : A) :
    s.hom (ρ.hom x) = 1 ↔ b.hom x = 1 :=
  CategoryTheory.originalGroupMap_double_collapse_kernel r L R ρ s b hL hR x

example
    {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : GrpCat.{v}}
    (f₁ : A₁ ⟶ A₂) (f₂ : A₂ ⟶ A₃) (f₃ : A₃ ⟶ A₄) (f₄ : A₄ ⟶ A₅)
    (g₁ : B₁ ⟶ B₂) (g₂ : B₂ ⟶ B₃) (g₃ : B₃ ⟶ B₄) (g₄ : B₄ ⟶ B₅)
    (a₁ : A₁ ⟶ B₁) (a₂ : A₂ ⟶ B₂) (a₃ : A₃ ⟶ B₃)
    (a₄ : A₄ ⟶ B₄) (a₅ : A₅ ⟶ B₅)
    (h₁ : a₁ ≫ g₁ = f₁ ≫ a₂) (h₂ : a₂ ≫ g₂ = f₂ ≫ a₃)
    (h₃ : a₃ ≫ g₃ = f₃ ≫ a₄) (h₄ : a₄ ≫ g₄ = f₄ ≫ a₅)
    (hf₁ : Function.MulExact f₁.hom f₂.hom)
    (hf₂ : Function.MulExact f₂.hom f₃.hom)
    (hf₃ : Function.MulExact f₃.hom f₄.hom)
    (hg₁ : Function.MulExact g₁.hom g₂.hom)
    (hg₂ : Function.MulExact g₂.hom g₃.hom)
    (hg₃ : Function.MulExact g₃.hom g₄.hom)
    [IsIso a₁] [IsIso a₂] [IsIso a₄] [IsIso a₅] : IsIso a₃ :=
  CategoryTheory.originalGrpCat_fiveLemma f₁ f₂ f₃ f₄ g₁ g₂ g₃ g₄ a₁ a₂ a₃ a₄ a₅ h₁ h₂ h₃ h₄ hf₁ hf₂ hf₃ hg₁ hg₂ hg₃

end MathlibExtTest.OriginalGroupAdapters
