/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedTensorConstructions
public import MathlibExt.AlgebraicTopology.ModelCategory.BrownSourceFunctor
public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.CategoryTheory.LiftingProperties.PushoutProduct

/-!
# The actual internal Hom derived with the original Q and R

The original pushout-product/WFS proves the genuine precomposition trivial
fibration for a trivial cofibration and fibrant target in any closed monoidal
model. The existing contravariant Brown theorem gives its weak invariance
between cofibrant sources. These source results and right Quillen invariance
construct the two-variable derived internal Hom `Hom(QX, RY)` with all maps.

Source: Hovey, *Model Categories*, Remark 4.2.3 and Proposition 4.3.1.
No cartesian tensor, unit cofibrancy or arbitrary-endpoint flatness is used.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory MorphismProperty Functor Opposite
open scoped MonoidalCategory MonoidalClosed

namespace HomotopicalAlgebra.DerivedTensorConstructions

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]

local notation "Ho" => MorphismProperty.Localization (weakEquivalences C)
local notation "π" => MorphismProperty.Q (weakEquivalences C)

/-- The actual internal-Hom precomposition map is a trivial fibration from the original PP/WFS. -/
theorem pre_trivialFibration {A B Z : C} (i : A ⟶ B)
    [Cofibration i] [WeakEquivalence i] [IsFibrant Z] :
    trivialFibrations C ((MonoidalClosed.pre i).app Z) := by
  rw [← cofibrations_rlp C]
  intro K L j hj
  apply (MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_mk_isTerminal_iff
    (f := i) (g := j) terminalIsTerminal).mp
  exact hasLiftingProperty_of_wfs _ _
    (IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left
      i j (mem_trivialCofibrations i) hj) (mem_fibrations (terminal.from Z))

/-- Original internal-Hom precomposition preserves a weak arrow between both actual cofibrant
sources. -/
theorem pre_weak {A B Z : C} (i : A ⟶ B)
    [WeakEquivalence i] [IsCofibrant A] [IsCofibrant B] [IsFibrant Z] :
    WeakEquivalence ((MonoidalClosed.pre i).app Z) := by
  let F := (MonoidalClosed.internalHom (C := C)).flip.obj Z
  apply sourceFunctor_weak_of_trivialCofibrations F ?_ i
  intro X Y j hC hW
  exact (weakEquivalence_iff _).mpr (pre_trivialFibration j).2

/-- The original fixed-source internal Hom preserves weak arrows between actual fibrant targets. -/
theorem ihom_map_weak (A : C) [IsCofibrant A] {Y Y' : C} (g : Y ⟶ Y')
    [WeakEquivalence g] [IsFibrant Y] [IsFibrant Y'] :
    WeakEquivalence ((ihom A).map g) := by
  let _ : (ihom.adjunction A).IsQuillenAdjunction :=
    (IsClosedSymmetricMonoidalModelCategory.pushoutProductAxiom
        (C := C)).ihomAdjunction_isQuillenAdjunction A
  exact Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := ihom.adjunction A) g

omit [SymmetricCategory C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The original replaced internal-Hom bifunctor retains the actual cofibrant source and fibrant
target. -/
def replacedHom (d : GeneratedFunctorialReplacements.Data (C := C)) : Cᵒᵖ ⥤ C ⥤ C :=
  d.Q.op ⋙ MonoidalClosed.internalHom ⋙ (whiskeringLeft C C C).obj d.R

omit [SymmetricCategory C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The raw original derived internal Hom uses the same canonical projection and both original
replacements. -/
def rawHom (d : GeneratedFunctorialReplacements.Data (C := C)) : Cᵒᵖ ⥤ C ⥤ Ho :=
  replacedHom d ⋙ (whiskeringRight C C Ho).obj π

omit [SymmetricCategory C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- Its object is the same actual `Hom(QX, RY)`. -/
theorem rawHom_obj (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y : C) :
    ((rawHom d).obj (op X)).obj Y = (π).obj ((ihom (d.Q.obj X)).obj (d.R.obj Y)) := rfl

omit [SymmetricCategory C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- Every original contravariant source map retains the actual Q-map precomposition. -/
theorem rawHom_map_source (d : GeneratedFunctorialReplacements.Data (C := C))
    {X X' : C} (f : X ⟶ X') (Y : C) :
    ((rawHom d).map f.op).app Y = (π).map ((MonoidalClosed.pre (d.Q.map f)).app (d.R.obj Y)) := rfl

omit [SymmetricCategory C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- Every original target map retains the actual R-map postcomposition. -/
theorem rawHom_map_target (d : GeneratedFunctorialReplacements.Data (C := C))
    (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    ((rawHom d).obj (op X)).map g = (π).map ((ihom (d.Q.obj X)).map (d.R.map g)) := rfl

/-- Both variables invert the original weak maps from the actual Q/R source preservation and proved
Hom invariance. -/
theorem rawHom_inverts (d : GeneratedFunctorialReplacements.Data (C := C)) :
    MorphismProperty.IsInvertedBy₂ (weakEquivalences C).op (weakEquivalences C) (rawHom d) := by
  rintro ⟨X, Y⟩ ⟨X', Y'⟩ ⟨f, g⟩ ⟨hf, hg⟩
  let _ : IsCofibrant (d.Q.obj X.unop) := d.q_cofibrant _
  let _ : IsCofibrant (d.Q.obj X'.unop) := d.q_cofibrant _
  let _ : IsFibrant (d.R.obj Y) := d.r_fibrant _
  let _ : IsFibrant (d.R.obj Y') := d.r_fibrant _
  let _ : WeakEquivalence (d.Q.map f.unop) := (weakEquivalence_iff _).mpr (d.q_map_weak f.unop hf)
  let _ : WeakEquivalence (d.R.map g) := (weakEquivalence_iff _).mpr (d.r_map_weak g hg)
  let _ : WeakEquivalence ((MonoidalClosed.pre (d.Q.map f.unop)).app (d.R.obj Y)) := pre_weak _
  let _ : WeakEquivalence ((ihom (d.Q.obj X'.unop)).map (d.R.map g)) := ihom_map_weak _ _
  change IsIso ((π).map ((MonoidalClosed.pre (d.Q.map f.unop)).app (d.R.obj Y)) ≫
    (π).map ((ihom (d.Q.obj X'.unop)).map (d.R.map g)))
  rw [← (π).map_comp]
  exact Localization.inverts (π) (weakEquivalences C) _ WeakEquivalence.mem

/-- The actual full internal-Hom bifunctor on the original homotopy categories. -/
def derivedInternalHom (d : GeneratedFunctorialReplacements.Data (C := C)) : Hoᵒᵖ ⥤ Ho ⥤ Ho :=
  Localization.lift₂ (rawHom d) (rawHom_inverts d) (π).op π

instance homLifting (d : GeneratedFunctorialReplacements.Data (C := C)) :
    Localization.Lifting₂ (π).op π (weakEquivalences C).op (weakEquivalences C)
      (rawHom d) (derivedInternalHom d) :=
  inferInstanceAs (Localization.Lifting₂ _ _ _ _ _
    (Localization.lift₂ (rawHom d) (rawHom_inverts d) (π).op π))

/-- The whole original Q/R internal-Hom calculation is a natural isomorphism of both variables. -/
def homProjectionIso (d : GeneratedFunctorialReplacements.Data (C := C)) :
    (((whiskeringLeft₂ Ho).obj (π).op).obj π).obj (derivedInternalHom d) ≅ rawHom d :=
  Localization.Lifting₂.iso (π).op π (weakEquivalences C).op (weakEquivalences C)
    (rawHom d) (derivedInternalHom d)

/-- The actual represented object comparison retains both original replacements. -/
def homComparison (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y : C) :
    ((derivedInternalHom d).obj (op ((π).obj X))).obj ((π).obj Y) ≅
      (π).obj ((ihom (d.Q.obj X)).obj (d.R.obj Y)) :=
  ((evaluation C Ho).obj Y).mapIso ((homProjectionIso d).app (op X))

/-- Every original contravariant source arrow preserves the complete derived Hom comparison. -/
theorem homComparison_naturality_source (d : GeneratedFunctorialReplacements.Data (C := C))
    {X X' : C} (f : X ⟶ X') (Y : C) :
    ((derivedInternalHom d).map ((π).map f).op).app ((π).obj Y) ≫ (homComparison d X Y).hom =
      (homComparison d X' Y).hom ≫ (π).map ((MonoidalClosed.pre (d.Q.map f)).app (d.R.obj Y)) :=
  congrArg (fun t => t.app Y) ((homProjectionIso d).hom.naturality f.op)

/-- Every original target arrow preserves the same actual derived Hom comparison. -/
theorem homComparison_naturality_target (d : GeneratedFunctorialReplacements.Data (C := C))
    (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    ((derivedInternalHom d).obj (op ((π).obj X))).map ((π).map g) ≫ (homComparison d X Y').hom =
      (homComparison d X Y).hom ≫ (π).map ((ihom (d.Q.obj X)).map (d.R.map g)) :=
  ((homProjectionIso d).hom.app (op X)).naturality g

omit [SymmetricCategory C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The same two actual replacement maps give the ordinary-to-derived internal-Hom computation. -/
def cofibrantFibrantHomMap (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y : C) :
    (π).obj ((ihom X).obj Y) ⟶ (π).obj ((ihom (d.Q.obj X)).obj (d.R.obj Y)) :=
  (π).map ((MonoidalClosed.pre (d.q.app X)).app Y ≫ (ihom (d.Q.obj X)).map (d.r.app Y))

/-- Both original source and target replacement maps are valid at their actual cofibrant/fibrant
endpoints. -/
theorem cofibrantFibrantHomMap_isIso (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y : C) [IsCofibrant X] [IsFibrant Y] : IsIso (cofibrantFibrantHomMap d X Y) := by
  let _ : IsCofibrant (d.Q.obj X) := d.q_cofibrant X
  let _ : IsFibrant (d.R.obj Y) := d.r_fibrant Y
  let qX : d.Q.obj X ⟶ X := d.q.app X
  let rY : Y ⟶ d.R.obj Y := d.r.app Y
  let _ : WeakEquivalence qX := (weakEquivalence_iff _).mpr (d.q_trivialFibration X).2
  let _ : WeakEquivalence rY := (weakEquivalence_iff _).mpr (d.r_trivialCofibration Y).2
  let _ : WeakEquivalence ((MonoidalClosed.pre qX).app Y) := pre_weak qX
  let _ : WeakEquivalence ((ihom (d.Q.obj X)).map rY) := ihom_map_weak _ _
  exact Localization.inverts (π) (weakEquivalences C) _ WeakEquivalence.mem

/-- Ordinary internal Hom on the same cofibrant source and fibrant target computes the actual
derived Hom. -/
def cofibrantFibrantHomComparison (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y : C) [IsCofibrant X] [IsFibrant Y] :
    ((derivedInternalHom d).obj (op ((π).obj X))).obj ((π).obj Y) ≅ (π).obj ((ihom X).obj Y) := by
  let _ : IsIso (cofibrantFibrantHomMap d X Y) := cofibrantFibrantHomMap_isIso d X Y
  exact homComparison d X Y ≪≫ (asIso (cofibrantFibrantHomMap d X Y)).symm

end HomotopicalAlgebra.DerivedTensorConstructions
