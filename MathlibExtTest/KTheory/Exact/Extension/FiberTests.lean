/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Exact.Extension.Fiber

/-!
# Ordinary clients of the full fixed-target groupoid and fiber comparison

The clients cover every given X with independent object and Hom universes,
both correspondence directions, every raw representative, all comparison
formulas, literal target identities, naturality, and the equivalence triangle.
-/

noncomputable section

open CategoryTheory CategoryTheory.ExactCategory Limits AlgebraicKTheory

universe u v

namespace WeibelFixedTargetGroupoidTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
  (X : C)

example : FixedTargetExtension C X ≌
    Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C) :=
  FixedTargetExtension.fiberEquivalence X

example : Groupoid.{v} (FixedTargetExtension C X) := inferInstance

example : Groupoid
    (Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)) :=
  FixedTargetExtension.actualFiberGroupoid X

example (E : FixedTargetExtension C X) :
    ((FixedTargetExtension.fiberInclusion X).obj E).val.row.X₁ = E.A ∧
    ((FixedTargetExtension.fiberInclusion X).obj E).val.row.X₂ = E.B ∧
    ((FixedTargetExtension.fiberInclusion X).obj E).val.row.X₃ = X ∧
    ((FixedTargetExtension.fiberInclusion X).obj E).val.row.f = E.i ∧
    ((FixedTargetExtension.fiberInclusion X).obj E).val.row.g = E.p :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

example {E' E : FixedTargetExtension C X} (f : E' ⟶ E) :
    (FixedTargetExtension.inclusionDiagram f).alpha = f.a.inv ∧
    (FixedTargetExtension.inclusionDiagram f).beta = f.b.hom ∧
    (FixedTargetExtension.inclusionDiagram f).D = X ∧
    (FixedTargetExtension.inclusionDiagram f).q = E'.p ∧
    (FixedTargetExtension.inclusionDiagram f).lambda = 𝟙 X ∧
    (FixedTargetExtension.inclusionDiagram f).mu = 𝟙 X ∧
    (FixedTargetExtension.inclusionDiagram f).j = f.a.inv ≫ E'.i :=
  FixedTargetExtension.inclusionDiagram_fields f

example {E' E : FixedTargetExtension C X} (f : E' ⟶ E) :
    Functor.IsHomLift (ExtensionCategory.target (C := C)) (𝟙 (⟨X⟩ : QuillenQ C))
      (ExtensionCategory.mkHom (FixedTargetExtension.inclusionDiagram f)) :=
  FixedTargetExtension.inclusion_lift f

example {E' E : FixedTargetExtension C X} : (E' ⟶ E) ≃
    ((FixedTargetExtension.fiberInclusion X).obj E' ⟶
      (FixedTargetExtension.fiberInclusion X).obj E) :=
  FixedTargetExtension.homEquiv E' E

example
    {s t : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)}
    (f : s ⟶ t) (d : ExtensionDiagram s.val t.val)
    (hd : ExtensionCategory.mkHom d = f.val) :
    ((FixedTargetExtension.fromFiber X).map f).a.inv = d.alpha ∧
    ((FixedTargetExtension.fromFiber X).map f).b.hom = d.beta :=
  FixedTargetExtension.fromFiber_map_components f d hd

example
    (s : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)) :
    (FixedTargetExtension.fromFiberObj s).A = s.val.row.X₁ ∧
    (FixedTargetExtension.fromFiberObj s).B = s.val.row.X₂ ∧
    (FixedTargetExtension.fromFiberObj s).i = s.val.row.f ∧
    (FixedTargetExtension.fromFiberObj s).p =
      s.val.row.g ≫ eqToHom (congrArg QuillenQ.obj s.property) :=
  ⟨FixedTargetExtension.fromFiberObj_A s, FixedTargetExtension.fromFiberObj_B s,
    FixedTargetExtension.fromFiberObj_i s, FixedTargetExtension.fromFiberObj_p s⟩

example {E' E : FixedTargetExtension C X}
    (f : (FixedTargetExtension.fiberInclusion X).obj E' ⟶
      (FixedTargetExtension.fiberInclusion X).obj E)
    (d : ExtensionDiagram E'.toExtension E.toExtension)
    (hd : ExtensionCategory.mkHom d = f.val) :
    ExtensionDiagram.Rel d
      (FixedTargetExtension.inclusionDiagram (FixedTargetExtension.homFromFiber f)) :=
  FixedTargetExtension.representative_relation f d hd

example (E : FixedTargetExtension C X) :
    (FixedTargetExtension.unitApp E).hom.a = Iso.refl E.A ∧
    (FixedTargetExtension.unitApp E).hom.b = Iso.refl E.B ∧
    (FixedTargetExtension.unitApp E).inv.a = Iso.refl E.A ∧
    (FixedTargetExtension.unitApp E).inv.b = Iso.refl E.B :=
  ⟨rfl, rfl, rfl, rfl⟩

example
    (s : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)) :
    (FixedTargetExtension.counitDiagram s).alpha = 𝟙 s.val.row.X₁ ∧
    (FixedTargetExtension.counitDiagram s).beta = 𝟙 s.val.row.X₂ ∧
    (FixedTargetExtension.counitDiagram s).D = s.val.row.X₃ ∧
    (FixedTargetExtension.counitDiagram s).j = s.val.row.f ∧
    (FixedTargetExtension.counitDiagram s).q = s.val.row.g ∧
    (FixedTargetExtension.counitDiagram s).lambda =
      eqToHom (congrArg QuillenQ.obj s.property) ∧
    (FixedTargetExtension.counitDiagram s).mu = 𝟙 s.val.row.X₃ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

example
    (s : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)) :
    (FixedTargetExtension.counitApp s).hom.val =
      ExtensionCategory.mkHom (FixedTargetExtension.counitDiagram s) ∧
    (FixedTargetExtension.counitApp s).inv.val =
      ExtensionCategory.mkHom (FixedTargetExtension.counitInverseDiagram s) :=
  ⟨FixedTargetExtension.counitApp_hom_val s, FixedTargetExtension.counitApp_inv_val s⟩

example
    (s : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)) :
    Functor.IsHomLift (ExtensionCategory.target (C := C)) (𝟙 (⟨X⟩ : QuillenQ C))
      (ExtensionCategory.mkHom (FixedTargetExtension.counitDiagram s)) ∧
    Functor.IsHomLift (ExtensionCategory.target (C := C)) (𝟙 (⟨X⟩ : QuillenQ C))
      (ExtensionCategory.mkHom (FixedTargetExtension.counitInverseDiagram s)) :=
  ⟨FixedTargetExtension.counit_lift s, FixedTargetExtension.counitInverse_lift s⟩

example {E' E : FixedTargetExtension C X} (f : E' ⟶ E) :
    f ≫ (FixedTargetExtension.fiberUnit X).hom.app E =
      (FixedTargetExtension.fiberUnit X).hom.app E' ≫
        (FixedTargetExtension.fromFiber X).map ((FixedTargetExtension.fiberInclusion X).map f) :=
  (FixedTargetExtension.fiberUnit X).hom.naturality f

example
    {s t : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)}
    (f : s ⟶ t) :
    (FixedTargetExtension.fiberInclusion X).map ((FixedTargetExtension.fromFiber X).map f) ≫
      (FixedTargetExtension.fiberCounit X).hom.app t =
      (FixedTargetExtension.fiberCounit X).hom.app s ≫ f :=
  (FixedTargetExtension.fiberCounit X).hom.naturality f

example (E : FixedTargetExtension C X) :
    (FixedTargetExtension.fiberInclusion X).map
      ((FixedTargetExtension.fiberUnit X).hom.app E) ≫
      (FixedTargetExtension.fiberCounit X).hom.app ((FixedTargetExtension.fiberInclusion X).obj E) =
        𝟙 ((FixedTargetExtension.fiberInclusion X).obj E) :=
  (FixedTargetExtension.fiberEquivalence X).functor_unitIso_comp E

end WeibelFixedTargetGroupoidTests


end
