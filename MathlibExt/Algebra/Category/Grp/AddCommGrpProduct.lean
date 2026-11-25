/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Tactic.CategoryTheory.Elementwise

/-!
# Products of abelian groups

A categorical product of an abelian-group family is isomorphic to the
pointwise product over the same index type. Projection, evaluation and
element formulas describe both directions for finite or infinite families.
-/

@[expose] public section

open CategoryTheory Limits

universe w u

namespace AddCommGrpCat

variable {J : Type w} (f : J → AddCommGrpCat.{max w u})

/-- The categorical product of a family of abelian groups agrees with the
concrete pointwise product. General-index analogue of `biproductIsoPi`
(which requires `[Finite J]`); proved over the native
`HasLimit.productLimitCone`. -/
noncomputable def piIsoPi [HasProduct f] :
    ∏ᶜ f ≅ AddCommGrpCat.of (∀ j, f j) :=
  limit.isoLimitCone (HasLimit.productLimitCone f)

@[simp]
theorem piIsoPi_inv_comp_π [HasProduct f] (j : J) :
    (piIsoPi f).inv ≫ Pi.π f j =
      ofHom (Pi.evalAddMonoidHom (fun j => f j) j) :=
  limit.isoLimitCone_inv_π _ _

@[simp, elementwise]
theorem piIsoPi_hom_comp_eval [HasProduct f] (j : J) :
    (piIsoPi f).hom ≫ ofHom (Pi.evalAddMonoidHom (fun j => f j) j) =
      Pi.π f j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) (Discrete.mk j)

/-- Element-level inverse law: projecting the reverse image recovers the family. -/
theorem piIsoPi_inv_apply [HasProduct f]
    (y : ∀ j, ↥(f j)) (j : J) :
    (Pi.π f j) ((piIsoPi f).inv y) = y j := by
  have h := ConcreteCategory.congr_hom (piIsoPi_inv_comp_π f j) y
  simpa only [CategoryTheory.comp_apply, AddCommGrpCat.hom_ofHom,
    Pi.evalAddMonoidHom_apply] using h


section UniverseLift

universe x

/-- Universe lifting commutes with a dependent family, with independent index and carrier sizes. -/
noncomputable def uliftPiIso {I : Type w} (A : I → AddCommGrpCat.{u}) :
    uliftFunctor.{x, max w u}.obj (AddCommGrpCat.of (∀ i : I, A i)) ≅
      AddCommGrpCat.of (∀ i : I, uliftFunctor.{x, u}.obj (A i)) :=
  ((AddEquiv.ulift : ULift.{x, max w u} (∀ i : I, A i) ≃+ (∀ i : I, A i)).trans
    (AddEquiv.piCongrRight fun i =>
      (AddEquiv.ulift : ULift.{x, u} (A i) ≃+ A i).symm)).toAddCommGrpIso

/-- The forward comparison retains each family component. -/
lemma uliftPiIso_hom_up {I : Type w} (A : I → AddCommGrpCat.{u})
    (a : ∀ i : I, A i) (i : I) :
    (uliftPiIso.{w, u, x} A).hom (ULift.up a) i = ULift.up (a i) := rfl

/-- The inverse comparison removes the lift component by component. -/
lemma uliftPiIso_inv_apply {I : Type w} (A : I → AddCommGrpCat.{u})
    (a : ∀ i : I, ULift.{x, u} (A i)) :
    (uliftPiIso.{w, u, x} A).inv a = ULift.up (fun i : I => (a i).down) := rfl

/-- Coefficient maps commute with the same component comparison. -/
lemma uliftPiIso_hom_naturality {I : Type w} {A B : I → AddCommGrpCat.{u}}
    (f : ∀ i : I, A i ⟶ B i) (a : ∀ i : I, A i) (i : I) :
    (uliftPiIso.{w, u, x} B).hom (ULift.up (fun j : I => f j (a j))) i =
      (uliftFunctor.{x, u}.map (f i)) ((uliftPiIso.{w, u, x} A).hom (ULift.up a) i) := rfl

end UniverseLift


section DiscreteDiagram

/-- A discrete diagram limit has its full dependent family as the product coordinates. -/
noncomputable def discreteLimitIsoPi {I : Type w}
    (F : Discrete I ⥤ AddCommGrpCat.{max w u}) :
    limit F ≅ AddCommGrpCat.of (∀ i : I, F.obj ⟨i⟩) :=
  (Pi.isoLimit F).symm ≪≫ piIsoPi (fun i : I => F.obj ⟨i⟩)

/-- The diagram comparison retains every limit projection. -/
@[reassoc]
lemma discreteLimitIsoPi_hom_eval {I : Type w}
    (F : Discrete I ⥤ AddCommGrpCat.{max w u}) (i : I) :
    (discreteLimitIsoPi F).hom ≫
        ofHom (Pi.evalAddMonoidHom (fun j : I => F.obj ⟨j⟩) i) = limit.π F ⟨i⟩ := by
  let f : I → AddCommGrpCat.{max w u} := fun j => F.obj ⟨j⟩
  let e : (∏ᶜ f : AddCommGrpCat.{max w u}) ≅ AddCommGrpCat.of (∀ j : I, f j) := piIsoPi f
  let p : AddCommGrpCat.of (∀ j : I, f j) ⟶ f i :=
    ofHom (Pi.evalAddMonoidHom (fun j : I => f j) i)
  have he : e.hom ≫ p = Pi.π f i := piIsoPi_hom_comp_eval f i
  change ((Pi.isoLimit F).inv ≫ e.hom) ≫ p = limit.π F ⟨i⟩
  exact (Category.assoc (Pi.isoLimit F).inv e.hom p).trans
    ((congrArg (fun a : (∏ᶜ f : AddCommGrpCat.{max w u}) ⟶ f i =>
      (Pi.isoLimit F).inv ≫ a) he).trans (Pi.isoLimit_inv_π F i))

/-- The inverse recovers the same component from a full dependent family. -/
@[reassoc]
lemma discreteLimitIsoPi_inv_π {I : Type w}
    (F : Discrete I ⥤ AddCommGrpCat.{max w u}) (i : I) :
    (discreteLimitIsoPi F).inv ≫ limit.π F ⟨i⟩ =
      ofHom (Pi.evalAddMonoidHom (fun j : I => F.obj ⟨j⟩) i) := by
  rw [← discreteLimitIsoPi_hom_eval, Iso.inv_hom_id_assoc]

end DiscreteDiagram

end AddCommGrpCat
