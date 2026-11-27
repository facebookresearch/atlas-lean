/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.CategoryTheory.Monoidal.IntExtension
import MathlibExt.CategoryTheory.Monoidal.RelCat
import Mathlib.Algebra.Category.FGModuleCat.Basic

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory
noncomputable section
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
  [RightRigidCategory D]
variable (T : SymmetricTrace C) (F : C ⥤ D) [F.Braided]
  (hF : T.Preserves (symmetricTraceOfRigid D) F)
example : (IntConstruction.extend T F hF).Braided := inferInstance
example : IntConstruction.embedding T ⋙ IntConstruction.extend T F hF ≅ F :=
  IntConstruction.extensionIso T F hF


open IntConstruction Functor.LaxMonoidal Functor.OplaxMonoidal

-- The source is arbitrary traced; only the target has right duals.
example : (extend T F hF).Monoidal := inferInstance
example : NatTrans.IsMonoidal (extensionIso T F hF).hom := inferInstance
example : NatTrans.IsMonoidal (extensionIso T F hF).inv := inferInstance
example (X : IntConstruction T) :
    (extend T F hF).obj X ≅ F.obj X.positive ⊗ (F.obj X.negative)ᘁ :=
  extendObjIso T F hF X
example (A U : C) :
    (extend T F hF).obj ⟨A, U⟩ ≅ F.obj A ⊗ (F.obj U)ᘁ := extendObjIso T F hF _

-- Both factorization directions and the conjugation formula work for arbitrary maps.
example (A : C) : (extend T F hF).obj ((embedding T).obj A) ≅ F.obj A :=
  (extensionIso T F hF).app A
example {A B : C} (f : A ⟶ B) :
    (extend T F hF).map ((embedding T).map f) ≫ (extensionIso T F hF).hom.app B =
      (extensionIso T F hF).hom.app A ≫ F.map f :=
  (extensionIso T F hF).hom.naturality f
example {A B : C} (f : A ⟶ B) :
    (extensionIso T F hF).inv.app A ≫ (extend T F hF).map ((embedding T).map f) ≫
      (extensionIso T F hF).hom.app B = F.map f := NatIso.naturality_1 (extensionIso T F hF) f

example (A B : C) :
    μ (embedding T ⋙ extend T F hF) A B ≫ (extensionIso T F hF).hom.app (A ⊗ B) =
      ((extensionIso T F hF).hom.app A ⊗ₘ (extensionIso T F hF).hom.app B) ≫ μ F A B :=
  NatTrans.IsMonoidal.tensor A B
example : ε (embedding T ⋙ extend T F hF) ≫ (extensionIso T F hF).hom.app (𝟙_ C) = ε F :=
  NatTrans.IsMonoidal.unit
example (X Y : IntConstruction T) :
    μ (extend T F hF) X Y ≫ (extend T F hF).map (β_ X Y).hom =
      (β_ _ _).hom ≫ μ (extend T F hF) Y X := Functor.LaxBraided.braided X Y
example {X Y U : IntConstruction T} (f : X ⊗ U ⟶ Y ⊗ U) :
    (extend T F hF).map ((symmetricTraceOfRigid (IntConstruction T)).trace f) =
      (symmetricTraceOfRigid D).trace
        (μ (extend T F hF) X U ≫ (extend T F hF).map f ≫ δ (extend T F hF) Y U) :=
  extend_preserves_trace T F hF f

-- An arbitrary supplied trace on the rigid target can be normalized by uniqueness.
example (S : SymmetricTrace D) (h : T.Preserves S F) :
    ∃ K : IntConstruction T ⥤ D, Nonempty (embedding T ⋙ K ≅ F) := by
  have hc : T.Preserves (symmetricTraceOfRigid D) F := by
    rw [← Subsingleton.elim S (symmetricTraceOfRigid D)]
    exact h
  exact ⟨extend T F hc, ⟨extensionIso T F hc⟩⟩

-- Concrete identity-target specializations recover nonzero morphisms as well as empty ones.
private def relExtension : IntConstruction RelCat.symmetricTrace.{0} ⥤ RelCat.{0} := extend RelCat.symmetricTrace.{0} (𝟭 RelCat.{0})
  (SymmetricTrace.preserves_of_rigid (𝟭 RelCat.{0}))
private def relFactorization : embedding RelCat.symmetricTrace.{0} ⋙ relExtension ≅ 𝟭 RelCat.{0} :=
  extensionIso RelCat.symmetricTrace.{0} (𝟭 RelCat.{0})
    (SymmetricTrace.preserves_of_rigid (𝟭 RelCat.{0}))

example (A B : RelCat.{0}) : relExtension.obj (⟨A, B⟩ : IntConstruction RelCat.symmetricTrace.{0}) ≅ A ⊗ B :=
  extendObjIso RelCat.symmetricTrace.{0} (𝟭 RelCat.{0}) (SymmetricTrace.preserves_of_rigid (𝟭 RelCat.{0})) _
example {A B : RelCat.{0}} (r : A ⟶ B) :
    relFactorization.inv.app A ≫ relExtension.map (X := (embedding RelCat.symmetricTrace.{0}).obj A)
      (Y := (embedding RelCat.symmetricTrace.{0}).obj B) ((embedding RelCat.symmetricTrace.{0}).map r) ≫
      relFactorization.hom.app B = r := NatIso.naturality_1 relFactorization r
example (A B : RelCat.{0}) :
    (relFactorization.inv.app A ≫ relExtension.map
      (X := (embedding RelCat.symmetricTrace.{0}).obj A)
      (Y := (embedding RelCat.symmetricTrace.{0}).obj B)
      ((embedding RelCat.symmetricTrace.{0}).map (RelCat.Hom.ofRel ∅ : A ⟶ B)) ≫
        relFactorization.hom.app B).rel = ∅ := by
  exact congrArg RelCat.Hom.rel (NatIso.naturality_1 relFactorization (RelCat.Hom.ofRel ∅ : A ⟶ B))

private abbrev linearTrace := symmetricTraceOfRigid (FGModuleCat ℚ)
private abbrev linearFactorization := extensionIso linearTrace (𝟭 (FGModuleCat ℚ))
  linearTrace.preserves_id
example (A : FGModuleCat ℚ) :
    linearFactorization.inv.app A ≫
      (extend linearTrace (𝟭 (FGModuleCat ℚ)) linearTrace.preserves_id).map
        ((embedding linearTrace).map ((2 : ℚ) • 𝟙 A)) ≫ linearFactorization.hom.app A =
      (2 : ℚ) • 𝟙 A := NatIso.naturality_1 linearFactorization ((2 : ℚ) • 𝟙 A)
