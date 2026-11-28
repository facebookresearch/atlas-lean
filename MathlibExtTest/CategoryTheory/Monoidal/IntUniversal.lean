/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.CategoryTheory.Monoidal.IntUniversal
import Mathlib.Algebra.Category.FGModuleCat.Basic

noncomputable section
open CategoryTheory MonoidalCategory IntConstruction
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
variable (T : SymmetricTrace C) (K L : IntConstruction T ⥤ D) [K.Braided] [L.Braided]
  (i : embedding T ⋙ K ≅ embedding T ⋙ L) [NatTrans.IsMonoidal i.hom]

-- The restriction theorem requires neither source nor target rigidity.
example : K ≅ L := restrictionLift T K L i
example : NatTrans.IsMonoidal (restrictionLift T K L i).hom := inferInstance
example : NatTrans.IsMonoidal (restrictionLift T K L i).inv := inferInstance
example (A : C) : (restrictionLift T K L i).app ((embedding T).obj A) = i.app A :=
  restrictionLift_positive T K L i A
example (A : C) : (restrictionLift T K L i).app (⟨𝟙_ C, A⟩ : IntConstruction T) =
    negativeComparison T K L i A := restrictionLift_negative T K L i A
example : Functor.isoWhiskerLeft (embedding T) (restrictionLift T K L i) = i := by simp
example (e : K ≅ L) [NatTrans.IsMonoidal e.hom]
    (h : Functor.isoWhiskerLeft (embedding T) e = i) : e = restrictionLift T K L i :=
  restrictionLift_unique T K L i e h
example : ∃! e : K ≅ L, NatTrans.IsMonoidal e.hom ∧
    Functor.isoWhiskerLeft (embedding T) e = i := existsUnique_restrictionLift T K L i

-- Arbitrary crossed maps exercise both negative endpoints.
example {A B U V : C} (f : A ⊗ V ⟶ B ⊗ U) :
    K.map (ofHom T (X := ⟨A, U⟩) (Y := ⟨B, V⟩) f) ≫
      (restrictionLift T K L i).hom.app ⟨B, V⟩ =
    (restrictionLift T K L i).hom.app ⟨A, U⟩ ≫
      L.map (ofHom T (X := ⟨A, U⟩) (Y := ⟨B, V⟩) f) :=
  (restrictionLift T K L i).hom.naturality _
example (X : IntConstruction T) :
    (restrictionLift T K L i).hom.app X ≫ (restrictionLift T K L i).inv.app X = 𝟙 _ := by simp
example (X : IntConstruction T) :
    (restrictionLift T K L i).inv.app X ≫ (restrictionLift T K L i).hom.app X = 𝟙 _ := by simp
example : ε K ≫ (restrictionLift T K L i).hom.app (𝟙_ (IntConstruction T)) = ε L :=
  NatTrans.IsMonoidal.unit
example (X Y : IntConstruction T) :
    μ K X Y ≫ (restrictionLift T K L i).hom.app (X ⊗ Y) =
      ((restrictionLift T K L i).hom.app X ⊗ₘ (restrictionLift T K L i).hom.app Y) ≫ μ L X Y :=
  NatTrans.IsMonoidal.tensor X Y
-- The negative factors reverse: (I,A) tensor (I,B) has negative object B tensor A.
example (A B : C) :
    μ K (⟨𝟙_ C, A⟩ : IntConstruction T) ⟨𝟙_ C, B⟩ ≫
      (restrictionLift T K L i).hom.app ⟨(𝟙_ C) ⊗ (𝟙_ C), B ⊗ A⟩ =
        ((negativeComparison T K L i A).hom ⊗ₘ (negativeComparison T K L i B).hom) ≫
          μ L (⟨𝟙_ C, A⟩ : IntConstruction T) ⟨𝟙_ C, B⟩ := by
  have h := NatTrans.IsMonoidal.tensor (τ := (restrictionLift T K L i).hom)
    (⟨𝟙_ C, A⟩ : IntConstruction T) (⟨𝟙_ C, B⟩ : IntConstruction T)
  simp only [← Iso.app_hom, restrictionLift_negative] at h
  exact h
example (A : C) : (mappedPositivePairing T K A).coevaluation' ≫
    (i.hom.app A ⊗ₘ (negativeComparison T K L i A).hom) =
      (mappedPositivePairing T L A).coevaluation' := negativeComparison_coevaluation T K L i A
example (A : C) : ((negativeComparison T K L i A).hom ⊗ₘ i.hom.app A) ≫
    (mappedPositivePairing T L A).evaluation' = (mappedPositivePairing T K A).evaluation' :=
  negativeComparison_evaluation T K L i A

section RigidTarget
variable [RightRigidCategory D] (F : C ⥤ D) [F.Braided]
  (hF : T.Preserves (symmetricTraceOfRigid D) F)
  (σ : embedding T ⋙ K ≅ F) [NatTrans.IsMonoidal σ.hom]
example : K ≅ extend T F hF := extensionComparison T K F hF σ
example : NatTrans.IsMonoidal (extensionComparison T K F hF σ).hom := inferInstance
example : Functor.isoWhiskerLeft (embedding T) (extensionComparison T K F hF σ) ≪≫
    extensionIso T F hF = σ := by simp
example (e : K ≅ extend T F hF) [NatTrans.IsMonoidal e.hom]
    (h : Functor.isoWhiskerLeft (embedding T) e ≪≫ extensionIso T F hF = σ) :
    e = extensionComparison T K F hF σ := extensionComparison_unique T K F hF σ e h
example : ∃! e : K ≅ extend T F hF, NatTrans.IsMonoidal e.hom ∧
    Functor.isoWhiskerLeft (embedding T) e ≪≫ extensionIso T F hF = σ :=
  existsUnique_extensionComparison T K F hF σ
example : K ≅ extend T (embedding T ⋙ K)
    (SymmetricTrace.Preserves.comp (embedding_preserves_trace T)
      (SymmetricTrace.preserves_of_rigid K)) := universalComparison T K
example : NatTrans.IsMonoidal (universalComparison T K).hom := inferInstance
end RigidTarget

-- An arbitrary traced source, with no source-dual assumptions: the target is its own Int.
example : (𝟭 (IntConstruction T)) ≅
    extend T (embedding T ⋙ 𝟭 (IntConstruction T))
      (SymmetricTrace.Preserves.comp (embedding_preserves_trace T)
        (SymmetricTrace.preserves_of_rigid (𝟭 (IntConstruction T)))) :=
  universalComparison T (𝟭 (IntConstruction T))

namespace ScalarOrientation
private abbrev trace := symmetricTraceOfRigid (FGModuleCat ℚ)
private abbrev original := (rigidEquivalence trace).inverse
private def scaled : IntConstruction trace ⥤ FGModuleCat ℚ := original
set_option backward.isDefEq.respectTransparency false in
private def scalarIso : original ≅ scaled := NatIso.ofComponents (fun X =>
  { hom := (2 : ℚ) • 𝟙 (original.obj X)
    inv := (1 / 2 : ℚ) • 𝟙 (original.obj X)
    hom_inv_id := by simp [Linear.smul_comp, Linear.comp_smul, smul_smul]
    inv_hom_id := by simp [scaled, Linear.comp_smul, smul_smul] })
  (by intro X Y f; simp [scaled, Linear.comp_smul, Linear.smul_comp])
local instance : scaled.Monoidal := Functor.Monoidal.transport scalarIso
local instance : NatTrans.IsMonoidal scalarIso.hom :=
  Functor.Monoidal.natTransIsMonoidal_of_transport scalarIso
local instance : scaled.LaxBraided := Functor.LaxBraided.ofNatIso scalarIso
local instance : scaled.Braided where
private def restricted := Functor.isoWhiskerLeft (embedding trace) scalarIso
local instance : NatTrans.IsMonoidal restricted.hom :=
  inferInstanceAs (NatTrans.IsMonoidal (Functor.whiskerLeft (embedding trace) scalarIso.hom))

-- A genuine nonidentity, noninvolutive isomorphism, with transported tensor structure.
private theorem lift_eq : restrictionLift trace original scaled restricted = scalarIso :=
  (restrictionLift_unique trace original scaled restricted scalarIso rfl).symm
example (A : FGModuleCat ℚ) :
    (restrictionLift trace original scaled restricted).hom.app ⟨𝟙_ _, A⟩ =
      (2 : ℚ) • 𝟙 (original.obj ⟨𝟙_ _, A⟩) := by rw [lift_eq]; rfl
example (A : FGModuleCat ℚ) :
    (restrictionLift trace original scaled restricted).inv.app ⟨𝟙_ _, A⟩ =
      (1 / 2 : ℚ) • 𝟙 (original.obj ⟨𝟙_ _, A⟩) := by rw [lift_eq]; rfl
end ScalarOrientation
