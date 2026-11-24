/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.FiniteResolutionComparison
public import MathlibExt.Algebra.Homology.FiniteResolutionSourceCoherence

/-!
# Transport of comparison maps between finite resolutions

The original `FiniteResolution.Hom` records a chain map and its augmentation square. Source change
applies the source functor to this chain map; target change retains it. Naturality of the
canonical complex comparisons proves the new augmentation squares. These transports preserve
identities and composition and agree under source/target interchange.

Every construction uses the existing finite resolutions, their complexes and augmentations, and
their unchanged inclusive support bounds.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uP vP uQ vQ uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.FiniteResolution

variable {P : Type uP} [Category.{vP} P] [Preadditive P]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {i : P ⥤ A} [i.Additive]

/--
A finite resolution is determined by its complex, augmentation, and inclusive support bound. The
remaining fields are proofs.
-/
@[ext]
theorem ext {X : A} (R S : FiniteResolution i X)
    (hcomplex : R.complex = S.complex)
    (haugmentation : HEq R.augmentation S.augmentation)
    (hbound : R.bound = S.bound) : R = S := by
  cases R
  cases S
  cases hcomplex
  cases (eq_of_heq haugmentation)
  cases hbound
  rfl

section Interchange

variable {Q : Type uQ} [Category.{vQ} Q] [Preadditive Q]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable {j : Q ⥤ A} [j.Additive] {k : Q ⥤ B} [k.Additive]
variable (F : P ⥤ Q) [F.Additive] (H : A ⥤ B) [H.Additive] [H.PreservesHomology]
variable (eF : F ⋙ j ≅ i) (eH : j ⋙ H ≅ k)

/-- The two original source/target transport programs give the same finite
resolution, including its augmentation and its exact original bound. -/
theorem mapSourceTarget_eq {X : A} (R : FiniteResolution i X) :
    (R.mapSource F eF).mapTarget H eH =
      (R.mapTarget H (sourceTargetCompatibility F H eF eH)).mapSource F
        (Iso.refl (F ⋙ k)) := by
  apply ext
  · rfl
  · exact heq_of_eq (mapSourceTarget_augmentation F H eF eH R)
  · rfl

end Interchange

namespace Hom

variable {X₁ X₂ X₃ : A}
variable {R₁ : FiniteResolution i X₁} {R₂ : FiniteResolution i X₂}
variable {R₃ : FiniteResolution i X₃}
variable {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃}

/-- An augmented comparison map is determined by its original chain map. -/
@[ext]
theorem ext (φ ψ : Hom R₁ R₂ f) (hmap : φ.map = ψ.map) : φ = ψ := by
  cases φ
  cases ψ
  cases hmap
  rfl

/-- Equality of the original resolutions, base map, and chain map identifies
comparison maps even when their dependent types use different programs. -/
theorem hext {S₁ : FiniteResolution i X₁} {S₂ : FiniteResolution i X₂}
    {f' : X₁ ⟶ X₂} (φ : Hom R₁ R₂ f) (ψ : Hom S₁ S₂ f')
    (hsource : R₁ = S₁) (htarget : R₂ = S₂) (hbase : f = f')
    (hmap : HEq φ.map ψ.map) : HEq φ ψ := by
  cases hsource
  cases htarget
  cases hbase
  exact heq_of_eq (ext φ ψ (eq_of_heq hmap))

section SourceChange

variable {Q : Type uQ} [Category.{vQ} Q] [Preadditive Q]
variable {j : Q ⥤ A} [j.Additive]
variable (F : P ⥤ Q) [F.Additive] (e : F ⋙ j ≅ i)

/--
Transport an augmented comparison map by the source functor. The new chain map is the canonical
image of the original chain map.
-/
def mapSource (φ : Hom R₁ R₂ f) : Hom (R₁.mapSource F e) (R₂.mapSource F e) f where
  map := (F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ.map
  augmentation_comm := by
    let E := Functor.mapHomologicalComplexCompIso e (ComplexShape.down ℕ)
    change
      (j.mapHomologicalComplex (ComplexShape.down ℕ)).map
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ.map) ≫
        (E.hom.app R₂.complex ≫ R₂.augmentation) =
      (E.hom.app R₁.complex ≫ R₁.augmentation) ≫ (ChainComplex.single₀ A).map f
    calc
      _ = E.hom.app R₁.complex ≫
          ((i.mapHomologicalComplex (ComplexShape.down ℕ)).map φ.map ≫
            R₂.augmentation) := by
        simpa only [CategoryTheory.Functor.comp_map, Category.assoc] using
          congrArg (fun t => t ≫ R₂.augmentation) (E.hom.naturality φ.map)
      _ = (E.hom.app R₁.complex ≫ R₁.augmentation) ≫
          (ChainComplex.single₀ A).map f := by
        simpa only [Category.assoc] using
          congrArg (fun t => E.hom.app R₁.complex ≫ t) φ.augmentation_comm

/-- The entire transported comparison chain map is the original image map. -/
theorem mapSource_map (φ : Hom R₁ R₂ f) :
    (φ.mapSource F e).map =
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ.map :=
  rfl

/-- Its degree component is the original source functor applied to the
original comparison component. -/
theorem mapSource_map_f (φ : Hom R₁ R₂ f) (n : ℕ) :
    (φ.mapSource F e).map.f n = F.map (φ.map.f n) :=
  rfl

/-- Source transport preserves the identity as an augmented comparison map. -/
theorem mapSource_id (R : FiniteResolution i X₁) :
    (Hom.id R).mapSource F e = Hom.id (R.mapSource F e) := by
  apply ext
  exact (F.mapHomologicalComplex (ComplexShape.down ℕ)).map_id R.complex

/-- Source transport preserves composition of the original augmented maps. -/
theorem mapSource_comp (φ : Hom R₁ R₂ f) (ψ : Hom R₂ R₃ g) :
    (φ.comp ψ).mapSource F e = (φ.mapSource F e).comp (ψ.mapSource F e) := by
  apply ext
  exact (F.mapHomologicalComplex (ComplexShape.down ℕ)).map_comp φ.map ψ.map

end SourceChange

section TargetChange

variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable {j : P ⥤ B} [j.Additive]
variable (H : A ⥤ B) [H.Additive] [H.PreservesHomology] (e : i ⋙ H ≅ j)

/-- Target transport retains the original comparison chain map. Its
augmentation square follows from the original square and the two canonical
comparison naturality equations. -/
def mapTarget (φ : Hom R₁ R₂ f) :
    Hom (R₁.mapTarget H e) (R₂.mapTarget H e) (H.map f) where
  map := φ.map
  augmentation_comm := by
    let E := Functor.mapHomologicalComplexCompIso e (ComplexShape.down ℕ)
    let S := HomologicalComplex.singleMapHomologicalComplex H (ComplexShape.down ℕ) 0
    let T := H.mapHomologicalComplex (ComplexShape.down ℕ)
    change
      (j.mapHomologicalComplex (ComplexShape.down ℕ)).map φ.map ≫
        (E.inv.app R₂.complex ≫ T.map R₂.augmentation ≫ S.hom.app X₂) =
      (E.inv.app R₁.complex ≫ T.map R₁.augmentation ≫ S.hom.app X₁) ≫
        (ChainComplex.single₀ B).map (H.map f)
    calc
      _ = E.inv.app R₁.complex ≫
          (T.map ((i.mapHomologicalComplex (ComplexShape.down ℕ)).map φ.map) ≫
            T.map R₂.augmentation ≫ S.hom.app X₂) := by
        simpa only [CategoryTheory.Functor.comp_map, Category.assoc] using
          congrArg (fun t => t ≫ T.map R₂.augmentation ≫ S.hom.app X₂)
            (E.inv.naturality φ.map)
      _ = E.inv.app R₁.complex ≫
          (T.map R₁.augmentation ≫ T.map ((ChainComplex.single₀ A).map f) ≫
            S.hom.app X₂) := by
        simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using
          congrArg (fun t => E.inv.app R₁.complex ≫ T.map t ≫ S.hom.app X₂)
            φ.augmentation_comm
      _ = E.inv.app R₁.complex ≫
          (T.map R₁.augmentation ≫ S.hom.app X₁ ≫
            (ChainComplex.single₀ B).map (H.map f)) := by
        simpa only [CategoryTheory.Functor.comp_map, Category.assoc] using
          congrArg (fun t => E.inv.app R₁.complex ≫ T.map R₁.augmentation ≫ t)
            (S.hom.naturality f)
      _ = (E.inv.app R₁.complex ≫ T.map R₁.augmentation ≫ S.hom.app X₁) ≫
          (ChainComplex.single₀ B).map (H.map f) := by
        simp only [Category.assoc]

/-- The whole resolving chain map is unchanged by target transport. -/
theorem mapTarget_map (φ : Hom R₁ R₂ f) : (φ.mapTarget H e).map = φ.map :=
  rfl

/-- Each original comparison component is retained by target transport. -/
theorem mapTarget_map_f (φ : Hom R₁ R₂ f) (n : ℕ) :
    (φ.mapTarget H e).map.f n = φ.map.f n :=
  rfl

/-- Target transport preserves the full identity comparison, with its base
map identified by the original functor identity law. -/
theorem mapTarget_id (R : FiniteResolution i X₁) :
    HEq ((Hom.id R).mapTarget H e) (Hom.id (R.mapTarget H e)) :=
  hext _ _ rfl rfl (H.map_id X₁) HEq.rfl

/-- Target transport preserves the full composition comparison, with its
base map identified by the original functor composition law. -/
theorem mapTarget_comp (φ : Hom R₁ R₂ f) (ψ : Hom R₂ R₃ g) :
    HEq ((φ.comp ψ).mapTarget H e)
      ((φ.mapTarget H e).comp (ψ.mapTarget H e)) :=
  hext _ _ rfl rfl (H.map_comp f g) HEq.rfl

end TargetChange

section Interchange

variable {Q : Type uQ} [Category.{vQ} Q] [Preadditive Q]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable {j : Q ⥤ A} [j.Additive] {k : Q ⥤ B} [k.Additive]
variable (F : P ⥤ Q) [F.Additive] (H : A ⥤ B) [H.Additive] [H.PreservesHomology]
variable (eF : F ⋙ j ≅ i) (eH : j ⋙ H ≅ k)

/--
The full source-first and target-first comparison programs coincide. Their resolutions are
identified by the already proved augmentation interchange, and both chain maps are the original
source-functor image.
-/
theorem mapSourceTarget (φ : Hom R₁ R₂ f) :
    HEq ((φ.mapSource F eF).mapTarget H eH)
      ((φ.mapTarget H (sourceTargetCompatibility F H eF eH)).mapSource F
        (Iso.refl (F ⋙ k))) :=
  hext _ _ (mapSourceTarget_eq F H eF eH R₁)
    (mapSourceTarget_eq F H eF eH R₂) rfl HEq.rfl

/-- Source/target interchange retains the same entire original image chain map. -/
theorem mapSourceTarget_map (φ : Hom R₁ R₂ f) :
    ((φ.mapSource F eF).mapTarget H eH).map =
      ((φ.mapTarget H (sourceTargetCompatibility F H eF eH)).mapSource F
        (Iso.refl (F ⋙ k))).map :=
  rfl

end Interchange

end Hom

end CategoryTheory.Abelian.FiniteResolution

end
