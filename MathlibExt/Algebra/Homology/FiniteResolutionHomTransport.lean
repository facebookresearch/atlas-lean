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
# Transport of augmented finite-resolution maps

Let P be preadditive, A abelian and i : P → A additive. Finite-resolution data is determined by
the resolving complex, augmentation and support bound, and an augmented comparison is determined
by its chain map.

An additive source functor F with jF ≅ i transports the resolving complex and each comparison
map. An additive homology-preserving target functor H with Hi ≅ j transports augmentations while
retaining the resolving maps. These transports preserve identities and composition and commute
with one another under the combined compatibility isomorphism.
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

/-- Let P be preadditive, A abelian and i : P → A additive. A finite resolution R of X∈A consists of
a nonnegative resolving complex in P, an augmentation i(R) → X[0] that is a quasi-isomorphism,
and an inclusive support bound. Two finite resolutions of the same X are equal if their
resolving complexes, augmentations and recorded support bounds agree. -/
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

/-- Let P,Q be preadditive, A,B abelian, and i : P → A, j : Q → A, k : Q → B additive. Let F : P → Q
and H : A → B be additive, H homology-preserving, with jF ≅ i and Hj ≅ k. Changing a finite
resolution first by F and then by H yields the same resolution as changing its target through
the composed compatibility and then its source by F. The complex, augmentation and support bound
agree. -/
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

/-- Let P be preadditive, A abelian and i : P → A additive. A finite resolution R of X∈A consists of
a nonnegative resolving complex in P, an augmentation i(R) → X[0] that is a quasi-isomorphism,
and an inclusive support bound. For finite resolutions R₁,R₂ and a fixed base map f : X₁ → X₂,
two augmented comparisons are equal when their resolving chain maps are equal. -/
@[ext]
theorem ext (φ ψ : Hom R₁ R₂ f) (hmap : φ.map = ψ.map) : φ = ψ := by
  cases φ
  cases ψ
  cases hmap
  rfl

/-- Let P be preadditive, A abelian and i : P → A additive. A finite resolution R of X∈A consists of
a nonnegative resolving complex in P, an augmentation i(R) → X[0] that is a quasi-isomorphism,
and an inclusive support bound. After identifying the source resolutions, target resolutions and
base maps, equal resolving chain maps identify the corresponding augmented comparisons,
including their augmentation squares. -/
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

/-- Let P be preadditive, A abelian and i : P → A additive. A finite resolution R of X∈A consists of
a nonnegative resolving complex in P, an augmentation i(R) → X[0] that is a quasi-isomorphism,
and an inclusive support bound. Let Q be preadditive, j : Q → A additive and F : P → Q additive
with j ∘ F ≅ i. Applying F to an augmented comparison R₁ → R₂ over f produces an augmented
comparison of the source-changed resolutions over the same f, using the compatibility jF ≅ i. -/
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

/-- Let P be preadditive, A abelian and i : P → A additive. A finite resolution R of X∈A consists of
a nonnegative resolving complex in P, an augmentation i(R) → X[0] that is a quasi-isomorphism,
and an inclusive support bound. Let Q be preadditive, j : Q → A additive and F : P → Q additive
with j ∘ F ≅ i. The entire resolving chain map of the source-changed comparison is F applied
degreewise to the original chain map. -/
theorem mapSource_map (φ : Hom R₁ R₂ f) :
    (φ.mapSource F e).map =
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ.map :=
  rfl

/-- Let P be preadditive, A abelian and i : P → A additive. A finite resolution R of X∈A consists of
a nonnegative resolving complex in P, an augmentation i(R) → X[0] that is a quasi-isomorphism,
and an inclusive support bound. Let Q be preadditive, j : Q → A additive and F : P → Q additive
with j ∘ F ≅ i. In resolution degree n ∈ ℕ, the source-changed comparison component is F(φₙ). -/
theorem mapSource_map_f (φ : Hom R₁ R₂ f) (n : ℕ) :
    (φ.mapSource F e).map.f n = F.map (φ.map.f n) :=
  rfl

/-- Let P be preadditive, A abelian and i : P → A additive. A finite resolution R of X∈A consists of
a nonnegative resolving complex in P, an augmentation i(R) → X[0] that is a quasi-isomorphism,
and an inclusive support bound. Let Q be preadditive, j : Q → A additive and F : P → Q additive
with j ∘ F ≅ i. Source change sends the identity augmented comparison of R to the identity of
its F-image resolution. -/
theorem mapSource_id (R : FiniteResolution i X₁) :
    (Hom.id R).mapSource F e = Hom.id (R.mapSource F e) := by
  apply ext
  exact (F.mapHomologicalComplex (ComplexShape.down ℕ)).map_id R.complex

/-- Let P be preadditive, A abelian and i : P → A additive. A finite resolution R of X∈A consists of
a nonnegative resolving complex in P, an augmentation i(R) → X[0] that is a quasi-isomorphism,
and an inclusive support bound. Let Q be preadditive, j : Q → A additive and F : P → Q additive
with j ∘ F ≅ i. Source change sends a composite of augmented comparisons to the composite of
their F-image comparisons. -/
theorem mapSource_comp (φ : Hom R₁ R₂ f) (ψ : Hom R₂ R₃ g) :
    (φ.comp ψ).mapSource F e = (φ.mapSource F e).comp (ψ.mapSource F e) := by
  apply ext
  exact (F.mapHomologicalComplex (ComplexShape.down ℕ)).map_comp φ.map ψ.map

end SourceChange

section TargetChange

variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable {j : P ⥤ B} [j.Additive]
variable (H : A ⥤ B) [H.Additive] [H.PreservesHomology] (e : i ⋙ H ≅ j)

/-- Let P be preadditive, A abelian and i : P → A additive. A finite resolution R of X∈A consists of
a nonnegative resolving complex in P, an augmentation i(R) → X[0] that is a quasi-isomorphism,
and an inclusive support bound. Let B be abelian, j : P → B additive and H : A → B additive and
homology-preserving with H ∘ i ≅ j. An augmented comparison over f becomes a comparison over
H(f) between the target-changed resolutions. Its resolving chain map in P remains the original
one. -/
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

/-- Let P be preadditive, A abelian and i : P → A additive. A finite resolution R of X∈A consists of
a nonnegative resolving complex in P, an augmentation i(R) → X[0] that is a quasi-isomorphism,
and an inclusive support bound. Let B be abelian, j : P → B additive and H : A → B additive and
homology-preserving with H ∘ i ≅ j. The resolving chain map of the target-changed comparison is
exactly the original comparison chain map in P. -/
theorem mapTarget_map (φ : Hom R₁ R₂ f) : (φ.mapTarget H e).map = φ.map :=
  rfl

/-- Let P be preadditive, A abelian and i : P → A additive. A finite resolution R of X∈A consists of
a nonnegative resolving complex in P, an augmentation i(R) → X[0] that is a quasi-isomorphism,
and an inclusive support bound. Let B be abelian, j : P → B additive and H : A → B additive and
homology-preserving with H ∘ i ≅ j. Every resolution-degree component of an augmented comparison
is unchanged in P under target change. -/
theorem mapTarget_map_f (φ : Hom R₁ R₂ f) (n : ℕ) :
    (φ.mapTarget H e).map.f n = φ.map.f n :=
  rfl

/-- Let P be preadditive, A abelian and i : P → A additive. A finite resolution R of X∈A consists of
a nonnegative resolving complex in P, an augmentation i(R) → X[0] that is a quasi-isomorphism,
and an inclusive support bound. Let B be abelian, j : P → B additive and H : A → B additive and
homology-preserving with H ∘ i ≅ j. Target change sends the identity comparison to the identity
comparison, after identifying H(id_X)=id_{H(X)}. -/
theorem mapTarget_id (R : FiniteResolution i X₁) :
    HEq ((Hom.id R).mapTarget H e) (Hom.id (R.mapTarget H e)) :=
  hext _ _ rfl rfl (H.map_id X₁) HEq.rfl

/-- Let P be preadditive, A abelian and i : P → A additive. A finite resolution R of X∈A consists of
a nonnegative resolving complex in P, an augmentation i(R) → X[0] that is a quasi-isomorphism,
and an inclusive support bound. Let B be abelian, j : P → B additive and H : A → B additive and
homology-preserving with H ∘ i ≅ j. Target change sends a composite comparison to the composite
of the target-changed comparisons, after identifying H(g ∘ f)=H(g) ∘ H(f). -/
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

/-- Let P,Q be preadditive, A,B abelian, and i : P → A, j : Q → A, k : Q → B additive. Let F : P → Q
and H : A → B be additive, H homology-preserving, with jF ≅ i and Hj ≅ k. The source-first and
target-first transports of an augmented comparison agree after the canonical identification of
their finite resolutions and base maps. -/
theorem mapSourceTarget (φ : Hom R₁ R₂ f) :
    HEq ((φ.mapSource F eF).mapTarget H eH)
      ((φ.mapTarget H (sourceTargetCompatibility F H eF eH)).mapSource F
        (Iso.refl (F ⋙ k))) :=
  hext _ _ (mapSourceTarget_eq F H eF eH R₁)
    (mapSourceTarget_eq F H eF eH R₂) rfl HEq.rfl

/-- Let P,Q be preadditive, A,B abelian, and i : P → A, j : Q → A, k : Q → B additive. Let F : P → Q
and H : A → B be additive, H homology-preserving, with jF ≅ i and Hj ≅ k. The two transport
orders have the same resolving chain map, namely the degreewise F-image of the original
comparison map. -/
theorem mapSourceTarget_map (φ : Hom R₁ R₂ f) :
    ((φ.mapSource F eF).mapTarget H eH).map =
      ((φ.mapTarget H (sourceTargetCompatibility F H eF eH)).mapSource F
        (Iso.refl (F ⋙ k))).map :=
  rfl

end Interchange

end Hom

end CategoryTheory.Abelian.FiniteResolution

end
