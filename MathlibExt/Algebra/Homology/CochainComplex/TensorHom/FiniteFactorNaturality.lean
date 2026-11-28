/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.HomTensorNaturality
public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.FiniteFactorIso
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Whiskering

/-!
# Natural Hom–tensor isomorphisms with a finite projective factor

The triples `(P, J, U)` of integer module cochain complexes form a category contravariant in
`P` and covariant in `J` and `U`. The functors `Hom_R(P,J) ⊗_R U` and `Hom_R(P,J ⊗_R U)` are
joined by the signed Hom–tensor natural transformation.

Restrict to the full subcategory where the third complex `U` is bounded above and below and
has finite categorically projective terms. On this subcategory, the same comparison is a
natural isomorphism. All cochain maps between such triples are retained, with no additional
conditions on `P` or `J`.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex

namespace CochainComplex.ModuleTensor

universe u v

variable (R : Type u) [CommRing R]

/-- Category of three cochain inputs with Hom source contravariance.

The category is the product of the opposite cochain-complex category in the first input with
the cochain-complex categories in the second and third inputs. A morphism reverses the `P`
direction and preserves the directions of `J` and `U`. -/
abbrev HomTensorCoChainTriples :=
  ((CochainComplex (ModuleCat.{v} R) ℤ)ᵒᵖ ×
    CochainComplex (ModuleCat.{v} R) ℤ) × CochainComplex (ModuleCat.{v} R) ℤ

/-- Triple-input functor for Hom followed by tensor.

The left functor takes `(P, J, U)` to `Hom_R(P,J) ⊗_R U`, with the first input contravariant
and the other two covariant. -/
def homTensorCoChainLeftFunctor :
    HomTensorCoChainTriples.{u, v} R ⥤ CochainComplex (ModuleCat.{v} R) ℤ :=
  ((CategoryTheory.Functor.uncurry.obj (linearFunctor R (ModuleCat.{v} R))).prod
      (𝟭 (CochainComplex (ModuleCat.{v} R) ℤ))) ⋙
    CategoryTheory.Functor.uncurry.obj
      (bifunctorAt R : CochainComplex (ModuleCat.{v} R) ℤ ⥤
        CochainComplex (ModuleCat.{v} R) ℤ ⥤ CochainComplex (ModuleCat.{v} R) ℤ)

/-- Triple-input functor for tensor followed by Hom.

The right functor takes `(P, J, U)` to `Hom_R(P,J ⊗_R U)` with the same input variance. -/
def homTensorCoChainRightFunctor :
    HomTensorCoChainTriples.{u, v} R ⥤ CochainComplex (ModuleCat.{v} R) ℤ := by
  let A : HomTensorCoChainTriples.{u, v} R ⥤
      (CochainComplex (ModuleCat.{v} R) ℤ)ᵒᵖ :=
    CategoryTheory.Prod.fst
        ((CochainComplex (ModuleCat.{v} R) ℤ)ᵒᵖ ×
          CochainComplex (ModuleCat.{v} R) ℤ)
        (CochainComplex (ModuleCat.{v} R) ℤ) ⋙
      CategoryTheory.Prod.fst
        (CochainComplex (ModuleCat.{v} R) ℤ)ᵒᵖ
        (CochainComplex (ModuleCat.{v} R) ℤ)
  let B : HomTensorCoChainTriples.{u, v} R ⥤
      CochainComplex (ModuleCat.{v} R) ℤ :=
    ((CategoryTheory.Prod.snd
        (CochainComplex (ModuleCat.{v} R) ℤ)ᵒᵖ
        (CochainComplex (ModuleCat.{v} R) ℤ)).prod
      (𝟭 (CochainComplex (ModuleCat.{v} R) ℤ))) ⋙
        CategoryTheory.Functor.uncurry.obj
          (bifunctorAt R : CochainComplex (ModuleCat.{v} R) ℤ ⥤
            CochainComplex (ModuleCat.{v} R) ℤ ⥤ CochainComplex (ModuleCat.{v} R) ℤ)
  exact A.prod' B ⋙ CategoryTheory.Functor.uncurry.obj
    (linearFunctor R (ModuleCat.{v} R))

/-- Object formula for the Hom-then-tensor functor.

At a triple `X`, the left functor is `complexAt R (linearComplex R X.1.1.unop X.1.2) X.2`. -/
theorem homTensorCoChainLeftFunctor_obj (X : HomTensorCoChainTriples.{u, v} R) :
    (homTensorCoChainLeftFunctor R).obj X =
      complexAt R (linearComplex R X.1.1.unop X.1.2) X.2 := rfl

/-- Object formula for the tensor-then-Hom functor.

At a triple `X`, the right functor is `linearComplex R X.1.1.unop (complexAt R X.1.2 X.2)`. -/
theorem homTensorCoChainRightFunctor_obj (X : HomTensorCoChainTriples.{u, v} R) :
    (homTensorCoChainRightFunctor R).obj X =
      linearComplex R X.1.1.unop (complexAt R X.1.2 X.2) := rfl

/-- Map formula for the Hom-then-tensor functor.

A triple morphism acts by the linear Hom map of its first two components, tensored with its
third component. -/
theorem homTensorCoChainLeftFunctor_map
    {X Y : HomTensorCoChainTriples.{u, v} R} (f : X ⟶ Y) :
    (homTensorCoChainLeftFunctor R).map f =
      mapAt R (linearComplexMap R f.1.1.unop f.1.2) f.2 := by
  change (CategoryTheory.Functor.uncurry.obj
      (bifunctorAt R : CochainComplex (ModuleCat.{v} R) ℤ ⥤
        CochainComplex (ModuleCat.{v} R) ℤ ⥤
        CochainComplex (ModuleCat.{v} R) ℤ)).map
          (X := (linearComplex R X.1.1.unop X.1.2, X.2))
          (Y := (linearComplex R Y.1.1.unop Y.1.2, Y.2))
          ((CategoryTheory.Functor.uncurry.obj
            (linearFunctor R (ModuleCat.{v} R))).map
              (X := X.1) (Y := Y.1) f.1, f.2) = _
  rw [linearFunctor_uncurry_map, mapAt_uncurry]

/-- Map formula for the tensor-then-Hom functor.

A triple morphism acts by precomposition in the first input and by the tensor map of the
second and third components in the Hom target. -/
theorem homTensorCoChainRightFunctor_map
    {X Y : HomTensorCoChainTriples.{u, v} R} (f : X ⟶ Y) :
    (homTensorCoChainRightFunctor R).map f =
      linearComplexMap R f.1.1.unop (mapAt R f.1.2 f.2) := by
  change (CategoryTheory.Functor.uncurry.obj
      (linearFunctor R (ModuleCat.{v} R))).map
        (X := (X.1.1, complexAt R X.1.2 X.2))
        (Y := (Y.1.1, complexAt R Y.1.2 Y.2))
        (f.1.1, (CategoryTheory.Functor.uncurry.obj
          (bifunctorAt R : CochainComplex (ModuleCat.{v} R) ℤ ⥤
            CochainComplex (ModuleCat.{v} R) ℤ ⥤
            CochainComplex (ModuleCat.{v} R) ℤ)).map
              (X := (X.1.2, X.2)) (Y := (Y.1.2, Y.2)) (f.1.2, f.2)) = _
  rw [linearFunctor_uncurry_map, mapAt_uncurry]

/-- Signed Hom–tensor comparison as a triple-input natural transformation.

The maps `homTensorComparison R P J U` form a natural transformation from the Hom-then-tensor
functor to the tensor-then-Hom functor. -/
def homTensorCoChainNatTrans :
    homTensorCoChainLeftFunctor.{u, v} R ⟶ homTensorCoChainRightFunctor.{u, v} R where
  app X := homTensorComparison R X.1.1.unop X.1.2 X.2
  naturality X Y f := by
    rw [homTensorCoChainLeftFunctor_map, homTensorCoChainRightFunctor_map]
    exact homTensorComparison_naturality R f.1.1.unop f.1.2 f.2

/-- Third-factor boundedness and finite projectivity property.

A triple has this property if there are integer bounds below and above which its third complex
vanishes, and every term of that complex is finite and categorically projective. -/
def finiteFactorHomTensorCoChainProperty : ObjectProperty (HomTensorCoChainTriples.{u, v} R) :=
  fun X => ∃ L N : ℤ,
    (∀ b : ℤ, b < L → IsZero (X.2.X b)) ∧
    (∀ b : ℤ, N < b → IsZero (X.2.X b)) ∧
    (∀ b : ℤ, CategoryTheory.Projective (X.2.X b)) ∧
    (∀ b : ℤ, Module.Finite R (X.2.X b))

/-- Full subcategory of triples with a bounded finite projective third factor.

Restrict the category of cochain triples by `finiteFactorHomTensorCoChainProperty`, leaving
the first and second complexes unrestricted. -/
abbrev FiniteFactorHomTensorCoChainTriples :=
  (finiteFactorHomTensorCoChainProperty.{u, v} R).FullSubcategory

/-- Inclusion of bounded finite-factor cochain triples.

The full-subcategory inclusion retains the cochain triples and all morphisms between objects
whose third factor is bounded with finite projective terms. -/
abbrev finiteFactorHomTensorCoChainInclusion :
    FiniteFactorHomTensorCoChainTriples.{u, v} R ⥤ HomTensorCoChainTriples.{u, v} R :=
  ObjectProperty.ι _

/-- Signed comparison is invertible on each bounded finite-factor triple.

At every object of the restricted triple category, the signed Hom–tensor natural
transformation has an isomorphism as its component. -/
theorem homTensorCoChainNatTrans_app_isIso
    (X : FiniteFactorHomTensorCoChainTriples.{u, v} R) :
    IsIso ((homTensorCoChainNatTrans R).app X.obj) := by
  obtain ⟨L, N, hUlo, hUhi, hProj, hFinite⟩ := X.property
  let : ∀ b : ℤ, CategoryTheory.Projective (X.obj.2.X b) := hProj
  let : ∀ b : ℤ, Module.Finite R (X.obj.2.X b) := hFinite
  change IsIso (homTensorComparison R X.obj.1.1.unop X.obj.1.2 X.obj.2)
  rw [← finiteFactorHomTensorIso_hom R X.obj.1.1.unop X.obj.1.2 X.obj.2
    L N hUlo hUhi]
  infer_instance

/-- Natural Hom–tensor isomorphism on bounded finite-factor triples.

The signed comparison restricts to a natural isomorphism between the two Hom–tensor functors
on triples with bounded finite projective third factor. -/
def finiteFactorHomTensorCoChainNatIso :
    finiteFactorHomTensorCoChainInclusion.{u, v} R ⋙ homTensorCoChainLeftFunctor R ≅
      finiteFactorHomTensorCoChainInclusion.{u, v} R ⋙ homTensorCoChainRightFunctor R := by
  let α := CategoryTheory.Functor.whiskerLeft
    (finiteFactorHomTensorCoChainInclusion R) (homTensorCoChainNatTrans R)
  letI : IsIso α := (NatTrans.isIso_iff_isIso_app α).2
    (fun X => homTensorCoChainNatTrans_app_isIso R X)
  exact asIso α

/-- Restricted natural isomorphism retains the signed comparison transformation.

Its forward natural transformation is the signed comparison whiskered by the full-subcategory
inclusion. -/
theorem finiteFactorHomTensorCoChainNatIso_hom :
    (finiteFactorHomTensorCoChainNatIso.{u, v} R).hom =
      CategoryTheory.Functor.whiskerLeft
        (finiteFactorHomTensorCoChainInclusion R) (homTensorCoChainNatTrans R) := rfl

/-- Restricted natural isomorphism has the signed cochain map as each component.

At a restricted triple `X`, the forward component is `homTensorComparison R X.obj.1.1.unop
X.obj.1.2 X.obj.2`. -/
theorem finiteFactorHomTensorCoChainNatIso_hom_app
    (X : FiniteFactorHomTensorCoChainTriples.{u, v} R) :
    (finiteFactorHomTensorCoChainNatIso R).hom.app X =
      homTensorComparison R X.obj.1.1.unop X.obj.1.2 X.obj.2 := rfl

end CochainComplex.ModuleTensor
