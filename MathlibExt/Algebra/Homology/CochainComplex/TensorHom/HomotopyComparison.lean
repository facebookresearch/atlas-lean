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

public import MathlibExt.Algebra.Homology.HomComplex.HomotopyFunctor
public import MathlibExt.Algebra.Homology.HomotopyCategory.TensorFunctor
public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.FiniteFactorNaturality

/-!
# Hom–tensor comparisons in homotopy categories

For integer module cochains over a commutative ring, tensor and full-product linear Hom
descend to homotopy categories. The triple category has the Hom source opposite and the Hom
target and tensor factor covariant. The signed cochain comparison gives a natural
transformation between the two induced Hom–tensor functors.

Restrict to triples whose third underlying cochain complex is bounded above and below and has
finite categorically projective terms. The comparison is then a natural isomorphism in the
homotopy category, induced by the cochain isomorphism. The first two complexes are
unrestricted.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex

namespace CochainComplex.ModuleTensor

universe u v

variable (R : Type u) [CommRing R]

/-- Category of Hom–tensor inputs in the homotopy category.

Form the triple category with the first homotopy-category factor opposite and the second and
third factors covariant, for integer cochain complexes over `R`. -/
abbrev HomTensorHomotopyTriples :=
  (((HomotopyCategory (ModuleCat.{v} R) (.up ℤ))ᵒᵖ ×
    HomotopyCategory (ModuleCat.{v} R) (.up ℤ)) ×
      HomotopyCategory (ModuleCat.{v} R) (.up ℤ))

/-- Componentwise quotient from cochain triples to homotopy triples.

Apply the homotopy-category quotient functor to all three cochain inputs, with the opposite
functor in the first input. -/
def homTensorHomotopyQuotient :
    HomTensorCoChainTriples.{u, v} R ⥤ HomTensorHomotopyTriples.{u, v} R :=
  ((HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).op.prod
      (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ))).prod
    (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ))

/-- Morphisms between quotient triples have cochain representatives.

Every morphism between the homotopy triples of two given cochain triples is the image of a
morphism between those cochain triples. -/
theorem homTensorHomotopyQuotient_map_surjective
    (X Y : HomTensorCoChainTriples.{u, v} R)
    (f : (homTensorHomotopyQuotient R).obj X ⟶
      (homTensorHomotopyQuotient R).obj Y) :
    ∃ g : X ⟶ Y, (homTensorHomotopyQuotient R).map g = f := by
  obtain ⟨a, ha⟩ :=
    (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map_surjective f.1.1.unop
  obtain ⟨b, hb⟩ :=
    (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map_surjective f.1.2
  obtain ⟨c, hc⟩ :=
    (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map_surjective f.2
  refine ⟨((a.op, b), c), ?_⟩
  apply Prod.ext
  · apply Prod.ext
    · change ((HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map a).op = f.1.1
      exact congrArg Quiver.Hom.op ha
    · exact hb
  · exact hc

/-- Hom followed by tensor as a functor on homotopy triples.

The left functor takes `(P, J, U)` to the homotopy class of `Hom_R(P,J) ⊗_R U`, using the
linear Hom and tensor homotopy bifunctors. -/
def homTensorHomotopyLeftFunctor :
    HomTensorHomotopyTriples.{u, v} R ⥤ HomotopyCategory (ModuleCat.{v} R) (.up ℤ) :=
  ((CategoryTheory.Functor.uncurry.obj
      (linearHomotopyBifunctor R (C := ModuleCat.{v} R))).prod
    (𝟭 (HomotopyCategory (ModuleCat.{v} R) (.up ℤ)))) ⋙
      CategoryTheory.Functor.uncurry.obj
        (tensorHomotopyBifunctor R : HomotopyCategory (ModuleCat.{v} R) (.up ℤ) ⥤
          HomotopyCategory (ModuleCat.{v} R) (.up ℤ) ⥤
            HomotopyCategory (ModuleCat.{v} R) (.up ℤ))

/-- Tensor followed by Hom as a functor on homotopy triples.

The right functor takes `(P, J, U)` to the homotopy class of `Hom_R(P,J ⊗_R U)` with the same
input variance. -/
def homTensorHomotopyRightFunctor :
    HomTensorHomotopyTriples.{u, v} R ⥤ HomotopyCategory (ModuleCat.{v} R) (.up ℤ) := by
  let A : HomTensorHomotopyTriples.{u, v} R ⥤
      (HomotopyCategory (ModuleCat.{v} R) (.up ℤ))ᵒᵖ :=
    CategoryTheory.Prod.fst
        ((HomotopyCategory (ModuleCat.{v} R) (.up ℤ))ᵒᵖ ×
          HomotopyCategory (ModuleCat.{v} R) (.up ℤ))
        (HomotopyCategory (ModuleCat.{v} R) (.up ℤ)) ⋙
      CategoryTheory.Prod.fst
        (HomotopyCategory (ModuleCat.{v} R) (.up ℤ))ᵒᵖ
        (HomotopyCategory (ModuleCat.{v} R) (.up ℤ))
  let B : HomTensorHomotopyTriples.{u, v} R ⥤
      HomotopyCategory (ModuleCat.{v} R) (.up ℤ) :=
    ((CategoryTheory.Prod.snd
        (HomotopyCategory (ModuleCat.{v} R) (.up ℤ))ᵒᵖ
        (HomotopyCategory (ModuleCat.{v} R) (.up ℤ))).prod
      (𝟭 (HomotopyCategory (ModuleCat.{v} R) (.up ℤ)))) ⋙
        CategoryTheory.Functor.uncurry.obj
          (tensorHomotopyBifunctor R : HomotopyCategory (ModuleCat.{v} R) (.up ℤ) ⥤
            HomotopyCategory (ModuleCat.{v} R) (.up ℤ) ⥤
              HomotopyCategory (ModuleCat.{v} R) (.up ℤ))
  exact A.prod' B ⋙ CategoryTheory.Functor.uncurry.obj
    (linearHomotopyBifunctor R (C := ModuleCat.{v} R))

/-- Object formula for Hom-then-tensor on homotopy triples.

At a homotopy triple, the left functor is the quotient of the tensor total of the linear Hom
of the first two underlying cochain complexes with the third complex. -/
theorem homTensorHomotopyLeftFunctor_obj (X : HomTensorHomotopyTriples.{u, v} R) :
    (homTensorHomotopyLeftFunctor R).obj X =
      (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).obj
        (complexAt R (linearComplex R X.1.1.unop.as X.1.2.as) X.2.as) := rfl

/-- Object formula for tensor-then-Hom on homotopy triples.

At a homotopy triple, the right functor is the quotient of the linear Hom from the first
underlying complex to the tensor total of the second and third. -/
theorem homTensorHomotopyRightFunctor_obj (X : HomTensorHomotopyTriples.{u, v} R) :
    (homTensorHomotopyRightFunctor R).obj X =
      (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).obj
        (linearComplex R X.1.1.unop.as (complexAt R X.1.2.as X.2.as)) := rfl

/-- Hom-then-tensor map on a cochain representative.

On the quotient of a cochain triple morphism, the left homotopy functor is the quotient class
of `mapAt R (linearComplexMap R f.1.1.unop f.1.2) f.2`. -/
theorem homTensorHomotopyLeftFunctor_map_original
    {X Y : HomTensorCoChainTriples.{u, v} R} (f : X ⟶ Y) :
    (homTensorHomotopyLeftFunctor R).map ((homTensorHomotopyQuotient R).map f) =
      (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map
        (mapAt R (linearComplexMap R f.1.1.unop f.1.2) f.2) := by
  let π := HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)
  let T := CategoryTheory.Functor.uncurry.obj
      (tensorHomotopyBifunctor R : HomotopyCategory (ModuleCat.{v} R) (.up ℤ) ⥤
        HomotopyCategory (ModuleCat.{v} R) (.up ℤ) ⥤
          HomotopyCategory (ModuleCat.{v} R) (.up ℤ))
  exact (congrArg
    (fun a => T.map
      (X := (π.obj (linearComplex R X.1.1.unop X.1.2), π.obj X.2))
      (Y := (π.obj (linearComplex R Y.1.1.unop Y.1.2), π.obj Y.2))
      (a, π.map f.2))
    (linearHomotopyBifunctor_uncurry_map R f.1.1.unop f.1.2)).trans
    (tensorHomotopyBifunctor_uncurry_map R (linearComplexMap R f.1.1.unop f.1.2) f.2)

/-- Tensor-then-Hom map on a cochain representative.

On the quotient of a cochain triple morphism, the right homotopy functor is the quotient class
of `linearComplexMap R f.1.1.unop (mapAt R f.1.2 f.2)`. -/
theorem homTensorHomotopyRightFunctor_map_original
    {X Y : HomTensorCoChainTriples.{u, v} R} (f : X ⟶ Y) :
    (homTensorHomotopyRightFunctor R).map ((homTensorHomotopyQuotient R).map f) =
      (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map
        (linearComplexMap R f.1.1.unop (mapAt R f.1.2 f.2)) := by
  let π := HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)
  let H := CategoryTheory.Functor.uncurry.obj
    (linearHomotopyBifunctor R (C := ModuleCat.{v} R))
  exact (congrArg
    (fun b => H.map
      (X := (Opposite.op (π.obj X.1.1.unop), π.obj (complexAt R X.1.2 X.2)))
      (Y := (Opposite.op (π.obj Y.1.1.unop), π.obj (complexAt R Y.1.2 Y.2)))
      ((π.map f.1.1.unop).op, b))
    (tensorHomotopyBifunctor_uncurry_map R f.1.2 f.2)).trans
    (linearHomotopyBifunctor_uncurry_map R f.1.1.unop (mapAt R f.1.2 f.2))

/-- Signed Hom–tensor map as a homotopy natural transformation.

The quotient classes of the signed cochain comparison form a natural transformation from the
Hom-then-tensor functor to the tensor-then-Hom functor on homotopy triples. -/
def homTensorHomotopyNatTrans :
    homTensorHomotopyLeftFunctor.{u, v} R ⟶ homTensorHomotopyRightFunctor.{u, v} R where
  app X := (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map
    (homTensorComparison R X.1.1.unop.as X.1.2.as X.2.as)
  naturality X Y f := by
    let X₀ : HomTensorCoChainTriples.{u, v} R :=
      ((Opposite.op X.1.1.unop.as, X.1.2.as), X.2.as)
    let Y₀ : HomTensorCoChainTriples.{u, v} R :=
      ((Opposite.op Y.1.1.unop.as, Y.1.2.as), Y.2.as)
    obtain ⟨f₀, hf⟩ := homTensorHomotopyQuotient_map_surjective R X₀ Y₀ f
    let π := HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)
    let a := mapAt R (linearComplexMap R f₀.1.1.unop f₀.1.2) f₀.2
    let b := linearComplexMap R f₀.1.1.unop (mapAt R f₀.1.2 f₀.2)
    let α := homTensorComparison R X.1.1.unop.as X.1.2.as X.2.as
    let β := homTensorComparison R Y.1.1.unop.as Y.1.2.as Y.2.as
    have hleft : (homTensorHomotopyLeftFunctor R).map f = π.map a :=
      (congrArg (fun k => (homTensorHomotopyLeftFunctor R).map k) hf.symm).trans
        (homTensorHomotopyLeftFunctor_map_original R f₀)
    have hright : (homTensorHomotopyRightFunctor R).map f = π.map b :=
      (congrArg (fun k => (homTensorHomotopyRightFunctor R).map k) hf.symm).trans
        (homTensorHomotopyRightFunctor_map_original R f₀)
    have hn : a ≫ β = α ≫ b :=
      homTensorComparison_naturality R f₀.1.1.unop f₀.1.2 f₀.2
    have hq : π.map a ≫ π.map β = π.map α ≫ π.map b :=
      ((π.map_comp a β).symm.trans
        (congrArg
          (fun k : complexAt R (linearComplex R X.1.1.unop.as X.1.2.as) X.2.as ⟶
              linearComplex R Y.1.1.unop.as (complexAt R Y.1.2.as Y.2.as) => π.map k)
          hn)).trans (π.map_comp α b)
    exact (congrArg (fun k => k ≫ π.map β) hleft).trans
      (hq.trans (congrArg (fun k => π.map α ≫ k) hright.symm))

/-- Homotopy comparison on a quotient cochain triple.

At the homotopy triple of a cochain triple `X`, the comparison is the quotient image of
`homTensorComparison R X.1.1.unop X.1.2 X.2`. -/
theorem homTensorHomotopyNatTrans_app_quotient (X : HomTensorCoChainTriples.{u, v} R) :
    (homTensorHomotopyNatTrans R).app ((homTensorHomotopyQuotient R).obj X) =
      (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map
        (homTensorComparison R X.1.1.unop X.1.2 X.2) := rfl

/-- Underlying third homotopy input has bounded finite projective terms.

A homotopy triple satisfies this property if its third underlying cochain complex has integer
lower and upper vanishing bounds and each term is finite and categorically projective. -/
def finiteFactorHomTensorHomotopyProperty : ObjectProperty (HomTensorHomotopyTriples.{u, v} R) :=
  fun X => ∃ L N : ℤ,
    (∀ b : ℤ, b < L → IsZero (X.2.as.X b)) ∧
    (∀ b : ℤ, N < b → IsZero (X.2.as.X b)) ∧
    (∀ b : ℤ, CategoryTheory.Projective (X.2.as.X b)) ∧
    (∀ b : ℤ, Module.Finite R (X.2.as.X b))

/-- Full subcategory of homotopy triples with a bounded finite factor.

Restrict the homotopy triple category by the bounded finite-projective property on the third
underlying cochain complex. -/
abbrev FiniteFactorHomTensorHomotopyTriples :=
  (finiteFactorHomTensorHomotopyProperty.{u, v} R).FullSubcategory

/-- Inclusion of the bounded finite-factor homotopy triples.

The full-subcategory inclusion retains all morphisms between triples with the prescribed
third-factor property. -/
abbrev finiteFactorHomTensorHomotopyInclusion :
    FiniteFactorHomTensorHomotopyTriples.{u, v} R ⥤ HomTensorHomotopyTriples.{u, v} R :=
  ObjectProperty.ι _

/-- Homotopy comparison is invertible on bounded finite-factor triples.

At a triple with bounded finite projective third factor, the homotopy natural transformation
has an isomorphism as its component. -/
theorem homTensorHomotopyNatTrans_app_isIso
    (X : FiniteFactorHomTensorHomotopyTriples.{u, v} R) :
    IsIso ((homTensorHomotopyNatTrans R).app X.obj) := by
  obtain ⟨L, N, hUlo, hUhi, hProj, hFinite⟩ := X.property
  let : ∀ b : ℤ, CategoryTheory.Projective (X.obj.2.as.X b) := hProj
  let : ∀ b : ℤ, Module.Finite R (X.obj.2.as.X b) := hFinite
  change IsIso ((HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map
    (homTensorComparison R X.obj.1.1.unop.as X.obj.1.2.as X.obj.2.as))
  let e := finiteFactorHomTensorIso R X.obj.1.1.unop.as X.obj.1.2.as X.obj.2.as
    L N hUlo hUhi
  have he : (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map e.hom =
      (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map
        (homTensorComparison R X.obj.1.1.unop.as X.obj.1.2.as X.obj.2.as) :=
    congrArg (fun a => (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map a)
      (finiteFactorHomTensorIso_hom R X.obj.1.1.unop.as X.obj.1.2.as X.obj.2.as
        L N hUlo hUhi)
  exact he ▸ (inferInstance :
    IsIso ((HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map e.hom))

/-- Natural Hom–tensor isomorphism in the bounded finite-factor homotopy subcategory.

The signed Hom–tensor natural transformation restricts to a natural isomorphism on homotopy
triples whose third underlying cochain complex is bounded with finite projective terms. -/
def finiteFactorHomTensorHomotopyNatIso :
    finiteFactorHomTensorHomotopyInclusion.{u, v} R ⋙ homTensorHomotopyLeftFunctor R ≅
      finiteFactorHomTensorHomotopyInclusion.{u, v} R ⋙ homTensorHomotopyRightFunctor R := by
  let α := CategoryTheory.Functor.whiskerLeft
    (finiteFactorHomTensorHomotopyInclusion R) (homTensorHomotopyNatTrans R)
  letI : IsIso α := (NatTrans.isIso_iff_isIso_app α).2
    (fun X => homTensorHomotopyNatTrans_app_isIso R X)
  exact asIso α

/-- Forward homotopy isomorphism is the restricted comparison.

The forward transformation of the restricted homotopy natural isomorphism is the comparison
whiskered by the full-subcategory inclusion. -/
theorem finiteFactorHomTensorHomotopyNatIso_hom :
    (finiteFactorHomTensorHomotopyNatIso.{u, v} R).hom =
      CategoryTheory.Functor.whiskerLeft
        (finiteFactorHomTensorHomotopyInclusion R) (homTensorHomotopyNatTrans R) := rfl

/-- Component of the restricted homotopy isomorphism is the signed map's class.

The forward component at a restricted triple is the quotient class of the signed cochain
comparison on its three underlying complexes. -/
theorem finiteFactorHomTensorHomotopyNatIso_hom_app
    (X : FiniteFactorHomTensorHomotopyTriples.{u, v} R) :
    (finiteFactorHomTensorHomotopyNatIso R).hom.app X =
      (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map
        (homTensorComparison R X.obj.1.1.unop.as X.obj.1.2.as X.obj.2.as) := rfl

end CochainComplex.ModuleTensor
