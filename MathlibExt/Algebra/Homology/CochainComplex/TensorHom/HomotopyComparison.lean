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
# Signed Hom–tensor comparisons on homotopy categories

Tensor and product Hom descend through homotopy in every input. The
comparison is the quotient class of the signed cochain map. Its finite
tensor-factor restriction requires only bounds and finite
categorical-projective terms on the third complex.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex

namespace CochainComplex.ModuleTensor

universe u v

variable (R : Type u) [CommRing R]

/-- The original homotopy triples, with only the first Hom input opposite. -/
abbrev HomTensorHomotopyTriples :=
  (((HomotopyCategory (ModuleCat.{v} R) (.up ℤ))ᵒᵖ ×
    HomotopyCategory (ModuleCat.{v} R) (.up ℤ)) ×
      HomotopyCategory (ModuleCat.{v} R) (.up ℤ))

/-- The native quotient applied to every original cochain input. -/
def homTensorHomotopyQuotient :
    HomTensorCoChainTriples.{u, v} R ⥤ HomTensorHomotopyTriples.{u, v} R :=
  ((HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).op.prod
      (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ))).prod
    (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ))

/-- Every native homotopy-triple map is represented by original cochain maps. -/
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

/-- The actual source T(H(P,J),U) on native homotopy-category inputs. -/
def homTensorHomotopyLeftFunctor :
    HomTensorHomotopyTriples.{u, v} R ⥤ HomotopyCategory (ModuleCat.{v} R) (.up ℤ) :=
  ((CategoryTheory.Functor.uncurry.obj
      (linearHomotopyBifunctor R (C := ModuleCat.{v} R))).prod
    (𝟭 (HomotopyCategory (ModuleCat.{v} R) (.up ℤ)))) ⋙
      CategoryTheory.Functor.uncurry.obj
        (tensorHomotopyBifunctor R : HomotopyCategory (ModuleCat.{v} R) (.up ℤ) ⥤
          HomotopyCategory (ModuleCat.{v} R) (.up ℤ) ⥤
            HomotopyCategory (ModuleCat.{v} R) (.up ℤ))

/-- The actual target H(P,T(J,U)) on native homotopy-category inputs. -/
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

/-- The source object is the native quotient of the original tensor/Hom. -/
theorem homTensorHomotopyLeftFunctor_obj (X : HomTensorHomotopyTriples.{u, v} R) :
    (homTensorHomotopyLeftFunctor R).obj X =
      (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).obj
        (complexAt R (linearComplex R X.1.1.unop.as X.1.2.as) X.2.as) := rfl

/-- The target object is the native quotient of the original Hom/tensor. -/
theorem homTensorHomotopyRightFunctor_obj (X : HomTensorHomotopyTriples.{u, v} R) :
    (homTensorHomotopyRightFunctor R).obj X =
      (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).obj
        (linearComplex R X.1.1.unop.as (complexAt R X.1.2.as X.2.as)) := rfl

/-- Every original source map retains its exact simultaneous tensor/Hom class. -/
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

/-- Every original target map retains its exact pre/postcomposition class. -/
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

/-- The natural transformation on all native homotopy classes is exactly
the quotient of the original signed comparison. -/
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

/-- On each original cochain triple, the component is the literal comparison class. -/
theorem homTensorHomotopyNatTrans_app_quotient (X : HomTensorCoChainTriples.{u, v} R) :
    (homTensorHomotopyNatTrans R).app ((homTensorHomotopyQuotient R).obj X) =
      (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map
        (homTensorComparison R X.1.1.unop X.1.2 X.2) := rfl

/-- Only the original third complex bounds and finite categorical-projective
terms qualify the homotopy-category restriction. -/
def finiteFactorHomTensorHomotopyProperty : ObjectProperty (HomTensorHomotopyTriples.{u, v} R) :=
  fun X => ∃ L N : ℤ,
    (∀ b : ℤ, b < L → IsZero (X.2.as.X b)) ∧
    (∀ b : ℤ, N < b → IsZero (X.2.as.X b)) ∧
    (∀ b : ℤ, CategoryTheory.Projective (X.2.as.X b)) ∧
    (∀ b : ℤ, Module.Finite R (X.2.as.X b))

/-- The native full subcategory retains every original homotopy map class. -/
abbrev FiniteFactorHomTensorHomotopyTriples :=
  (finiteFactorHomTensorHomotopyProperty.{u, v} R).FullSubcategory

/-- The native inclusion retains every homotopy map and forgets only the finite-U qualification. -/
abbrev finiteFactorHomTensorHomotopyInclusion :
    FiniteFactorHomTensorHomotopyTriples.{u, v} R ⥤ HomTensorHomotopyTriples.{u, v} R :=
  ObjectProperty.ι _

/-- The earned original finite-C cochain Iso makes the original homotopy
comparison component invertible. -/
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

/-- The finite-C native homotopy natural Iso is the restricted original
unrestricted signed comparison class. -/
def finiteFactorHomTensorHomotopyNatIso :
    finiteFactorHomTensorHomotopyInclusion.{u, v} R ⋙ homTensorHomotopyLeftFunctor R ≅
      finiteFactorHomTensorHomotopyInclusion.{u, v} R ⋙ homTensorHomotopyRightFunctor R := by
  let α := CategoryTheory.Functor.whiskerLeft
    (finiteFactorHomTensorHomotopyInclusion R) (homTensorHomotopyNatTrans R)
  letI : IsIso α := (NatTrans.isIso_iff_isIso_app α).2
    (fun X => homTensorHomotopyNatTrans_app_isIso R X)
  exact asIso α

/-- Its entire forward transformation remains the restricted comparison class. -/
theorem finiteFactorHomTensorHomotopyNatIso_hom :
    (finiteFactorHomTensorHomotopyNatIso.{u, v} R).hom =
      CategoryTheory.Functor.whiskerLeft
        (finiteFactorHomTensorHomotopyInclusion R) (homTensorHomotopyNatTrans R) := rfl

/-- Every forward component is the quotient of the literal original map. -/
theorem finiteFactorHomTensorHomotopyNatIso_hom_app
    (X : FiniteFactorHomTensorHomotopyTriples.{u, v} R) :
    (finiteFactorHomTensorHomotopyNatIso R).hom.app X =
      (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map
        (homTensorComparison R X.obj.1.1.unop.as X.obj.1.2.as X.obj.2.as) := rfl

end CochainComplex.ModuleTensor
