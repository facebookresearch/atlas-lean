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

public import MathlibExt.LinearAlgebra.Quotient.IdealHom
public import MathlibExt.Algebra.Category.ModuleCat.TorsionAnnihilatorColimit
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Quotient-Hom diagrams and primary-component cocones

The quotient objects use the same module-category universe as R; the
evaluation equivalence has independent scalar and coefficient universes.
Ideal powers, linear Coyoneda and the annihilator colimit give the diagram
and its primary-component cocone.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace ModuleCat.Torsion

variable {R : Type u} [CommRing R]

/-- The actual native R/I^n object, in its valid common module world. -/
@[implicit_reducible]
def quotientPowerModule (I : Ideal R) (n : ℕ) : ModuleCat.{u} R :=
  (localCohomology.ringModIdeals (localCohomology.idealPowersDiagram I)).obj (op n)

/-- Native quotient contravariance followed by native linear Coyoneda. -/
@[implicit_reducible]
def quotientHomFamily (I : Ideal R) : ℕ ⥤ (ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
  opOp ℕ ⋙
    (localCohomology.ringModIdeals (localCohomology.idealPowersDiagram I)).op ⋙
      linearCoyoneda R (ModuleCat.{u} R)

local instance (I : Ideal R) (n : ℕ) : ((quotientHomFamily I).obj n).Additive := by
  change ((linearCoyoneda R (ModuleCat.{u} R)).obj (op (quotientPowerModule I n))).Additive
  infer_instance

/-- The same actual family, with its native additive Hom functors. -/
def quotientHomAdditiveFamily (I : Ideal R) :
    ℕ ⥤ (ModuleCat.{u} R ⥤+ ModuleCat.{u} R) where
  obj n := AdditiveFunctor.of ((quotientHomFamily I).obj n)
  map f := ⟨(quotientHomFamily I).map f⟩
  map_id n := by
    apply ObjectProperty.hom_ext
    exact (quotientHomFamily I).map_id n
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (quotientHomFamily I).map_comp f g

/-- Coefficients vary through the native flipped functor family. -/
@[implicit_reducible]
def quotientHomDiagramFunctor (I : Ideal R) :
    ModuleCat.{u} R ⥤ (ℕ ⥤ ModuleCat.{u} R) :=
  (quotientHomFamily I).flip

/-- The actual degreewise Hom diagram at a given coefficient. -/
@[implicit_reducible]
def quotientHomDiagram (I : Ideal R) (M : ModuleCat.{u} R) : ℕ ⥤ ModuleCat.{u} R :=
  (quotientHomDiagramFunctor I).obj M

/-- Native categorical Hom is classified by the actual ideal-power annihilator. -/
def quotientHomDiagramIsoAnnihilator (I : Ideal R) (M : ModuleCat.{u} R) :
    quotientHomDiagram I M ≅ annihilatorDiagram I M :=
  NatIso.ofComponents
    (fun n =>
      ((ModuleCat.homLinearEquiv (S := R) (M := quotientPowerModule I n) (N := M)).trans
        (Ideal.quotientHomEquiv (I ^ n) (M : Type u))).toModuleIso)
    (by
      intro i j f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      apply Subtype.ext
      rfl)

/-- The whole diagram comparison respects actual coefficient maps. -/
def quotientHomDiagramFunctorIsoAnnihilator (I : Ideal R) :
    quotientHomDiagramFunctor I ≅ annihilatorDiagramFunctor I :=
  NatIso.ofComponents (quotientHomDiagramIsoAnnihilator I) (by
    intro M N f
    apply NatTrans.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    rfl)

/-- Precompose the earned annihilator cocone with its actual Hom comparison. -/
def quotientHomCocone (I : Ideal R) (M : ModuleCat.{u} R) :
    Cocone (quotientHomDiagram I M) :=
  (Cocone.precompose (quotientHomDiagramIsoAnnihilator I M).hom).obj
    (annihilatorCocone I M)

/-- The cocone leg is evaluation at the original quotient one. -/
lemma quotientHomCocone_val (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ)
    (φ : quotientPowerModule I n ⟶ M) :
    (((quotientHomCocone I M).ι.app n).hom φ).val =
      φ.hom (Ideal.quotientOne (I ^ n)) := rfl

/-- Native change-of-diagram transports G5's earned universal property. -/
def quotientHomIsColimit (I : Ideal R) (M : ModuleCat.{u} R) :
    IsColimit (quotientHomCocone I M) :=
  (IsColimit.precomposeHomEquiv (quotientHomDiagramIsoAnnihilator I M)
    (annihilatorCocone I M)).symm (annihilatorIsColimit I M)

/-- The cocone intertwines the original coefficient maps and primary-component map. -/
lemma quotientHom_coefficient_naturality (I : Ideal R) {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (n : ℕ) :
    (quotientHomCocone I M).ι.app n ≫ (functor I).map f =
      ((quotientHomDiagramFunctor I).map f).app n ≫ (quotientHomCocone I N).ι.app n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  rfl

/-- The canonical cocone-point comparison, with its actual universal property. -/
def gammaIsoQuotientHomColimitObj (I : Ideal R) (M : ModuleCat.{u} R) :
    (functor I).obj M ≅ colimit (quotientHomDiagram I M) :=
  (quotientHomIsColimit I M).coconePointUniqueUpToIso
    (colimit.isColimit (quotientHomDiagram I M))

/-- Its forward map takes each evaluation leg to the native colimit inclusion. -/
lemma quotientHomCocone_comp_gammaIso_hom (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    (quotientHomCocone I M).ι.app n ≫ (gammaIsoQuotientHomColimitObj I M).hom =
      colimit.ι (quotientHomDiagram I M) n :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (quotientHomIsColimit I M) (colimit.isColimit (quotientHomDiagram I M)) n

/-- Its inverse is the same actual evaluation-at-one cocone. -/
lemma colimit_iota_comp_gammaIso_inv (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    colimit.ι (quotientHomDiagram I M) n ≫ (gammaIsoQuotientHomColimitObj I M).inv =
      (quotientHomCocone I M).ι.app n :=
  IsColimit.comp_coconePointUniqueUpToIso_inv
    (quotientHomIsColimit I M) (colimit.isColimit (quotientHomDiagram I M)) n

/-- The canonical primary-component comparison is natural in the actual coefficient. -/
def gammaIsoQuotientHomColimit (I : Ideal R) :
    (functor I : ModuleCat.{u} R ⥤ ModuleCat.{u} R) ≅ quotientHomDiagramFunctor I ⋙ colim :=
  NatIso.ofComponents (gammaIsoQuotientHomColimitObj I) (by
    intro M N f
    apply (quotientHomIsColimit I M).hom_ext
    intro n
    let iM := (quotientHomCocone I M).ι.app n
    let iN := (quotientHomCocone I N).ι.app n
    let d := ((quotientHomDiagramFunctor I).map f).app n
    let eM := gammaIsoQuotientHomColimitObj I M
    let eN := gammaIsoQuotientHomColimitObj I N
    have hM : iM ≫ eM.hom = colimit.ι (quotientHomDiagram I M) n :=
      quotientHomCocone_comp_gammaIso_hom I M n
    have hN : iN ≫ eN.hom = colimit.ι (quotientHomDiagram I N) n :=
      quotientHomCocone_comp_gammaIso_hom I N n
    have hf : iM ≫ (functor I).map f = d ≫ iN :=
      quotientHom_coefficient_naturality I f n
    have hc : colimit.ι (quotientHomDiagram I M) n ≫
        colim.map ((quotientHomDiagramFunctor I).map f) =
          d ≫ colimit.ι (quotientHomDiagram I N) n :=
      colimit.ι_map ((quotientHomDiagramFunctor I).map f) n
    calc
      iM ≫ ((functor I).map f ≫ eN.hom) = (iM ≫ (functor I).map f) ≫ eN.hom :=
        (Category.assoc _ _ _).symm
      _ = (d ≫ iN) ≫ eN.hom := congrArg (fun g => g ≫ eN.hom) hf
      _ = d ≫ (iN ≫ eN.hom) := Category.assoc _ _ _
      _ = d ≫ colimit.ι (quotientHomDiagram I N) n := congrArg (fun g => d ≫ g) hN
      _ = colimit.ι (quotientHomDiagram I M) n ≫
          colim.map ((quotientHomDiagramFunctor I).map f) := hc.symm
      _ = (iM ≫ eM.hom) ≫ colim.map ((quotientHomDiagramFunctor I).map f) :=
        congrArg (fun g => g ≫ colim.map ((quotientHomDiagramFunctor I).map f)) hM.symm
      _ = iM ≫ (eM.hom ≫ colim.map ((quotientHomDiagramFunctor I).map f)) :=
        Category.assoc _ _ _)

end ModuleCat.Torsion
