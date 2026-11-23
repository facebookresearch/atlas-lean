/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatConstantNaturality
public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.CGWHBaseHomology
public import MathlibExt.Algebra.Homology.Functor
public import
  MathlibExt.AlgebraicTopology.PlusConstruction.HomologyCandidate
public import MathlibExt.AlgebraicTopology.SingularHomology.CGWH
public import
  Mathlib.AlgebraicTopology.SimplicialSet.Homology.MapHomologicalComplex
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Ordinary integral consequence of local-coefficient homology equivalence

The constant-system naturality square first shows that an integral local-
coefficient homology equivalence induces an isomorphism on ordinary singular
homology valued in `ModuleCat ℤ`.  Forgetting the module structure and using
the canonical homology comparison identifies this with the existing
`AddCommGrp`-valued integral singular homology map.

Only the forward implication is proved.  There is no converse, fiber
acyclicity, local-coefficient Whitehead theorem, plus recognition, or
plus-construction claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe w u

namespace AlgebraicTopology

/-- Integral coefficients as a `ℤ`-module in the universe of the space. -/
abbrev singularIntegralModuleCoefficients : ModuleCat.{u} ℤ :=
  ModuleCat.of ℤ (ULift.{u} ℤ)

/-- Forget the `ℤ`-module structure while retaining the same universe. -/
abbrev forgetIntegralModule :
    ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} :=
  forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}

/-- The singular chain complex with universe-polymorphic integral module
coefficients. -/
abbrev singularIntegralModuleChainComplex (X : TopCat.{u}) :
    ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor
    (ModuleCat.{u} ℤ)).obj singularIntegralModuleCoefficients.{u}).obj X

/-- After forgetting its module structure, the integral-module singular
chain complex is canonically the existing integral singular chain complex. -/
noncomputable def moduleIntegralChainIso (X : TopCat.{u}) :
    (forgetIntegralModule.{u}.mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
        (singularIntegralModuleChainComplex X) ≅
      AlgebraicTopology.singularIntegralChainFunctor.obj X :=
  (SSet.chainComplexFunctorObjCompMapIso.{u}
    forgetIntegralModule.{u} singularIntegralModuleCoefficients.{u}).app
      (TopCat.toSSet.obj X)

/-- Forgetting the integral-module structure on singular homology is
naturally isomorphic to the existing `AddCommGrp`-valued integral singular
homology functor on simplicial sets. -/
noncomputable def moduleIntegralHomologyNatIso (n : ℕ) :
    ((SSet.chainComplexFunctor.{u, u, u + 1}
        (ModuleCat.{u} ℤ)).obj singularIntegralModuleCoefficients.{u} ⋙
      HomologicalComplex.homologyFunctor
        (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) n) ⋙
        forgetIntegralModule.{u} ≅
    (SSet.chainComplexFunctor.{u, u, u + 1} AddCommGrpCat.{u}).obj
        (forgetIntegralModule.{u}.obj
          singularIntegralModuleCoefficients.{u}) ⋙
      HomologicalComplex.homologyFunctor
        AddCommGrpCat.{u} (ComplexShape.down ℕ) n :=
  calc
    _ ≅ (SSet.chainComplexFunctor.{u, u, u + 1}
          (ModuleCat.{u} ℤ)).obj singularIntegralModuleCoefficients.{u} ⋙
        (HomologicalComplex.homologyFunctor
          (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) n ⋙
            forgetIntegralModule.{u}) :=
      Functor.associator _ _ _
    _ ≅ (SSet.chainComplexFunctor.{u, u, u + 1}
          (ModuleCat.{u} ℤ)).obj singularIntegralModuleCoefficients.{u} ⋙
        (forgetIntegralModule.{u}.mapHomologicalComplex
            (ComplexShape.down ℕ) ⋙
          HomologicalComplex.homologyFunctor
            AddCommGrpCat.{u} (ComplexShape.down ℕ) n) :=
      Functor.isoWhiskerLeft _
        (HomologicalComplex.mapHomologyFunctorIso
          (c := ComplexShape.down ℕ) n forgetIntegralModule.{u}).symm
    _ ≅ ((SSet.chainComplexFunctor.{u, u, u + 1}
          (ModuleCat.{u} ℤ)).obj singularIntegralModuleCoefficients.{u} ⋙
        forgetIntegralModule.{u}.mapHomologicalComplex
          (ComplexShape.down ℕ)) ⋙
        HomologicalComplex.homologyFunctor
          AddCommGrpCat.{u} (ComplexShape.down ℕ) n :=
      (Functor.associator _ _ _).symm
    _ ≅ _ :=
      Functor.isoWhiskerRight
        (SSet.chainComplexFunctorObjCompMapIso.{u}
          forgetIntegralModule.{u}
          singularIntegralModuleCoefficients.{u})
        (HomologicalComplex.homologyFunctor
          AddCommGrpCat.{u} (ComplexShape.down ℕ) n)

/-- Homology of the integral-module singular complex, after forgetting
module structure, is canonically existing integral singular homology. -/
noncomputable def moduleIntegralHomologyIso
    (X : TopCat.{u}) (n : ℕ) :
    forgetIntegralModule.{u}.obj
        (((AlgebraicTopology.singularHomologyFunctor
          (ModuleCat.{u} ℤ) n).obj
            singularIntegralModuleCoefficients.{u}).obj X) ≅
      AlgebraicTopology.singularIntegralHomology n X :=
  (moduleIntegralHomologyNatIso n).app (TopCat.toSSet.obj X)

/-- The integral-module/integral-group homology comparison is natural in the
topological space. -/
theorem moduleIntegralHomologyIso_naturality
    {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    forgetIntegralModule.{u}.map
        (((AlgebraicTopology.singularHomologyFunctor
          (ModuleCat.{u} ℤ) n).obj
            singularIntegralModuleCoefficients.{u}).map f) ≫
      (moduleIntegralHomologyIso Y n).hom =
    (moduleIntegralHomologyIso X n).hom ≫
      (AlgebraicTopology.singularIntegralHomologyFunctor n).map f :=
  (moduleIntegralHomologyNatIso n).hom.naturality
    (TopCat.toSSet.map f)

end AlgebraicTopology

namespace TopCat.IsLocalCoefficientHomologyEquivalence

/-- An integral local-coefficient homology equivalence is an ordinary
integral singular homology equivalence in every degree. -/
theorem isIntegral
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (n : ℕ) :
    IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f) := by
  let M := AlgebraicTopology.singularIntegralModuleCoefficients.{u}
  let L := TopCat.constantLocalSystem (X := Y) M
  let c := TopCat.localCoefficientHomologyMap
    (TopCat.LocalSystem.constantPullbackIso f M).hom n
  let m := ((AlgebraicTopology.singularHomologyFunctor
    (ModuleCat.{u} ℤ) n).obj M).map f
  let z := (AlgebraicTopology.singularIntegralHomologyFunctor n).map f
  let _ : IsIso (TopCat.localCoefficientPullbackHomologyMap f L n) :=
    hf L n
  let _ : IsIso c := by
    change IsIso ((TopCat.localCoefficientHomologyFunctor n).map
      (TopCat.LocalSystem.constantPullbackIso f M).hom)
    infer_instance
  have hConstant := TopCat.ConstantNaturality.homologyMap f M n
  have hConstant' :
      (c ≫ (TopCat.constantLocalCoefficientHomologyIso
          (X := X) M n).hom) ≫ m =
        TopCat.localCoefficientPullbackHomologyMap f L n ≫
          (TopCat.constantLocalCoefficientHomologyIso
            (X := Y) M n).hom := by
    simpa only [Category.assoc] using hConstant.symm
  let _ : IsIso m := IsIso.of_isIso_fac_left hConstant'
  have hIntegral :=
    AlgebraicTopology.moduleIntegralHomologyIso_naturality f n
  exact IsIso.of_isIso_fac_left hIntegral.symm

end TopCat.IsLocalCoefficientHomologyEquivalence

namespace CGWH.IsLocalCoefficientHomologyEquivalence

/-- A CGWH integral local-coefficient homology equivalence is an ordinary
integral singular homology equivalence. -/
theorem isIntegral
    {X Y : CGWH.{w, u}} {f : X ⟶ Y}
    (hf : CGWH.IsLocalCoefficientHomologyEquivalence f) :
    CGWH.IsIntegralHomologyEquivalence f := by
  intro n
  change IsIso
    ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (CGWH.cgwhToTop.map f))
  exact TopCat.IsLocalCoefficientHomologyEquivalence.isIntegral hf n

end CGWH.IsLocalCoefficientHomologyEquivalence
