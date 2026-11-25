/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.TensorRestriction
public import MathlibExt.Algebra.Category.ModuleCat.CompatibleScalarRestriction
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Original scalar restriction of the native coefficient tensor

The S-linear coefficient-first tensor refines the original R-linear tensor
of the SAME original M with its restricted R-action.  The existing compatible
restriction identity earns this natural isomorphism.  No coefficient
replacement, flatness, Small, or carrier-size equality is assumed.

Actual scalar restriction is exact, so native homology comparison also
retains the original R-valued homology object.  These bridges let a stronger
S-linear base-change API specialize to the literal original R-AQ functor.
Native verification remains unexecuted for this source proposal.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Functor
open scoped TensorProduct

universe u w t v

namespace ModuleCat.TensorRestriction

variable (R : Type u) (S : Type w) [CommRing R] [CommRing S] [Algebra R S]
  (M : ModuleCat.{t} S)

/-- Original R-valued tensoring is recovered by the actual compatible scalar restriction. -/
def compatibleNativeNatIso :
    (functorAt R S M : ModuleCat.{v} R ⥤ ModuleCat.{max t v} S) ⋙
        ModuleCat.restrictScalars (algebraMap R S) ≅
      (ModuleCat.tensorBifunctorAt.{u, t, v} R).obj
        ((ModuleCat.restrictScalars (algebraMap R S)).obj M) :=
  NatIso.ofComponents
    (fun L => by
      letI : Module R M := restrictModule R S M
      letI : IsScalarTower R S M := restrictTower R S M
      letI : SMulCommClass R S M := restrictCommute R S M
      let MR := (ModuleCat.restrictScalars (algebraMap R S)).obj M
      letI : Module S MR := M.isModule
      letI : IsScalarTower R S MR :=
        IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
      letI : SMulCommClass R S MR := ⟨fun r s m => by
        change (algebraMap R S r) • (s • m) = s • ((algebraMap R S r) • m)
        exact smul_comm _ _ _⟩
      exact LinearEquiv.toModuleIso
        (ModuleCat.compatibleRestrictScalarsEquiv R S (MR ⊗[R] L)))
    (by
      intro L L' f
      letI : Module R M := restrictModule R S M
      letI : IsScalarTower R S M := restrictTower R S M
      letI : SMulCommClass R S M := restrictCommute R S M
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro m l
      rfl)

/-- The native scalar restriction functor is homology-preserving with no flatness premise. -/
theorem restrictScalars_preservesHomology :
    (ModuleCat.restrictScalars (algebraMap R S) :
      ModuleCat.{v} S ⥤ ModuleCat.{v} R).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro T hT
  exact ModuleCat.restrictScalars_map_exact (algebraMap R S) T hT

/-- Exact scalar restriction transports the actual homology object by the native short-complex API. -/
def restrictHomologyIso (L : ChainComplex (ModuleCat.{v} S) ℕ) (n : ℕ) :
    (((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj L).homology n ≅
        (ModuleCat.restrictScalars (algebraMap R S)).obj (L.homology n) := by
  let F : ModuleCat.{v} S ⥤ ModuleCat.{v} R :=
    ModuleCat.restrictScalars (algebraMap R S)
  letI : F.PreservesHomology := restrictScalars_preservesHomology R S
  exact (L.sc n).mapHomologyIso F

/-- The actual exact-restriction homology comparison retains native chain-map naturality. -/
@[reassoc]
theorem restrictHomologyIso_inv_naturality
    {L L' : ChainComplex (ModuleCat.{v} S) ℕ} (f : L ⟶ L') (n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap R S)).map
        (HomologicalComplex.homologyMap f n) ≫ (restrictHomologyIso R S L' n).inv =
      (restrictHomologyIso R S L n).inv ≫
        HomologicalComplex.homologyMap
          (((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex
            (ComplexShape.down ℕ)).map f) n := by
  let F : ModuleCat.{v} S ⥤ ModuleCat.{v} R :=
    ModuleCat.restrictScalars (algebraMap R S)
  letI : F.PreservesHomology := restrictScalars_preservesHomology R S
  exact ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} S) (ComplexShape.down ℕ) n).map f) F

end ModuleCat.TensorRestriction

end
