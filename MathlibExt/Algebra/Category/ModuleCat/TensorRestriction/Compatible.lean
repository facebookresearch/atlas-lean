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
# Scalar restriction of coefficient-first tensor products

Let `R : Type u` and `S : Type w` be commutative rings with `Algebra R S`, and let `M :
ModuleCat.{t} S`. The `S`-linear functor `L ↦ M ⊗_R L`, with `S` acting on the first factor,
restricts naturally to the `R`-linear tensor functor using the restricted `R`-module `M`. The
input carrier universe `v` and coefficient carrier universe `t` are independent.

Restriction of scalars preserves homology. For an `S`-module chain complex, the homology of
its restricted complex is naturally isomorphic to the restriction of its homology, with the
inverse comparison compatible with chain maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Functor
open scoped TensorProduct

universe u w t v

namespace ModuleCat.TensorRestriction

variable (R : Type u) (S : Type w) [CommRing R] [CommRing S] [Algebra R S]
  (M : ModuleCat.{t} S)

/-- Let `R : Type u`, `S : Type w` be commutative rings with `Algebra R S`, and `M : ModuleCat.{t}
S`. The `S`-linear coefficient-first tensor functor `functorAt R S M : ModuleCat.{v} R →
ModuleCat.{max t v} S`, followed by restriction along `algebraMap R S`, is naturally
isomorphic to `L ↦ (Res_R M) ⊗_R L` in `ModuleCat R`. Its components preserve the tensor
entries `m,l`. -/
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

/-- For commutative rings `R : Type u`, `S : Type w` with `Algebra R S`, the functor
`ModuleCat.restrictScalars (algebraMap R S) : ModuleCat.{v} S → ModuleCat.{v} R` preserves
homology. The ring and module-carrier universes are independent. -/
theorem restrictScalars_preservesHomology :
    (ModuleCat.restrictScalars (algebraMap R S) :
      ModuleCat.{v} S ⥤ ModuleCat.{v} R).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro T hT
  exact ModuleCat.restrictScalars_map_exact (algebraMap R S) T hT

/-- Let `R,S` be commutative rings with `Algebra R S`, `L : ChainComplex (ModuleCat.{v} S) ℕ`, and
`n : ℕ`. The canonical comparison has direction `H_n(Res_R L) ≅ Res_R(H_n L)`. Here scalar
restriction is applied to every term and differential of the chain complex. -/
def restrictHomologyIso (L : ChainComplex (ModuleCat.{v} S) ℕ) (n : ℕ) :
    (((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj L).homology n ≅
        (ModuleCat.restrictScalars (algebraMap R S)).obj (L.homology n) := by
  let F : ModuleCat.{v} S ⥤ ModuleCat.{v} R :=
    ModuleCat.restrictScalars (algebraMap R S)
  letI : F.PreservesHomology := restrictScalars_preservesHomology R S
  exact (L.sc n).mapHomologyIso F

/-- Let `R,S` be commutative rings with `Algebra R S`, `f : L → L'` a map of `ℕ`-chain complexes
of `S`-modules, and `n : ℕ`. For `e_L : H_n(Res_R L) ≅ Res_R(H_n L)`, the inverse comparisons
satisfy `Res_R(H_n f) ≫ e_{L'}⁻¹ = e_L⁻¹ ≫ H_n(Res_R f)`. -/
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
