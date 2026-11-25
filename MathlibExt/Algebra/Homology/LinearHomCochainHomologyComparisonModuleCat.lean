/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Algebra.Homology.LinearHomCochainHomologyComparison
public import MathlibExt.Algebra.Homology.LinearHomCochainEvaluation

/-!
# The Hom-cochain comparison in `ModuleCat`

This file identifies the generic canonical Hom-cochain comparison with the
closed-monoidal evaluation pairing when the ambient abelian linear category is
`ModuleCat`.  It introduces no second comparison map: the
`ModuleCat`-specialized API below is the generic comparison with the linear
structure fixed to `ModuleCat.instLinear`, so that its statement does not
depend on instance synthesis for `Linear R (ModuleCat R)` at the use site.
Over `ℤ` such synthesis selects `Linear.preadditiveIntLinear` instead, and
the resulting generic term does not compose with the `ModuleCat` evaluation
API; the specialized API does, for every `R`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct

universe u

namespace HomologicalComplex

variable (R : Type u) [CommRing R]

/-- The monoidal structure on chain complexes of `R`-modules used in this
file, installed locally so that tensor notation refers to the total-complex
tensor product. -/
noncomputable local instance linearHomComparisonChainMonoidalCategory :
    MonoidalCategory (ChainComplex (ModuleCat.{u} R) ℕ) :=
  HomologicalComplex.monoidalCategory (ModuleCat.{u} R) (ComplexShape.down ℕ)

/-- In `ModuleCat`, uncurrying the generic canonical Hom-cochain comparison
is the homology evaluation pairing, with the braiding that exchanges homology
and cohomology inputs. -/
@[simp]
public theorem linearHomCochainHomologyComparison_uncurry
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (M : ModuleCat.{u} R) (n : ℕ) :
    MonoidalClosed.uncurry (linearHomCochainHomologyComparison R K M n) =
      (β_ (K.homology n)
        (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj
          (op K)).homology n)).hom ≫
        linearHomCochainEvaluationHomology R K M n := by
  let D := (linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj (op K)
  let q := (β_ (K.homology n) (D.homology n)).hom ≫
    linearHomCochainEvaluationHomology R K M n
  let c : D.homology n ⟶ (ihom (K.homology n)).obj M := by
    with_unfolding_all
      exact linearHomCochainHomologyComparison R K M n
  let cyc : (D.sc n).leftHomologyData.K ⟶
      (ihom (K.homology n)).obj M := by
    with_unfolding_all exact linearHomCochainCyclesComparison R K M n
  let πD : (D.sc n).leftHomologyData.K ⟶ D.homology n := by
    with_unfolding_all exact D.homologyπ n
  let hπD : Epi πD := by
    with_unfolding_all
      exact Limits.epi_of_isColimit_cofork ((D.sc n).homologyIsCokernel)
  let _ : Epi πD := hπD
  have hπc : πD ≫ c = cyc := by
    with_unfolding_all
      exact linearHomCochainHomologyπ_comp_comparison R K M n
  with_unfolding_all
    change MonoidalClosed.uncurry c = q
  apply MonoidalClosed.curry_injective
  rw [MonoidalClosed.curry_uncurry]
  apply (cancel_epi πD).1
  rw [hπc]
  apply ModuleCat.hom_ext
  ext φ
  with_unfolding_all
    change linearHomCochainCycleDesc R K M n φ =
      (MonoidalClosed.curry q).hom (((D.sc n).homologyπ).hom φ)
  apply (cancel_epi (K.homologyπ n)).1
  rw [linearHomCochainCycleDesc_fac]
  apply ModuleCat.hom_ext
  ext x
  with_unfolding_all
    change ((D.iCycles n).hom φ).hom
        ((K.iCycles n).hom x) =
      q.hom (((K.homologyπ n).hom x) ⊗ₜ[R]
        πD.hom φ)
  rw [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.braiding_hom_apply]
  with_unfolding_all
    exact (linearHomCochainEvaluationHomology_π_apply R K M n φ x).symm

/-! ## The instance-stable `ModuleCat` comparison

The definitions in this section are the generic comparison and its
projective isomorphism, specialized to `ModuleCat` with the linear
structure fixed explicitly to `ModuleCat.instLinear`, together with
the corresponding characteristic factorization and naturality
theorems.  They are definitionally the generic maps and equations at
that instance; fixing the instance in the statements makes every use
elaborate to the same term, independently of instance synthesis at
the use site. -/

/-- The canonical comparison from linear Hom-cochain cohomology to the
linear dual of homology, in `ModuleCat` with the canonical linear
structure `ModuleCat.instLinear` fixed.  Unlike the generic comparison
written directly at `ModuleCat R`, this term does not depend on instance
synthesis for `Linear R (ModuleCat R)` (which over `ℤ` selects
`Linear.preadditiveIntLinear`), so it composes with the `ModuleCat`
evaluation pairing for every `R`, including `ℤ`. -/
public noncomputable def linearHomCochainHomologyComparisonModuleCat
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (M : ModuleCat.{u} R) (n : ℕ) :
    ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj
        (op K)).homology n ⟶
      ModuleCat.of R (K.homology n ⟶ M) :=
  @linearHomCochainHomologyComparison R _ (ModuleCat.{u} R) _ _
    ModuleCat.instLinear K M n

/-- The instance-stable comparison factors through cycles.  This is the
`ModuleCat`-specialized alias of
`linearHomCochainHomologyπ_comp_comparison` with `ModuleCat.instLinear`
fixed, so it applies at `ℤ` with no local linear instance. -/
@[reassoc (attr := simp)]
public theorem linearHomCochainHomologyComparisonModuleCat_homologyπ_comp
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (M : ModuleCat.{u} R) (n : ℕ) :
    ((@linearHomCochainComplexFunctor R _
          (ModuleCat.{u} R) _ _ ModuleCat.instLinear M).obj
        (op K)).homologyπ n ≫
        linearHomCochainHomologyComparisonModuleCat R K M n =
      @linearHomCochainCyclesComparison R _
        (ModuleCat.{u} R) _ _ ModuleCat.instLinear K M n := by
  exact @linearHomCochainHomologyπ_comp_comparison
    R _ (ModuleCat.{u} R) _ _ ModuleCat.instLinear K M n

/-- The instance-stable comparison is covariantly natural in the
coefficient object.  This is the `ModuleCat`-specialized alias of
`linearHomCochainHomologyComparison_naturality_coefficient` with
`ModuleCat.instLinear` fixed, so it applies at `ℤ` with no local
linear instance. -/
@[reassoc]
public theorem
    linearHomCochainHomologyComparisonModuleCat_naturality_coefficient
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {M N : ModuleCat.{u} R} (a : M ⟶ N) (n : ℕ) :
    homologyMap
          (((@linearHomCochainComplexBifunctor R _
            (ModuleCat.{u} R) _ _ ModuleCat.instLinear).map a).app (op K)) n ≫
        linearHomCochainHomologyComparisonModuleCat R K N n =
      linearHomCochainHomologyComparisonModuleCat R K M n ≫
        ((@linearYoneda R _ (ModuleCat.{u} R) _ _
          ModuleCat.instLinear).map a).app (op (K.homology n)) := by
  exact @linearHomCochainHomologyComparison_naturality_coefficient
    R _ (ModuleCat.{u} R) _ _ ModuleCat.instLinear K M N a n

/-- The instance-stable comparison is contravariantly natural in the
chain complex.  This is the `ModuleCat`-specialized alias of
`linearHomCochainHomologyComparison_naturality_chain` with
`ModuleCat.instLinear` fixed, so it applies at `ℤ` with no local
linear instance. -/
@[reassoc]
public theorem linearHomCochainHomologyComparisonModuleCat_naturality_chain
    {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L)
    (M : ModuleCat.{u} R) (n : ℕ) :
    homologyMap
          ((@linearHomCochainComplexFunctor R _
            (ModuleCat.{u} R) _ _ ModuleCat.instLinear M).map f.op) n ≫
        linearHomCochainHomologyComparisonModuleCat R K M n =
      linearHomCochainHomologyComparisonModuleCat R L M n ≫
        ModuleCat.ofHom
          (@Linear.leftComp (ModuleCat.{u} R) _ _ R _
            ModuleCat.instLinear _ _ M
            (homologyMap f n)) := by
  exact @linearHomCochainHomologyComparison_naturality_chain
    R _ (ModuleCat.{u} R) _ _ ModuleCat.instLinear K L f M n

/-- In `ModuleCat`, uncurrying the instance-stable canonical Hom-cochain
comparison is the homology evaluation pairing, with the braiding that
exchanges homology and cohomology inputs. -/
@[simp]
public theorem linearHomCochainHomologyComparisonModuleCat_uncurry
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (M : ModuleCat.{u} R) (n : ℕ) :
    MonoidalClosed.uncurry
        (linearHomCochainHomologyComparisonModuleCat R K M n) =
      (β_ (K.homology n)
        (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj
          (op K)).homology n)).hom ≫
        linearHomCochainEvaluationHomology R K M n :=
  linearHomCochainHomologyComparison_uncurry R K M n

/-- If a chain complex of `R`-modules and all its homology objects are
projective, the instance-stable canonical comparison from linear
Hom-cochain cohomology to the linear dual of homology is an isomorphism. -/
public theorem
    linearHomCochainHomologyComparisonModuleCat_isIso_of_projective_terms_and_homology
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (M : ModuleCat.{u} R) (n : ℕ)
    [∀ i, Projective (K.X i)]
    [∀ i, Projective (K.homology i)] :
    IsIso (linearHomCochainHomologyComparisonModuleCat R K M n) :=
  @linearHomCochainHomologyComparison_isIso_of_projective_terms_and_homology
    R _ (ModuleCat.{u} R) _ _ ModuleCat.instLinear K M n
    inferInstance inferInstance

/-- The universal-coefficient isomorphism in `ModuleCat` for a complex
whose terms and homology objects are projective, whose forward map is
the instance-stable canonical Hom-cochain comparison. -/
public noncomputable def
    linearHomCochainHomologyIsoOfProjectiveTermsAndHomologyModuleCat
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (M : ModuleCat.{u} R) (n : ℕ)
    [∀ i, Projective (K.X i)]
    [∀ i, Projective (K.homology i)] :
    ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj
        (op K)).homology n ≅
      ModuleCat.of R (K.homology n ⟶ M) :=
  @linearHomCochainHomologyIsoOfProjectiveTermsAndHomology
    R _ (ModuleCat.{u} R) _ _ ModuleCat.instLinear K M n
    inferInstance inferInstance

@[simp]
public theorem
    linearHomCochainHomologyIsoOfProjectiveTermsAndHomologyModuleCat_hom
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (M : ModuleCat.{u} R) (n : ℕ)
    [∀ i, Projective (K.X i)]
    [∀ i, Projective (K.homology i)] :
    (linearHomCochainHomologyIsoOfProjectiveTermsAndHomologyModuleCat
      R K M n).hom =
      linearHomCochainHomologyComparisonModuleCat R K M n :=
  rfl

end HomologicalComplex

end
