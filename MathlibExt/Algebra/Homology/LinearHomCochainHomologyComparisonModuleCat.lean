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
# Evaluation of Hom cohomology on chain homology

Let R be a commutative ring, K a nonnegative chain complex of R-modules, and M
an R-module, with the coefficient ring and module carriers in the universe u.
The cochain complex Hom_R(K; M) has degree n term Hom_R(K_n, M) and
differential φ ↦ φ ∘ d_K. A cocycle therefore induces a map from H_n(K) to M.

The comparison α_n : Hⁿ(Hom_R(K; M)) → Hom_R(H_n(K), M) is R-linear.
Its evaluation on a homology class is α_n([φ])([x]) = φ(x). It is natural
contravariantly in K and covariantly in M. When every term and every homology
module of K is projective over R, α_n is an isomorphism for every n.
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

/-- For a commutative ring R, the category of nonnegative chain complexes of
R-modules carries the total tensor product. Its degree n term is the finite
sum of K_p ⊗[R] L_q over p + q = n, with differential
d(x ⊗ y) = d_K(x) ⊗ y + (-1)^p x ⊗ d_L(y) for x of degree p. -/
noncomputable local instance linearHomComparisonChainMonoidalCategory :
    MonoidalCategory (ChainComplex (ModuleCat.{u} R) ℕ) :=
  HomologicalComplex.monoidalCategory (ModuleCat.{u} R) (ComplexShape.down ℕ)

/-- Let R be a commutative ring, K a nonnegative chain complex of R-modules,
M an R-module, and n a nonnegative integer. Uncurrying the comparison
Hⁿ(Hom_R(K; M)) → Hom_R(H_n(K), M) gives evaluation after interchanging
H_n(K) and Hⁿ(Hom_R(K; M)): on [x] ⊗ [φ] its value is φ(x).
The interchange is the module tensor braiding, with no degree-dependent sign. -/
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

/-!
# Naturality and projective comparison

The module Hom_R(H_n(K), M) has pointwise addition and R-scalar multiplication.
The comparison from Hom cohomology to this module sends a cocycle class to
its induced map on homology. It commutes with postcomposition by a coefficient
map M → N and precomposition by the homology map of a chain map K → L.

If all terms K_i and all homology modules H_i(K) are projective over R, this
comparison is invertible. The coefficient module M remains arbitrary.
-/

/-- For a commutative ring R, a nonnegative chain complex K of R-modules, an
R-module M, and n ∈ ℕ, this is the R-linear comparison
α_n : Hⁿ(Hom_R(K; M)) → Hom_R(H_n(K), M).
A cocycle φ : K_n → M vanishes on boundaries and induces
α_n([φ])([x]) = φ(x) for a cycle x ∈ K_n. -/
public noncomputable def linearHomCochainHomologyComparisonModuleCat
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (M : ModuleCat.{u} R) (n : ℕ) :
    ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj
        (op K)).homology n ⟶
      ModuleCat.of R (K.homology n ⟶ M) :=
  @linearHomCochainHomologyComparison R _ (ModuleCat.{u} R) _ _
    ModuleCat.instLinear K M n

/-- Let R be a commutative ring, K a nonnegative chain complex of R-modules,
M an R-module, and n ∈ ℕ. The composite of the projection
Zⁿ(Hom_R(K; M)) → Hⁿ(Hom_R(K; M)) with α_n equals the map obtained by
restricting each cocycle φ to Z_n(K) and factoring through H_n(K).
Thus the comparison has value [x] ↦ φ(x) already on cocycle representatives. -/
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

/-- Let R be a commutative ring, K a nonnegative chain complex of R-modules,
n ∈ ℕ, and a : M → N an R-linear coefficient map. Writing α_M and α_N for
the comparisons in degree n, α_N ∘ Hⁿ(Hom_R(K; a)) =
postcompose(a) ∘ α_M. Both maps send [φ] to the homology map [x] ↦ a(φ(x)). -/
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

/-- Let R be a commutative ring, f : K → L a map of nonnegative chain
complexes of R-modules, M an R-module, and n ∈ ℕ. The degree n comparisons
satisfy α_K ∘ Hⁿ(Hom_R(f; M)) = precompose(H_n(f)) ∘ α_L.
Here Hom_R(f; M) goes from Hom_R(L; M) to Hom_R(K; M), and the two maps
send [φ] to [x] ↦ φ(f_n(x)). -/
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

/-- For a commutative ring R, a nonnegative chain complex K of R-modules,
an R-module M, and n ∈ ℕ, uncurrying the module comparison α_n gives
H_n(K) ⊗[R] Hⁿ(Hom_R(K; M)) → M. This map is the tensor braiding followed
by cohomology–homology evaluation; it sends [x] ⊗ [φ] to φ(x). -/
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

/-- Let R be a commutative ring and K a nonnegative chain complex of
R-modules. If K_i and H_i(K) are projective over R for every i ∈ ℕ, then,
for every R-module M and every n ∈ ℕ, the comparison
Hⁿ(Hom_R(K; M)) → Hom_R(H_n(K), M) is an isomorphism. -/
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

/-- Let R be a commutative ring and K a nonnegative chain complex of
R-modules with all K_i and all H_i(K) projective over R. For any R-module M
and n ∈ ℕ, this is the isomorphism
Hⁿ(Hom_R(K; M)) ≅ Hom_R(H_n(K), M).
Its forward map sends the class of a cocycle φ to the map [x] ↦ φ(x). -/
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
