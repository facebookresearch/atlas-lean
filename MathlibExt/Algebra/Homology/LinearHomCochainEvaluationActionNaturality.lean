/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
import MathlibExt.Algebra.Homology.ChainGradedPairingDegreeZeroActionNaturality

/-!
# Coefficient naturality of the single-complex evaluation action

Let R be commutative and all module carriers lie in universe u. Write I=R[0] for the chain
tensor unit. The right unitor of M[0] gives the degree-zero coefficient action
ρ^M_q:M⊗I_q→(M[0])_q used in Hom cochain evaluation.

For every linear map a:M→M′ and q∈ℕ, these actions satisfy ρ^M_q≫(a[0])_q=(a⊗id_{I_q})≫ρ^{M′}_q.
The degree-zero case is the module right-unit naturality square, and the positive-degree cases
have zero terms.
-/

universe u

open CategoryTheory MonoidalCategory

namespace HomologicalComplex

variable (R : Type u) [CommRing R]

/-- Let R be commutative in universe u, with all module carriers and nonnegative chain terms in u.
The monoidal category of nonnegative R-module chain complexes has unit I=R[0] and total tensor
product with vertical sign (-1)^p. Its right unitors M[0]⊗I→M[0] give the coefficient actions in
every degree. -/
noncomputable local instance linearHomCochainEvaluationActionMonoidalCategory :
    MonoidalCategory (ChainComplex (ModuleCat.{u} R) ℕ) :=
  HomologicalComplex.monoidalCategory (ModuleCat.{u} R) (ComplexShape.down ℕ)

/-- Let R be commutative in universe u, with all module carriers and nonnegative chain terms in u.
For a:M→M′ and q∈ℕ, let ρ^M_q:M⊗I_q→(M[0])_q and ρ^{M′}_q be the normalized degree-zero actions
of the right unitors, with I=R[0]. Then ρ^M_q≫(a[0])_q=(a⊗id_{I_q})≫ρ^{M′}_q. The equation
retains the specified coefficient map and the same unit-chain term. -/
@[reassoc]
public theorem linearHomCochainEvaluationAction_naturality
    {M M' : ModuleCat.{u} R} (a : M ⟶ M') (q : ℕ) :
    chainGradedPairingDegreeZeroAction R
        (rightUnitor ((ChainComplex.single₀ (ModuleCat.{u} R)).obj M)).hom
        q ≫ ((ChainComplex.single₀ (ModuleCat.{u} R)).map a).f q =
      (a ⊗ₘ 𝟙 _) ≫ chainGradedPairingDegreeZeroAction R
        (rightUnitor ((ChainComplex.single₀ (ModuleCat.{u} R)).obj M')).hom
        q := by
  simpa only [HomologicalComplex.id_f] using
    chainGradedPairingDegreeZeroAction_naturality R M M'
      (tensorUnit (ModuleCat.{u} R) (ComplexShape.down ℕ))
      (tensorUnit (ModuleCat.{u} R) (ComplexShape.down ℕ))
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj M)
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj M')
      (rightUnitor ((ChainComplex.single₀ (ModuleCat.{u} R)).obj M)).hom
      (rightUnitor ((ChainComplex.single₀ (ModuleCat.{u} R)).obj M')).hom
      a (𝟙 (tensorUnit (ModuleCat.{u} R) (ComplexShape.down ℕ)))
      ((ChainComplex.single₀ (ModuleCat.{u} R)).map a)
      (MonoidalCategory.rightUnitor_naturality
        ((ChainComplex.single₀ (ModuleCat.{u} R)).map a)) q

end HomologicalComplex
