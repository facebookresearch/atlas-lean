/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Basis.Defs

@[expose] public noncomputable section

/-!
# Continuity of the normalized geometric adic Galois operators

The remaining realization request concerns the actual continuous
pro-étale coefficient model. Its carrier is Ext of the discrete coefficient
unit into C(-, ℚ_ell). Its operators are actual inverse image along
id_X × Spec σ, with the fixed coefficient/global-section adjunction.
The Krull topology is the actual topology on Aut_k(K).

Authors of the mathematical source: Pierre Deligne; Bhargav Bhatt;
Peter Scholze.
References: SGA 4½, Rapport, §1; Bhatt--Scholze, The pro-étale topology for
schemes, §6.8, especially Definition 6.8.3 and Proposition 6.8.14.

Completed Axiom étale Galois actions, Tag 03ST and finite-field Frobenius
comparisons are existing toolbox. They are not additional requests here.
-/

namespace WantedExt.AlgebraicGeometry.GeometricAdicGaloisOperators

open CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators

universe u

/-- Every matrix coefficient of the fixed geometric Galois operator is
continuous. A supplied finite basis describes the usual finite-dimensional
adic topology without choosing a cohomology carrier or representation. -/
public theorem_wanted galoisCohomologyOperator_coordinate_continuous
    (ell : ℕ) [Fact ell.Prime] (k K : Type u) [Field k] [Field K]
    [Algebra k K] [IsAlgClosure k K] [Algebra.IsSeparable k K]
    (X : Over (Spec (.of k))) [IsProper X.hom] [Smooth X.hom]
    (ellInvertible : (ell : k) ≠ 0) (n r : ℕ)
    (b : Module.Basis (Fin r) ℚ_[ell] (AdicCohomology ell (geometricFibre X K) n))
    (v : AdicCohomology ell (geometricFibre X K) n) (i : Fin r) :
    Continuous (fun σ : K ≃ₐ[k] K ↦ b.repr (galoisCohomologyOperator X K ell σ n v) i)

end WantedExt.AlgebraicGeometry.GeometricAdicGaloisOperators
