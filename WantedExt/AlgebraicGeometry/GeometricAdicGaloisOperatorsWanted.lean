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
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.LinearAlgebra.Basis.Defs

@[expose] public noncomputable section

/-!
# Continuity of the Galois action on `ℓ`-adic cohomology

For a proper smooth scheme `X` over a field `k`, a separable closure `K` of `k` and a prime `ℓ`
invertible in `k`, the absolute Galois group `Aut_k(K)`, with its Krull topology, acts
continuously on the finite-dimensional `ℚ_ℓ`-vector space `H^n(X_K, ℚ_ℓ)`: the operators
`galoisCohomologyOperator` are `ℚ_ℓ`-linear and form a representation of `Aut_k(K)`, and in any
basis its matrix coefficients are continuous.

Here `H^n(X_K, ℚ_ℓ)` is the cohomology of the pro-étale sheaf `C(-, ℚ_ℓ)`
(`MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators.AdicCohomology`), which computes
`ℓ`-adic cohomology for such `X`, and `σ` acts by inverse image along `id_X × Spec σ`.

References: SGA 4½, Rapport, §1; Bhatt--Scholze, The pro-étale topology for
schemes, §6.8, especially Definition 6.8.3 and Proposition 6.8.14.
-/

namespace WantedExt.AlgebraicGeometry.GeometricAdicGaloisOperators

open CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators

universe u

/-- **Continuity of the Galois action on ℓ-adic cohomology.** Let $\ell$ be a prime invertible in a
field $k$, $K$ a separable closure of $k$, $X$ a proper smooth $k$-scheme, $n \in \mathbb{N}$, and
$b$ a basis, indexed by $\{0, \dots, r - 1\}$, of $H^n(X_K, \mathbb{Q}_\ell)$ (the cohomology of the
pro-étale sheaf $C(-, \mathbb{Q}_\ell)$ on the geometric fibre). Then the operators
`galoisCohomologyOperator` form a representation $\rho$ of $\mathrm{Aut}_k(K)$ by
$\mathbb{Q}_\ell$-linear maps, and for every $v$ and $i$ the coordinate
$\sigma \mapsto (b.\mathrm{repr}(\rho(\sigma) v))_i$ is continuous for the Krull topology. -/
public theorem_wanted galoisCohomologyOperator_coordinate_continuous
    (ell : ℕ) [Fact ell.Prime] (k K : Type u) [Field k] [Field K]
    [Algebra k K] [IsSepClosure k K]
    (X : Over (Spec (.of k))) [IsProper X.hom] [Smooth X.hom]
    (ellInvertible : (ell : k) ≠ 0) (n r : ℕ)
    (b : Module.Basis (Fin r) ℚ_[ell] (AdicCohomology ell (geometricFibre X K) n)) :
    ∃ ρ : (K ≃ₐ[k] K) →* Module.End ℚ_[ell] (AdicCohomology ell (geometricFibre X K) n),
      (∀ σ v, ρ σ v = galoisCohomologyOperator X K ell σ n v) ∧
        ∀ (v : AdicCohomology ell (geometricFibre X K) n) (i : Fin r),
          Continuous (fun σ : K ≃ₐ[k] K ↦ b.repr (ρ σ v) i)

end WantedExt.AlgebraicGeometry.GeometricAdicGaloisOperators
