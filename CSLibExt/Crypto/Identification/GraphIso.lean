/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Identification.Sigma

/-!
# The graph-isomorphism Sigma protocol

A graph on the vertices `Fin n` is given by its adjacency function `G : Fin n → Fin n → Bool`.
Every such function is allowed, so directed graphs and graphs with loops are included; simple
graphs are the symmetric, irreflexive adjacency functions. A permutation `σ` relabels `G` to
`graphAct σ G`, which has the edge `(σ a, σ b)` exactly when `G` has the edge `(a, b)`, and `φ` is
an isomorphism from `G₀` to `G₁` when `graphAct φ G₀ = G₁`.

`GraphIso.sigma n` is the graph-isomorphism protocol as a `SigmaProtocol`. The statement is a pair
of graphs `(G₀, G₁)` and the witness is an isomorphism `φ` from `G₀` to `G₁`. With coins `ρ`, the
prover commits to `H = graphAct ρ G₀`; on the challenge `b` it answers `ρ⁻¹` if `b = false` and
`φ * ρ⁻¹` if `b = true`. The verifier accepts the answer `τ` when `graphAct τ H` is `G₀` for
`b = false` and `G₁` for `b = true`.

## Main results

* `GraphIso.graphAct_mul`, `GraphIso.graphAct_one`: relabeling is an action of the permutation
  group.
* `GraphIso.sigma_complete`: completeness; the honest prover is accepted for every choice of
  coins and challenge.

Special soundness and honest-verifier zero knowledge are not proved here; they are proved for the
`SimpleGraph` formulation in `CSLibExt.Crypto.Identification.GraphIsomorphism`
(`GraphIsomorphism.sigma_specialSound`, `GraphIsomorphism.sigma_hvzk`).

## References

* O. Goldreich, S. Micali and A. Wigderson, *Proofs that yield nothing but their validity or all
  languages in NP have zero-knowledge proof systems*, J. ACM 38 (1991).
-/

@[expose] public section

namespace Cslib.Crypto.Identification.GraphIso

/-- Relabeling of a graph on `Fin n` by the permutation `σ`: `graphAct σ G` has the edge
`(σ a, σ b)` exactly when `G` has the edge `(a, b)`. -/
def graphAct {n : ℕ} (σ : Equiv.Perm (Fin n)) (G : Fin n → Fin n → Bool) :
    Fin n → Fin n → Bool :=
  fun u v => G (σ.symm u) (σ.symm v)

/-- Relabeling by `τ` and then by `σ` is relabeling by `σ * τ`. -/
theorem graphAct_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (G : Fin n → Fin n → Bool) :
    graphAct σ (graphAct τ G) = graphAct (σ * τ) G := by
  funext u v
  simp only [graphAct, ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.Perm.mul_apply]

/-- Relabeling by the identity permutation does not change a graph. -/
theorem graphAct_one {n : ℕ} (G : Fin n → Fin n → Bool) : graphAct 1 G = G :=
  rfl

/-- The **graph-isomorphism Sigma protocol** on the vertices `Fin n`. Statements are pairs of graphs
`(G₀, G₁)`, and the witnesses for `(G₀, G₁)` are the isomorphisms `φ` from `G₀` to `G₁`. The
prover's coins are a permutation `ρ` and its commitment is `graphAct ρ G₀`. The challenge is a bit
`b`, answered by `ρ⁻¹` if `b = false` and by `φ * ρ⁻¹` if `b = true`, and the verifier accepts the
answer `τ` to the commitment `H` when `graphAct τ H` is `G₀` or `G₁` according to `b`. -/
def sigma (n : ℕ) :
    SigmaProtocol ((Fin n → Fin n → Bool) × (Fin n → Fin n → Bool)) (Equiv.Perm (Fin n))
      (Equiv.Perm (Fin n)) (Fin n → Fin n → Bool) Bool (Equiv.Perm (Fin n)) where
  Rel G φ := graphAct φ G.1 = G.2
  commit G _ ρ := graphAct ρ G.1
  respond _ φ ρ b := if b then φ * ρ⁻¹ else ρ⁻¹
  verify G H b τ := decide (graphAct τ H = if b then G.2 else G.1)

/-- **Completeness** of the graph-isomorphism Sigma protocol: if `φ` is an isomorphism from `G₀` to
`G₁`, then for all coins `ρ` and both challenges the honest answer relabels the commitment
`graphAct ρ G₀` to the challenged graph. -/
theorem sigma_complete (n : ℕ) : (sigma n).Complete := by
  rintro ⟨G₀, G₁⟩ φ hφ ρ b
  cases b with
  | false =>
    have h : graphAct ρ⁻¹ (graphAct ρ G₀) = G₀ := by
      rw [graphAct_mul, inv_mul_cancel, graphAct_one]
    simp [sigma, h]
  | true =>
    have h : graphAct (φ * ρ⁻¹) (graphAct ρ G₀) = G₁ := by
      rw [graphAct_mul, mul_assoc, inv_mul_cancel, mul_one]
      exact hφ
    simp [sigma, h]

end Cslib.Crypto.Identification.GraphIso
