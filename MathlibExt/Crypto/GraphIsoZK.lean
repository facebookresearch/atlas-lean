/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Pi

/-!
# Graph-isomorphism sigma protocol completeness

Graphs are adjacency functions on `Fin n`, with permutations
acting by relabeling. In the sigma protocol the prover
commits `H = ρ • G₁`, answers challenge `b` with `ρ⁻¹`
(`b = false`) or `ρ⁻¹φ` composed appropriately
(`b = true`, response `φ * ρ.symm` under this action), and
verification relabels `H` back. Completeness: an honest
prover always passes. Soundness and honest-verifier
zero-knowledge are not included here.
-/

@[expose] public section

/-- Graphs as adjacency functions on `Fin n` (ZK core of
QCI-28); permutations act by relabeling. -/
def graphAct {n : ℕ} (σ : Equiv.Perm (Fin n)) (G : Fin n → Fin n → Bool)
    (u v : Fin n) : Bool :=
  G (σ.symm u) (σ.symm v)

/-- The graph isomorphism sigma protocol: the prover commits
`H = ρ • G₁`, the verifier challenges `b : Bool`, the prover
responds with a permutation; verification checks that the
response maps the committed graph back to `G_b` (`G₂` for
`b = true`, `G₁` for `false`), where the prover's secret is
`φ` with `graphAct φ G₁ = G₂`. -/
def zkVerify {n : ℕ} (G₁ G₂ H : Fin n → Fin n → Bool) (b : Bool)
    (τ : Equiv.Perm (Fin n)) : Bool :=
  graphAct τ H == (if b then G₂ else G₁)

/-- Composition of relabelings: applying `τ` then `σ` is the
single relabeling `σ * τ`. -/
private theorem graphAct_comp {n : ℕ} (σ τ : Equiv.Perm (Fin n))
    (G : Fin n → Fin n → Bool) :
    graphAct σ (graphAct τ G) = graphAct (σ * τ) G := by
  funext u v
  simp only [graphAct, ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.Perm.mul_apply]

/-- The identity permutation acts trivially. -/
private theorem graphAct_one {n : ℕ} (G : Fin n → Fin n → Bool) :
    graphAct 1 G = G := by
  funext u v
  rfl

/-- Completeness: an honest prover who knows `φ` with
`graphAct φ G₁ = G₂` and commitment randomness `ρ` always
answers: for challenge `false` respond `ρ⁻¹`, for `true`
respond `φ * ρ⁻¹`, and verification accepts
(`graphAct` composes as `graphAct σ (graphAct τ G) =
graphAct (σ * τ) G`). -/
theorem zkVerify_complete {n : ℕ} {G₁ G₂ : Fin n → Fin n → Bool}
    (φ ρ : Equiv.Perm (Fin n))
    (hφ : graphAct φ G₁ = G₂) (b : Bool) :
    zkVerify G₁ G₂ (graphAct ρ G₁) b
      (if b then φ * ρ.symm else ρ.symm) = true := by
  cases b with
  | false =>
    have h : graphAct ρ.symm (graphAct ρ G₁) = G₁ := by
      rw [graphAct_comp, ← Equiv.Perm.inv_def, inv_mul_cancel, graphAct_one]
    simp [zkVerify, h]
  | true =>
    have h : graphAct (φ * ρ.symm) (graphAct ρ G₁) = G₂ := by
      rw [graphAct_comp, mul_assoc, ← Equiv.Perm.inv_def, inv_mul_cancel, mul_one, hφ]
    simp [zkVerify, h]

#print axioms zkVerify_complete

end
