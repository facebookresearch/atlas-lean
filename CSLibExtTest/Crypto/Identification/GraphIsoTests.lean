/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Identification.GraphIso

/-!
# Tests for the graph-isomorphism Sigma protocol

On the vertices `Fin 3`, `G₀` has the single undirected edge `{0, 1}`, and the isomorphism
`φ = swap 1 2` maps it to `G₁`, whose single edge is `{0, 2}`. The prover's coins are the 3-cycle
`ρ = swap 0 1 * swap 1 2` (`0 ↦ 1 ↦ 2 ↦ 0`), which does not commute with `φ`, and the commitment
`H = graphAct ρ G₀` has the single edge `{1, 2}`. The honest answers to both challenges are
accepted. Rejected: each honest answer sent for the other challenge, the answer `ρ⁻¹ * φ` with the
composition reversed, and the coins `ρ` sent for the challenge `false`.
-/

@[expose] public section

namespace Cslib.Crypto.GraphIsoTests

open Cslib.Crypto.Identification Cslib.Crypto.Identification.GraphIso

/-- The graph on `Fin 3` with the single undirected edge `{0, 1}`. -/
def G₀ : Fin 3 → Fin 3 → Bool := fun a b => (a == 0 && b == 1) || (a == 1 && b == 0)

/-- The graph on `Fin 3` with the single undirected edge `{0, 2}`. -/
def G₁ : Fin 3 → Fin 3 → Bool := fun a b => (a == 0 && b == 2) || (a == 2 && b == 0)

/-- The graph on `Fin 3` with the single undirected edge `{1, 2}`. -/
def H : Fin 3 → Fin 3 → Bool := fun a b => (a == 1 && b == 2) || (a == 2 && b == 1)

/-- The witness: the isomorphism `swap 1 2` from `G₀` to `G₁`. -/
def φ : Equiv.Perm (Fin 3) := Equiv.swap 1 2

/-- The prover's coins: the 3-cycle `0 ↦ 1 ↦ 2 ↦ 0`. -/
def ρ : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

example : ρ 0 = 1 ∧ ρ 1 = 2 ∧ ρ 2 = 0 := by decide

/-- The coins and the witness do not commute. -/
example : φ * ρ ≠ ρ * φ := by decide

/-- `φ` is a witness for `(G₀, G₁)`, and `ρ` is not. -/
example : (sigma 3).Rel (G₀, G₁) φ :=
  show graphAct φ G₀ = G₁ by decide

example : ¬ (sigma 3).Rel (G₀, G₁) ρ :=
  show ¬ graphAct ρ G₀ = G₁ by decide

/-- The commitment is `H`. -/
example : (sigma 3).commit (G₀, G₁) φ ρ = H := by decide

/-- The honest answers: `ρ⁻¹` to the challenge `false` and `φ * ρ⁻¹` to the challenge `true`. -/
example : (sigma 3).respond (G₀, G₁) φ ρ false = ρ⁻¹ ∧
    (sigma 3).respond (G₀, G₁) φ ρ true = φ * ρ⁻¹ := ⟨rfl, rfl⟩

/-- Both honest transcripts are accepted. -/
example : (sigma 3).verify (G₀, G₁) H false ρ⁻¹ = true := by decide

example : (sigma 3).verify (G₀, G₁) H true (φ * ρ⁻¹) = true := by decide

/-- An honest answer sent for the other challenge is rejected. -/
example : (sigma 3).verify (G₀, G₁) H true ρ⁻¹ = false := by decide

example : (sigma 3).verify (G₀, G₁) H false (φ * ρ⁻¹) = false := by decide

/-- The answer with the composition reversed is rejected. -/
example : (sigma 3).verify (G₀, G₁) H true (ρ⁻¹ * φ) = false := by decide

/-- The coins themselves are rejected as the answer to the challenge `false`. -/
example : (sigma 3).verify (G₀, G₁) H false ρ = false := by decide

/-- Completeness at this statement and witness, for both challenges. -/
example (b : Bool) :
    (sigma 3).verify (G₀, G₁) ((sigma 3).commit (G₀, G₁) φ ρ) b
      ((sigma 3).respond (G₀, G₁) φ ρ b) = true :=
  sigma_complete 3 (G₀, G₁) φ (show graphAct φ G₀ = G₁ by decide) ρ b

end Cslib.Crypto.GraphIsoTests
