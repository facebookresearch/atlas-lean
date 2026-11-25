/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Identification.GraphIsomorphism

/-!
# Tests for the graph-isomorphism zero-knowledge protocol

* **A true statement.** On `Fin 3`, the path `G₀` with edges `0 – 1`, `1 – 2` and its image `G₁`
  under the transposition `φ = (0 1)`; `φ` is a witness. Every honest transcript is accepted, and
  the honest pair for each challenge is distributed as the simulator's.
* **A cheating verifier.** The verifier that asks `α = 1` exactly when the prover's graph contains
  the edge `0 – 2` (using no coins) is simulated: one attempt succeeds and matches the real view
  up to the factor `1/2`, and the truncated simulator is within `2^{-k}` of the real view.
* **A false statement.** On `Fin 2`, the empty graph and the complete graph are not isomorphic,
  so every cheating prover passes one round with probability at most `1/2`, and `m` rounds with
  probability at most `1 / 2 ^ m`.
-/

@[expose] public section

namespace Cslib.Crypto.GraphIsomorphismTests

open Cslib.Crypto.Identification Cslib.Crypto.Identification.GraphIsomorphism Cslib.Crypto.Framework

/-- The path `0 – 1 – 2`. -/
def G₀ : SimpleGraph (Fin 3) := SimpleGraph.fromEdgeSet {s(0, 1), s(1, 2)}

/-- The transposition `(0 1)`. -/
def φ : Equiv.Perm (Fin 3) := Equiv.swap 0 1

/-- The relabelled path `1 – 0 – 2`. -/
def G₁ : SimpleGraph (Fin 3) := G₀.map φ

theorem rel : (sigma (V := Fin 3)).Rel (G₀, G₁) φ := rfl

example : Nonempty (G₀ ≃g G₁) := (exists_rel_iff_nonempty_iso G₀ G₁).mp ⟨φ, rfl⟩

/-- Every honest transcript is accepted. -/
example (π : Equiv.Perm (Fin 3)) (α : Bool) :
    sigma.verify (G₀, G₁) (sigma.commit (G₀, G₁) φ π) α (sigma.respond (G₀, G₁) φ π α) = true :=
  sigma_complete _ _ rel π α

/-- The honest pair for challenge `false` is distributed as the simulator's. -/
example : sigma.challengeTranscript (G₀, G₁) φ false = simAt (G₀, G₁) false :=
  sigma_specialHVZK _ _ rel false

open Classical in
/-- A verifier whose challenge depends on the prover's graph. -/
noncomputable def edgeVerifier : SimpleGraph (Fin 3) → Unit → Bool :=
  fun H _ => decide (H.Adj 0 2)

example (T : Unit × SimpleGraph (Fin 3) × Equiv.Perm (Fin 3) → Bool) :
    winProb ((SigmaProtocol.attemptDist simAt (G₀, G₁) edgeVerifier).map fun p => p.1 && T p.2) =
      winProb ((sigma.realViewDist (G₀, G₁) φ edgeVerifier).map T) / 2 :=
  winProb_attemptDist_half rfl edgeVerifier T

example (T : Unit × SimpleGraph (Fin 3) × Equiv.Perm (Fin 3) → Bool) (k : ℕ) :
    |winProb ((SigmaProtocol.simulatorK simAt (G₀, G₁) edgeVerifier k).map
        fun o => o.elim false T) -
      winProb ((sigma.realViewDist (G₀, G₁) φ edgeVerifier).map T)| ≤ 1 / 2 ^ k :=
  abs_winProb_simulatorK_sub_le_half_pow rfl edgeVerifier T k

/-- With zero attempts the simulator always fails. -/
example (T : Unit × SimpleGraph (Fin 3) × Equiv.Perm (Fin 3) → Bool) :
    winProb ((SigmaProtocol.simulatorK simAt (G₀, G₁) edgeVerifier 0).map
      fun o => o.elim false T) = 0 := by
  rw [SigmaProtocol.simulatorK, PMF.pure_map]
  simp

/-- The empty and the complete graph on two vertices are not isomorphic. -/
theorem not_iso : IsEmpty ((⊥ : SimpleGraph (Fin 2)) ≃g (⊤ : SimpleGraph (Fin 2))) := by
  refine ⟨fun e => ?_⟩
  have h : (⊤ : SimpleGraph (Fin 2)).Adj (e 0) (e 1) := by simp
  exact (e.map_rel_iff.mp h).elim

example {R : Type} [Fintype R] [Nonempty R] (a : R → SimpleGraph (Fin 2))
    (z : R → Bool → Equiv.Perm (Fin 2)) :
    winProb (sigma.cheatGame (⊥, ⊤) a z) ≤ 1 / 2 :=
  winProb_cheatGame_le_half not_iso a z

example {R : Type} [Fintype R] [Nonempty R] (a : R → List Bool → SimpleGraph (Fin 2))
    (z : R → List Bool → Bool → Equiv.Perm (Fin 2)) (m : ℕ) :
    winProb (sigma.seqCheatGame (⊥, ⊤) a z m) ≤ 1 / 2 ^ m :=
  winProb_seqCheatGame_le not_iso a z m

end Cslib.Crypto.GraphIsomorphismTests
