/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Identification.RewindingSimulator
public import CSLibExt.Crypto.Identification.SequentialRepetition
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# The zero-knowledge proof system for graph isomorphism

Goldreich, Micali and Wigderson (J. ACM 38 (1991), Protocol 2 and Theorem 2) give a perfect
zero-knowledge interactive proof that two graphs `G₀`, `G₁` on a common vertex set `V` are
isomorphic. The prover knows `φ` with `G₁ = φ G₀`. In each round it sends a random isomorphic copy
`H = π G₁`; the verifier sends a uniform bit `α`; the prover answers `π` if `α = 1` and `π ∘ φ`
if `α = 0`; the verifier accepts the round if the answer maps `G_α` onto `H`.

One round is a three-move public-coin protocol with challenge set `Bool`, so it is a
`Cslib.Crypto.Identification.SigmaProtocol` (`GraphIsomorphism.sigma`), and the generic results of
`CSLibExt.Crypto.Identification.Sigma` apply:

* `GraphIsomorphism.sigma_complete` (**completeness**): the honest prover is always accepted.
* `GraphIsomorphism.sigma_specialSound`: two accepting answers to both challenges for the same
  `H` give an isomorphism `G₀ → G₁` (`GraphIsomorphism.extract`).
* `GraphIsomorphism.winProb_cheatGame_le_half` (**soundness error `1/2` per round**): if `G₀` and
  `G₁` are not isomorphic, every cheating prover is accepted with probability at most `1/2`,
  because `H` cannot be isomorphic to both graphs (the argument in the proof of GMW Theorem 2).
* `GraphIsomorphism.winProb_seqCheatGame_le` (**soundness error `2^{-m}` over `m` rounds**): the `m`
  rounds of Protocol 2, against an adaptive cheating prover, accept two non-isomorphic graphs with
  probability at most `1 / 2 ^ m` (`SigmaProtocol.winProb_seqCheatGame_le`).
* `GraphIsomorphism.sigma_specialHVZK` and `GraphIsomorphism.sigma_hvzk` (**perfect
  honest-verifier zero knowledge**): for each challenge `α`, the honest pair `(H, answer)` is
  distributed as `(σ G_α, σ)` for a uniform permutation `σ`, which the simulator
  `GraphIsomorphism.simAt` samples from the graphs alone.

* `GraphIsomorphism.winProb_attemptDist_half` and
  `GraphIsomorphism.abs_winProb_simulatorK_sub_le_half_pow`
  (**zero knowledge against an arbitrary verifier, one round**): instances of the generic rewinding
  simulator of `CSLibExt.Crypto.Identification.RewindingSimulator`. For any verifier whose
  challenge is any function of the prover's graph and of its coins, one attempt (guess the
  challenge, simulate, keep the attempt if the guess was right) succeeds with probability exactly
  `1/2` and then reproduces the real view exactly; with `k` attempts, every test of the view
  (counting a failed simulation as failing the test) has probabilities within `2^{-k}`.

**Scope.** GMW's simulator repeats attempts until one succeeds and is perfect in expected
polynomial time; here it is truncated after `k` attempts, which gives an approximation within
`2^{-k}` on every test rather than perfect zero knowledge. Only one round is simulated, against
verifiers modelled as functions of the graph `H` and of their coins; the composition over `m`
rounds (with a verifier whose challenges depend on the earlier rounds) and the completeness of
the `m`-round protocol (round by round from `GraphIsomorphism.sigma_complete`) are not formalized.

Graphs are Mathlib's `SimpleGraph V`, relabelled by `SimpleGraph.map`; the statement `x` is the
pair `(G₀, G₁)` and the witness is a permutation `φ` of `V` with `G₀.map φ = G₁`
(`GraphIsomorphism.exists_rel_iff_nonempty_iso`: such a `φ` exists exactly when `G₀ ≃g G₁`).

## Relation to `CSLibExt.Crypto.Identification.GraphIso`

That module formalizes the same protocol as `GraphIso.sigma n`, for graphs given as adjacency
functions `Fin n → Fin n → Bool` (directed graphs and loops allowed) and with the prover
committing to a relabelling of `G₀` instead of `G₁`; it proves only completeness
(`GraphIso.sigma_complete`).

## References

* O. Goldreich, S. Micali and A. Wigderson, *Proofs that yield nothing but their validity or all
  languages in NP have zero-knowledge proof systems*, J. ACM 38 (1991), 691-729, Section 2.2
  (Protocol 2, Theorem 2).
* S. Goldwasser, S. Micali and C. Rackoff, *The knowledge complexity of interactive proof
  systems*, SIAM J. Comput. 18 (1989), 186-208 (the definitions of interactive proofs and zero
  knowledge, as restated in GMW, Definitions 2 and 3).
-/

@[expose] public section

namespace Cslib.Crypto.Identification

namespace GraphIsomorphism

open Cslib.Crypto.Framework

variable {V : Type*}

/-- **The graph a challenge asks about.** For the statement `x = (G₀, G₁)`, the challenge `α`
selects `G₁` when `α = true` and `G₀` when `α = false`. -/
def pickGraph (x : SimpleGraph V × SimpleGraph V) (α : Bool) : SimpleGraph V :=
  if α then x.2 else x.1

@[simp] theorem pickGraph_true (x : SimpleGraph V × SimpleGraph V) : pickGraph x true = x.2 := rfl

@[simp] theorem pickGraph_false (x : SimpleGraph V × SimpleGraph V) :
    pickGraph x false = x.1 := rfl

open Classical in
/-- **The graph-isomorphism protocol as a Sigma protocol** (Goldreich, Micali and Wigderson,
J. ACM 1991, Protocol 2, one round). Statements are pairs `(G₀, G₁)` of graphs on `V`; a witness is
a permutation `φ` with `G₀.map φ = G₁`; the prover's coins are a permutation `π`; it commits to
`H = G₁.map π`; on challenge `α` it answers `π` (`α = true`) or `π * φ = π ∘ φ` (`α = false`); the
verifier accepts the answer `σ` when `G_α.map σ = H`. -/
noncomputable def sigma :
    SigmaProtocol (SimpleGraph V × SimpleGraph V) (Equiv.Perm V) (Equiv.Perm V) (SimpleGraph V)
      Bool (Equiv.Perm V) where
  Rel x φ := x.1.map φ = x.2
  commit x _ π := x.2.map π
  respond _ φ π α := if α then π else π * φ
  verify x H α σ := decide ((pickGraph x α).map σ = H)

theorem sigma_verify_eq_true_iff {x : SimpleGraph V × SimpleGraph V} {H : SimpleGraph V}
    {α : Bool} {σ : Equiv.Perm V} :
    sigma.verify x H α σ = true ↔ (pickGraph x α).map σ = H := by
  classical
  simp [sigma]

/-- **Composing relabellings**: relabelling by `σ` and then by `τ` is relabelling by `τ * σ`. -/
theorem map_map_perm (G : SimpleGraph V) (σ τ : Equiv.Perm V) :
    (G.map σ).map τ = G.map (τ * σ) := by
  rw [SimpleGraph.map_map, Equiv.Perm.coe_mul]

/-- **Relabelling by the identity** does nothing. -/
theorem map_one_perm (G : SimpleGraph V) : G.map (1 : Equiv.Perm V) = G := by
  rw [Equiv.Perm.coe_one]
  exact SimpleGraph.map_id (G := G)

/-- **Witnesses are isomorphisms.** A permutation `φ` with `G₀.map φ = G₁` exists if and only if
`G₀` and `G₁` are isomorphic in Mathlib's sense. -/
theorem exists_rel_iff_nonempty_iso (G₀ G₁ : SimpleGraph V) :
    (∃ φ : Equiv.Perm V, G₀.map φ = G₁) ↔ Nonempty (G₀ ≃g G₁) := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨SimpleGraph.Iso.map φ G₀⟩
  · rintro ⟨e⟩
    refine ⟨e.toEquiv, ?_⟩
    ext u v
    change (G₀.map (e.toEquiv.toEmbedding : V ↪ V)).Adj u v ↔ G₁.Adj u v
    rw [SimpleGraph.map_adj]
    constructor
    · rintro ⟨u', v', h, rfl, rfl⟩
      exact e.map_rel_iff.mpr h
    · intro h
      refine ⟨e.symm u, e.symm v, e.symm.map_rel_iff.mpr h, by simp, by simp⟩

/-- **Completeness** of the graph-isomorphism protocol: for isomorphic graphs, the honest prover
answers every challenge correctly (GMW, proof of Theorem 2, first paragraph). -/
theorem sigma_complete : (sigma (V := V)).Complete := by
  rintro ⟨G₀, G₁⟩ φ (hφ : G₀.map φ = G₁) π α
  rw [sigma_verify_eq_true_iff]
  cases α
  · change G₀.map (π * φ) = G₁.map π
    rw [← map_map_perm, hφ]
  · rfl

/-- **The extractor**: from accepting answers `σ` to challenge `α` and `σ'` to challenge `α'`
for the same commitment, the permutation `σ₁⁻¹ * σ₀`, where `σ₀` is the answer to challenge
`false` and `σ₁` the answer to challenge `true`. -/
def extract (_x : SimpleGraph V × SimpleGraph V) (_H : SimpleGraph V) (α : Bool)
    (σ : Equiv.Perm V) (_α' : Bool) (σ' : Equiv.Perm V) : Equiv.Perm V :=
  if α then σ⁻¹ * σ' else σ'⁻¹ * σ

/-- **Two answers give an isomorphism**: if `G₀.map σ₀ = H` and `G₁.map σ₁ = H` then `σ₁⁻¹ * σ₀`
maps `G₀` onto `G₁`. -/
theorem map_inv_mul_eq {G₀ G₁ H : SimpleGraph V} {σ₀ σ₁ : Equiv.Perm V} (h₀ : G₀.map σ₀ = H)
    (h₁ : G₁.map σ₁ = H) : G₀.map (σ₁⁻¹ * σ₀) = G₁ := by
  rw [← map_map_perm, h₀, ← h₁, map_map_perm, inv_mul_cancel, map_one_perm]

/-- **Special soundness** of the graph-isomorphism protocol: accepting answers to both challenges
for the same `H` yield an isomorphism from `G₀` to `G₁` (GMW, proof of Theorem 2: "the graphs `H`
sent by him cannot be isomorphic to both `G₁` and `G₀`"). -/
theorem sigma_specialSound : (sigma (V := V)).SpecialSound extract := by
  rintro ⟨G₀, G₁⟩ H α σ α' σ' hne h h'
  rw [sigma_verify_eq_true_iff] at h h'
  change G₀.map (extract (G₀, G₁) H α σ α' σ') = G₁
  cases α <;> cases α'
  · exact absurd rfl hne
  · exact map_inv_mul_eq h h'
  · exact map_inv_mul_eq h' h
  · exact absurd rfl hne

/-- **Non-isomorphic graphs have no witness**: if `G₀` and `G₁` are not isomorphic, no permutation
maps `G₀` onto `G₁`. -/
theorem forall_not_rel_of_isEmpty {G₀ G₁ : SimpleGraph V} (hiso : IsEmpty (G₀ ≃g G₁)) :
    ∀ φ, ¬ sigma.Rel (G₀, G₁) φ := fun φ hφ =>
  hiso.false ((exists_rel_iff_nonempty_iso G₀ G₁).mp ⟨φ, hφ⟩).some

/-- **Soundness error `1/2` per round.** If `G₀` and `G₁` are not isomorphic, a cheating prover
with coins in any finite type `R`, committing to `a r` and answering `z r α`, convinces the honest
verifier of one round with probability at most `1/2` (GMW, proof of Theorem 2). This is
`SigmaProtocol.winProb_cheatGame_le` for the two-element challenge set. -/
theorem winProb_cheatGame_le_half {R : Type*} [Fintype R] [Nonempty R]
    {G₀ G₁ : SimpleGraph V} (hiso : IsEmpty (G₀ ≃g G₁)) (a : R → SimpleGraph V)
    (z : R → Bool → Equiv.Perm V) :
    winProb (sigma.cheatGame (G₀, G₁) a z) ≤ 1 / 2 := by
  have hx := forall_not_rel_of_isEmpty hiso
  have := sigma.winProb_cheatGame_le sigma_specialSound hx a z
  simpa using this

/-- **Soundness error `2^{-m}` over `m` rounds** (GMW, Protocol 2 and proof of Theorem 2): if
`G₀` and `G₁` are not isomorphic, an adaptive cheating prover, whose graph and answers in each
round may depend on its coins and on the earlier challenges, passes all `m` rounds with
probability at most `1 / 2 ^ m`. -/
theorem winProb_seqCheatGame_le {R : Type*} [Fintype R] [Nonempty R]
    {G₀ G₁ : SimpleGraph V} (hiso : IsEmpty (G₀ ≃g G₁)) (a : R → List Bool → SimpleGraph V)
    (z : R → List Bool → Bool → Equiv.Perm V) (m : ℕ) :
    winProb (sigma.seqCheatGame (G₀, G₁) a z m) ≤ 1 / 2 ^ m := by
  have hx := forall_not_rel_of_isEmpty hiso
  have := sigma.winProb_seqCheatGame_le sigma_specialSound hx a z m
  simpa using this

section Finite

variable [Fintype V] [DecidableEq V]

/-- **The per-challenge simulator**: for the challenge `α`, a uniform permutation `σ` and the
pair `(G_α.map σ, σ)`, computed from the two graphs alone. -/
noncomputable def simAt (x : SimpleGraph V × SimpleGraph V) (α : Bool) :
    PMF (SimpleGraph V × Equiv.Perm V) :=
  (Cslib.Probability.PMF.uniformOfFintype (Equiv.Perm V)).map fun σ : Equiv.Perm V =>
    ((pickGraph x α).map σ, σ)

/-- **Perfect special honest-verifier zero knowledge** of the graph-isomorphism protocol: for
isomorphic graphs and every challenge `α`, the honest commitment–answer pair has exactly the
distribution `simAt x α`. For `α = true` the pair is `(G₁.map π, π)`; for `α = false` it is
`(G₁.map π, π * φ) = (G₀.map σ, σ)` with `σ = π * φ`, uniform when `π` is. -/
theorem sigma_specialHVZK : (sigma (V := V)).SpecialHVZK simAt := by
  rintro ⟨G₀, G₁⟩ φ (hφ : G₀.map φ = G₁) α
  rw [SigmaProtocol.challengeTranscript, simAt]
  cases α
  · have hcomp : (fun π : Equiv.Perm V => (sigma.commit (G₀, G₁) φ π,
        sigma.respond (G₀, G₁) φ π false)) =
        (fun σ : Equiv.Perm V => ((pickGraph (G₀, G₁) false).map σ, σ)) ∘ Equiv.mulRight φ := by
      funext π
      simp only [sigma, Function.comp, Equiv.coe_mulRight, pickGraph_false, Bool.false_eq_true,
        ite_false, Prod.mk.injEq, and_true]
      rw [← map_map_perm, hφ]
    rw [hcomp, ← PMF.map_comp, Cslib.Probability.PMF.uniformOfFintype_map_equiv]
  · rfl

/-- **Perfect honest-verifier zero knowledge** of the graph-isomorphism protocol, with the
simulator that draws a uniform challenge `α` and a uniform permutation `σ` and outputs
`(G_α.map σ, α, σ)`. -/
theorem sigma_hvzk :
    (sigma (V := V)).HVZK (SigmaProtocol.uniformChallengeSim simAt) :=
  sigma_specialHVZK.hvzk

end Finite


/-! ### Zero knowledge against an arbitrary verifier -/

section CheatingVerifier

variable [Fintype V] [DecidableEq V] {R : Type*} [Fintype R] [Nonempty R]

/-- **One rewinding attempt for the graph-isomorphism protocol** (Goldreich, Micali and Wigderson,
J. ACM 1991, proof of Theorem 2, exact form): for isomorphic graphs with witness `φ`, every
verifier `Vstar` (its challenge any function of the prover's graph `H` and of its coins) and every
test `T` of its view, one attempt of the simulator (guess `α'`, send `G_{α'}.map σ`, keep the
attempt if the verifier asks `α'`) succeeds and passes `T` with probability exactly half the
probability that the real view passes `T`. -/
theorem winProb_attemptDist_half {G₀ G₁ : SimpleGraph V} {φ : Equiv.Perm V}
    (hφ : G₀.map φ = G₁) (Vstar : SimpleGraph V → R → Bool)
    (T : R × SimpleGraph V × Equiv.Perm V → Bool) :
    winProb ((SigmaProtocol.attemptDist simAt (G₀, G₁) Vstar).map fun p => p.1 && T p.2) =
      winProb ((sigma.realViewDist (G₀, G₁) φ Vstar).map T) / 2 := by
  have := sigma.winProb_attemptDist sigma_specialHVZK (x := (G₀, G₁)) hφ Vstar T
  simpa using this

/-- **Zero knowledge of the graph-isomorphism protocol against an arbitrary verifier,
one round** (Goldreich, Micali and Wigderson, J. ACM 1991, Theorem 2, truncated form): for
isomorphic graphs, every verifier and every test `T` of its view, the rewinding simulator with `k`
attempts (which never sees the witness) and the real interaction pass `T` with probabilities that
differ by at most `1 / 2 ^ k`. -/
theorem abs_winProb_simulatorK_sub_le_half_pow {G₀ G₁ : SimpleGraph V} {φ : Equiv.Perm V}
    (hφ : G₀.map φ = G₁) (Vstar : SimpleGraph V → R → Bool)
    (T : R × SimpleGraph V × Equiv.Perm V → Bool) (k : ℕ) :
    |winProb ((SigmaProtocol.simulatorK simAt (G₀, G₁) Vstar k).map fun o => o.elim false T) -
        winProb ((sigma.realViewDist (G₀, G₁) φ Vstar).map T)| ≤ 1 / 2 ^ k := by
  have := sigma.abs_winProb_simulatorK_sub_le sigma_specialHVZK (x := (G₀, G₁)) hφ Vstar T k
  norm_num at this ⊢
  simpa [inv_pow] using this

end CheatingVerifier

end GraphIsomorphism

end Cslib.Crypto.Identification
