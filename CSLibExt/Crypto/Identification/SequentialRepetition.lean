/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Identification.Sigma

/-!
# Sequential repetition of Sigma protocols

Running a Sigma protocol `m` times in sequence, with a fresh uniform challenge in every round, and
accepting only if every round is accepted, multiplies the soundness errors: a cheating prover for
a statement with no witness is accepted with probability at most `1 / |Ch| ^ m`. This is the
amplification step of Goldwasser, Micali and Rackoff's interactive proofs, used for instance in
the graph-isomorphism protocol of Goldreich, Micali and Wigderson (Protocol 2: "the following four
steps are executed `m` times, each time using independent random coin tosses").

The cheating prover is **adaptive**: in round `i` its commitment `a r l` and its answer
`z r l e` may depend on its coins `r` and on the list `l` of the challenges of the earlier rounds.

* `SigmaProtocol.allAccept x a z m c`: the verifier accepts all `m` rounds with challenges `c`.
* `SigmaProtocol.allAccept_subsingleton`: under special soundness, for a statement with no witness,
  at most one challenge sequence is accepted (in each round, at most one challenge is answerable).
* `SigmaProtocol.seqCheatGame`, `SigmaProtocol.winProb_seqCheatGame_le` (**soundness error of
  sequential repetition**): such a prover is accepted with probability at most `1 / |Ch| ^ m`.

## References

* O. Goldreich, S. Micali and A. Wigderson, *Proofs that yield nothing but their validity or all
  languages in NP have zero-knowledge proof systems*, J. ACM 38 (1991), 691-729, Section 2.2
  (Protocol 2 and the soundness part of the proof of Theorem 2).
* I. Damgård, *On Σ-protocols*, lecture notes, Aarhus University, 2010 (special soundness).
-/

@[expose] public section

namespace Cslib.Crypto.Identification

namespace SigmaProtocol

open Finset Cslib.Crypto.Framework

variable {X W K Cm Ch Z : Type*} (P : SigmaProtocol X W K Cm Ch Z)

/-- **Acceptance of `m` sequential rounds.** For the statement `x`, a prover whose commitment in a
round is `a l` and whose answer to the challenge `e` is `z l e`, where `l` lists the challenges of
the earlier rounds in order, and the challenge sequence `c`, the verifier accepts every round. -/
def allAccept (x : X) : (a : List Ch → Cm) → (z : List Ch → Ch → Z) → (m : ℕ) → (Fin m → Ch) →
    Bool
  | _, _, 0, _ => true
  | a, z, m + 1, c => P.verify x (a []) (c 0) (z [] (c 0)) &&
      allAccept x (fun l => a (c 0 :: l)) (fun l => z (c 0 :: l)) m (Fin.tail c)

/-- **At most one accepted challenge sequence.** Under special soundness, for a statement `x` with
no witness, two challenge sequences that are both accepted against the same (adaptive) prover are
equal: in the first round both challenges are answered for the same commitment, so they coincide,
and the rest follows by induction. -/
theorem allAccept_subsingleton {ext : X → Cm → Ch → Z → Ch → Z → W} (hP : P.SpecialSound ext)
    {x : X} (hx : ∀ w, ¬ P.Rel x w) :
    ∀ (m : ℕ) (a : List Ch → Cm) (z : List Ch → Ch → Z) (c c' : Fin m → Ch),
      P.allAccept x a z m c = true → P.allAccept x a z m c' = true → c = c'
  | 0, _, _, c, c', _, _ => funext fun i => i.elim0
  | m + 1, a, z, c, c', h, h' => by
    simp only [allAccept, Bool.and_eq_true] at h h'
    have h0 : c 0 = c' 0 := by
      by_contra hne
      exact hx _ (hP x (a []) (c 0) (z [] (c 0)) (c' 0) (z [] (c' 0)) hne h.1 h'.1)
    have htail := allAccept_subsingleton hP hx m (fun l => a (c 0 :: l)) (fun l => z (c 0 :: l))
      (Fin.tail c) (Fin.tail c') h.2 (by rw [h0]; exact h'.2)
    rw [← Fin.cons_self_tail c, ← Fin.cons_self_tail c', h0, htail]

variable [Fintype Ch] [Nonempty Ch]

/-- **The experiment of an adaptive cheating prover over `m` sequential rounds**: coins `r`
uniform in `R`, challenges uniform and independent; output whether every round is accepted. -/
noncomputable def seqCheatGame {R : Type*} [Fintype R] [Nonempty R] (x : X)
    (a : R → List Ch → Cm) (z : R → List Ch → Ch → Z) (m : ℕ) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (R × (Fin m → Ch))).map fun ω =>
    P.allAccept x (a ω.1) (z ω.1) m ω.2

/-- **Soundness error of sequential repetition**: under special soundness, an adaptive cheating
prover for a statement with no witness is accepted in all `m` rounds with probability at most
`1 / |Ch| ^ m`. -/
theorem winProb_seqCheatGame_le {ext : X → Cm → Ch → Z → Ch → Z → W} (hP : P.SpecialSound ext)
    {x : X} (hx : ∀ w, ¬ P.Rel x w) {R : Type*} [Fintype R] [Nonempty R]
    (a : R → List Ch → Cm) (z : R → List Ch → Ch → Z) (m : ℕ) :
    winProb (P.seqCheatGame x a z m) ≤ 1 / (Fintype.card Ch : ℝ) ^ m := by
  classical
  rw [seqCheatGame, winProb_map_uniform]
  have hone : ∀ r : R,
      (univ.filter fun c : Fin m → Ch => P.allAccept x (a r) (z r) m c = true).card ≤ 1 :=
    fun r => Finset.card_le_one.mpr fun c hc c' hc' =>
      P.allAccept_subsingleton hP hx m (a r) (z r) c c' (mem_filter.mp hc).2 (mem_filter.mp hc').2
  have hcard : (univ.filter fun ω : R × (Fin m → Ch) =>
      P.allAccept x (a ω.1) (z ω.1) m ω.2 = true).card ≤ Fintype.card R := by
    rw [card_filter, Fintype.sum_prod_type]
    calc ∑ r : R, ∑ c : Fin m → Ch, (if P.allAccept x (a r) (z r) m c = true then 1 else 0)
        = ∑ r : R, (univ.filter fun c : Fin m → Ch =>
            P.allAccept x (a r) (z r) m c = true).card := by
          simp only [card_filter]
      _ ≤ ∑ _r : R, 1 := sum_le_sum fun r _ => hone r
      _ = Fintype.card R := by simp
  have hR : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have hC : (0 : ℝ) < (Fintype.card Ch : ℝ) ^ m := pow_pos (by exact_mod_cast Fintype.card_pos) m
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow,
    div_le_div_iff₀ (mul_pos hR hC) hC]
  have : ((univ.filter fun ω : R × (Fin m → Ch) =>
      P.allAccept x (a ω.1) (z ω.1) m ω.2 = true).card : ℝ) ≤ Fintype.card R := by
    exact_mod_cast hcard
  nlinarith

end SigmaProtocol

end Cslib.Crypto.Identification
