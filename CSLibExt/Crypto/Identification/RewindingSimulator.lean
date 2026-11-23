/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Identification.Sigma

/-!
# Simulating an arbitrary verifier by rewinding

Goldwasser, Micali and Rackoff (SIAM J. Comput. 1989, Section 5, proof of Theorem 1) and
Goldreich, Micali and Wigderson (J. ACM 1991, proof of Theorem 2) simulate a *cheating* verifier
of a protocol with a small challenge set by guessing its challenge: pick a challenge `e'`, produce
a commitment and an answer for `e'` without the witness, and keep the attempt only if the verifier,
shown the commitment, asks exactly `e'`; otherwise start again. This file proves that this works
for every Sigma protocol with a perfect special honest-verifier zero-knowledge simulator, against
every one-round verifier whose challenge is any function of the commitment and of its coins.

* `realViewDist P x w Vstar`: the verifier's view `(coins, commitment, answer)` in one real round.
* `attemptDist sim x Vstar`: one simulation attempt, with its success bit.
* `winProb_attemptDist` (**one attempt**): for every test `T` of the view,
  `Pr[the attempt succeeds and T holds] = Pr[T holds of the real view] / |Ch|`. So an attempt
  succeeds with probability exactly `1 / |Ch|`, whatever the verifier does, and a successful
  attempt has exactly the distribution of the real view.
* Each attempt draws fresh verifier coins together with a fresh guess. GMR's machine `M` and
  GMW's simulator fix the verifier's random tape once and retry only the guess; for one round with
  a perfect special-HVZK simulator both work, and fixing the tape is what composing rounds needs.
* `simulatorK sim x Vstar k`: up to `k` independent attempts, outputting the first successful
  view or `none`. `winProb_simulatorK`: it outputs a view passing `T` with probability exactly
  `(1 - (1 - 1/|Ch|)^k) Pr[T holds of the real view]`. `abs_winProb_simulatorK_sub_le`
  (**zero knowledge against an arbitrary verifier, one round**): for every test `T`, counting a
  failed simulation as failing `T`, the two probabilities differ by at most `(1 - 1/|Ch|)^k`.
  (The same bound holds for tests that count a failure as passing, with gap
  `(1 - 1/|Ch|)^k (1 - Pr[T])`, so the statistical distance is at most `(1 - 1/|Ch|)^k`; that
  second case is not formalized.)

**Scope.** One round only; the composition over sequential rounds (with a verifier depending on
the earlier rounds), GMR's simulator that repeats until success (perfect, in expected polynomial
time), and auxiliary inputs are not formalized. With a large challenge set the number of attempts
needed grows with `|Ch|`, which is why this simulation is used for two-element challenge sets.

## References

* S. Goldwasser, S. Micali and C. Rackoff, *The knowledge complexity of interactive proof
  systems*, SIAM J. Comput. 18 (1989), 186-208, Section 5 (Theorem 1 and its proof).
* O. Goldreich, S. Micali and A. Wigderson, *Proofs that yield nothing but their validity or all
  languages in NP have zero-knowledge proof systems*, J. ACM 38 (1991), 691-729, proof of
  Theorem 2.
-/

@[expose] public section

namespace Cslib.Crypto.Identification

namespace SigmaProtocol

open Finset Cslib.Crypto.Framework

variable {X W K Cm Ch Z R : Type*} (P : SigmaProtocol X W K Cm Ch Z)
variable [Fintype K] [Nonempty K] [Fintype Ch] [Nonempty Ch] [Fintype R] [Nonempty R]

/-- **The view of an arbitrary verifier in one round**: the verifier `Vstar` chooses its challenge
as any function of the commitment and of its coins `r`; with uniform coins `r` and uniform prover
coins `k`, its view is `(r, commitment, answer)`. -/
noncomputable def realViewDist (x : X) (w : W) (Vstar : Cm → R → Ch) : PMF (R × Cm × Z) :=
  (Cslib.Probability.PMF.uniformOfFintype (R × K)).map fun ω =>
    (ω.1, P.commit x w ω.2, P.respond x w ω.2 (Vstar (P.commit x w ω.2) ω.1))

/-- **One rewinding attempt**: draw the verifier's coins `r` and a guess `e'` of its challenge,
let the per-challenge simulator `sim` produce `(a, z)` for `e'` from the statement alone, and
output whether the verifier's challenge on `a` is `e'`, together with the simulated view
`(r, a, z)`. -/
noncomputable def attemptDist [DecidableEq Ch] (sim : X → Ch → PMF (Cm × Z)) (x : X)
    (Vstar : Cm → R → Ch) : PMF (Bool × (R × Cm × Z)) :=
  (Cslib.Probability.PMF.uniformOfFintype (R × Ch)).bind fun ω =>
    (sim x ω.2).map fun az => (decide (Vstar az.1 ω.1 = ω.2), (ω.1, az.1, az.2))

omit [Nonempty K] in
/-- **One rewinding attempt simulates the real view** (Goldwasser, Micali and Rackoff, proof of
Theorem 1; Goldreich, Micali and Wigderson, proof of Theorem 2; exact form): for a perfect special
HVZK simulator, a statement with a witness, every verifier `Vstar` and every test `T` of its view,
`Pr[the attempt succeeds and T holds] = Pr[T holds of the real view] / |Ch|`. -/
theorem winProb_attemptDist [Nonempty K] [DecidableEq Ch] {sim : X → Ch → PMF (Cm × Z)}
    (hsim : P.SpecialHVZK sim) {x : X} {w : W} (hw : P.Rel x w) (Vstar : Cm → R → Ch)
    (T : R × Cm × Z → Bool) :
    winProb ((attemptDist sim x Vstar).map fun p => p.1 && T p.2) =
      winProb ((P.realViewDist x w Vstar).map T) / Fintype.card Ch := by
  classical
  have hatt : (attemptDist sim x Vstar).map (fun p => p.1 && T p.2) =
      (Cslib.Probability.PMF.uniformOfFintype (R × Ch × K)).map fun ω =>
        decide (Vstar (P.commit x w ω.2.2) ω.1 = ω.2.1) &&
          T (ω.1, P.commit x w ω.2.2, P.respond x w ω.2.2 ω.2.1) := by
    simp only [attemptDist, ← hsim x w hw, challengeTranscript, PMF.map_bind, PMF.map_comp,
      Function.comp_def]
    conv_rhs => rw [← Cslib.Probability.PMF.uniformOfFintype_map_equiv (Equiv.prodAssoc R Ch K),
      ← Cslib.Probability.PMF.uniformOfFintype_prod (R × Ch) K]
    simp only [PMF.map_comp, PMF.map_bind, Function.comp_def, Equiv.prodAssoc_apply]
  rw [hatt, realViewDist, PMF.map_comp, winProb_map_uniform, winProb_map_uniform]
  have hcard : (univ.filter fun ω : R × Ch × K =>
      (decide (Vstar (P.commit x w ω.2.2) ω.1 = ω.2.1) &&
        T (ω.1, P.commit x w ω.2.2, P.respond x w ω.2.2 ω.2.1)) = true).card =
      (univ.filter fun ω : R × K => (T ∘ fun ω : R × K =>
        (ω.1, P.commit x w ω.2, P.respond x w ω.2 (Vstar (P.commit x w ω.2) ω.1))) ω =
          true).card := by
    refine Finset.card_bij' (fun ω _ => (ω.1, ω.2.2))
      (fun ω _ => (ω.1, Vstar (P.commit x w ω.2) ω.1, ω.2)) ?_ ?_ ?_ ?_
    · rintro ⟨r, e, k⟩ h
      simp only [mem_filter, mem_univ, true_and, Bool.and_eq_true, decide_eq_true_eq,
        Function.comp] at h ⊢
      rw [h.1]
      exact h.2
    · rintro ⟨r, k⟩ h
      simp only [mem_filter, mem_univ, true_and, Bool.and_eq_true, decide_eq_true_eq,
        Function.comp] at h ⊢
      simpa using h
    · rintro ⟨r, e, k⟩ h
      simp only [mem_filter, mem_univ, true_and, Bool.and_eq_true, decide_eq_true_eq] at h
      simp [h.1]
    · rintro ⟨r, k⟩ -
      rfl
  rw [hcard, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod]
  push_cast
  have hC : (0 : ℝ) < Fintype.card Ch := by exact_mod_cast Fintype.card_pos
  field_simp

/-- **The rewinding simulator truncated after `k` attempts**: run independent attempts and output
the view of the first successful one, or `none` if all `k` attempts fail. -/
noncomputable def simulatorK [DecidableEq Ch] (sim : X → Ch → PMF (Cm × Z)) (x : X)
    (Vstar : Cm → R → Ch) : ℕ → PMF (Option (R × Cm × Z))
  | 0 => PMF.pure none
  | k + 1 => (attemptDist sim x Vstar).bind fun p =>
      if p.1 then PMF.pure (some p.2) else simulatorK sim x Vstar k

/-- **The truncated rewinding simulator reproduces the real view** (exact form): for a perfect
special HVZK simulator, a statement with a witness, every verifier and every test `T` of its view,
the simulator with `k` attempts outputs a view passing `T` with probability exactly
`(1 - (1 - 1/|Ch|)^k) Pr[T holds of the real view]`. -/
theorem winProb_simulatorK [DecidableEq Ch] {sim : X → Ch → PMF (Cm × Z)}
    (hsim : P.SpecialHVZK sim) {x : X} {w : W} (hw : P.Rel x w) (Vstar : Cm → R → Ch)
    (T : R × Cm × Z → Bool) (k : ℕ) :
    winProb ((simulatorK sim x Vstar k).map fun o => o.elim false T) =
      (1 - (1 - 1 / (Fintype.card Ch : ℝ)) ^ k) * winProb ((P.realViewDist x w Vstar).map T) := by
  have hatt := P.winProb_attemptDist hsim hw Vstar
  have hfail : winProb ((attemptDist sim x Vstar).map fun p => !p.1) =
      1 - 1 / (Fintype.card Ch : ℝ) := by
    have h1 := hatt fun _ => true
    have hone : winProb ((P.realViewDist x w Vstar).map fun _ => true) = 1 := by
      rw [show ((P.realViewDist x w Vstar).map fun _ => true) = PMF.pure true from
        PMF.map_const _ true, winProb_pure]
      rfl
    have hsplit : winProb ((attemptDist sim x Vstar).map fun p => !p.1) =
        1 - winProb ((attemptDist sim x Vstar).map fun p => p.1 && true) := by
      rw [← toReal_apply_false, winProb]
      simp only [PMF.map_apply, Bool.and_true]
      congr 1
      refine tsum_congr fun p => ?_
      cases p.1 <;> simp
    rw [hsplit, h1, hone]
  induction k with
  | zero =>
    rw [simulatorK, PMF.pure_map]
    simp
  | succ k ih =>
    have hbind : ((simulatorK sim x Vstar (k + 1)).map fun o => o.elim false T) true =
        ((attemptDist sim x Vstar).map fun p => p.1 && T p.2) true +
          ((attemptDist sim x Vstar).map fun p => !p.1) true *
            ((simulatorK sim x Vstar k).map fun o => o.elim false T) true := by
      have hmap : ∀ p : Bool × (R × Cm × Z),
          (if p.1 then PMF.pure (some p.2) else simulatorK sim x Vstar k).map
            (fun o => o.elim false T) =
          if p.1 then PMF.pure (T p.2)
            else (simulatorK sim x Vstar k).map fun o => o.elim false T := by
        intro p
        split <;> simp [PMF.pure_map]
      simp only [simulatorK, PMF.map_bind, hmap, PMF.bind_apply]
      rw [PMF.map_apply, PMF.map_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
      refine tsum_congr fun p => ?_
      obtain ⟨b, v⟩ := p
      cases b
      · simp
      · simp [PMF.pure_apply]
    have hreal := congrArg ENNReal.toReal hbind
    rw [ENNReal.toReal_add (PMF.apply_ne_top _ _)
      (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)),
      ENNReal.toReal_mul] at hreal
    change winProb _ = winProb _ + winProb _ * winProb _ at hreal
    rw [hreal, hatt, hfail, ih]
    ring

/-- **Zero knowledge against an arbitrary verifier, one round**: for a perfect special
HVZK simulator and a statement with a witness, the truncated rewinding simulator with `k` attempts
(which never sees the witness) and the real interaction produce views passing any test `T` with
probabilities that differ by at most `(1 - 1/|Ch|)^k`, a failed simulation counting as failing
`T`. -/
theorem abs_winProb_simulatorK_sub_le [DecidableEq Ch] {sim : X → Ch → PMF (Cm × Z)}
    (hsim : P.SpecialHVZK sim) {x : X} {w : W} (hw : P.Rel x w) (Vstar : Cm → R → Ch)
    (T : R × Cm × Z → Bool) (k : ℕ) :
    |winProb ((simulatorK sim x Vstar k).map fun o => o.elim false T) -
        winProb ((P.realViewDist x w Vstar).map T)| ≤ (1 - 1 / (Fintype.card Ch : ℝ)) ^ k := by
  rw [P.winProb_simulatorK hsim hw Vstar T k]
  have h0 := winProb_nonneg ((P.realViewDist x w Vstar).map T)
  have h1 := winProb_le_one ((P.realViewDist x w Vstar).map T)
  have hC : (1 : ℝ) ≤ Fintype.card Ch := by exact_mod_cast Fintype.card_pos
  have hq0 : 0 ≤ 1 - 1 / (Fintype.card Ch : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]; exact hC
  have hpow : 0 ≤ (1 - 1 / (Fintype.card Ch : ℝ)) ^ k := pow_nonneg hq0 k
  rw [show (1 - (1 - 1 / (Fintype.card Ch : ℝ)) ^ k) * winProb ((P.realViewDist x w Vstar).map T)
      - winProb ((P.realViewDist x w Vstar).map T) =
      -((1 - 1 / (Fintype.card Ch : ℝ)) ^ k * winProb ((P.realViewDist x w Vstar).map T)) by
      ring, abs_neg, abs_of_nonneg (mul_nonneg hpow h0)]
  nlinarith

end SigmaProtocol

end Cslib.Crypto.Identification
