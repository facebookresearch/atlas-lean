/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.PublicKey.SemanticSecurity

/-!
# Tests for semantic security and indistinguishability

Two extreme one-bit schemes make the definitions non-vacuous.
* `blind`: the ciphertext is always `()`. Its encryptions are identical, so it has
  indistinguishable encryptions with error `0` and, by Goldreich's Proposition 5.2.6, is
  semantically secure with error `0`.
* `clear`: the ciphertext is the plaintext. The distinguisher that outputs the ciphertext has
  advantage `1`, so `clear` is not `IndSecure` with any error `ε < 1`, and by Proposition 5.2.7
  it is not semantically secure with any error `ε < 1/2`. `clear` is correct, so the general
  impossibility `not_indSecure_of_correct` applies to it (as to every correct public-key scheme).
-/

@[expose] public section

namespace Cslib.Crypto.SemanticSecurityTests

open Cslib.Crypto.Framework Cslib.Crypto.PublicKey.SemanticSecurity

/-- The scheme whose ciphertext carries no information. -/
noncomputable def blind : PKEScheme Bool Unit Unit Unit where
  gen := PMF.pure ((), ())
  enc _ _ := PMF.pure ()
  dec _ _ := none

/-- The scheme whose ciphertext is the plaintext. -/
noncomputable def clear : PKEScheme Bool Unit Unit Bool where
  gen := PMF.pure ((), ())
  enc _ m := PMF.pure m
  dec _ c := some c

theorem blind_indSecure : IndSecure blind (fun _ => 0) (PMF.pure ()) 0 := by
  intro D m m' _
  simp [indAdvantage, indExp, blind]

example : SemanticallySecure blind (fun _ => 0) (PMF.pure ()) Bool Bool 0 :=
  semanticallySecure_of_indSecure blind le_rfl (fun _ => false) (fun _ => rfl) blind_indSecure
    Bool Bool

theorem clear_indAdvantage :
    indAdvantage clear (PMF.pure ()) (fun _ c _ => c) false true = 1 := by
  simp [indAdvantage, indExp, clear, advantage, winProb]

example {ε : ℝ} (hε : ε < 1) : ¬ IndSecure clear (fun _ => 0) (PMF.pure ()) ε := fun h => by
  have := h (fun _ c _ => c) false true rfl
  rw [clear_indAdvantage] at this
  linarith

example {ε : ℝ} (hε₀ : 0 ≤ ε) (hε : ε < 1 / 2) :
    ¬ SemanticallySecure clear (fun _ => 0) (PMF.pure ()) Unit Bool ε := fun h => by
  have := (indSecure_of_semanticallySecure clear hε₀ h) (fun _ c _ => c) false true rfl
  rw [clear_indAdvantage] at this
  linarith

/-- `clear` is correct, so the general impossibility applies to it. -/
theorem clear_correct : clear.Correct := by
  intro kp _ m c hc
  simp only [clear, PMF.support_pure, Set.mem_singleton_iff] at hc
  simp [clear, hc]

example {ε : ℝ} (hε : ε < 1) : ¬ IndSecure clear (fun _ => 0) (PMF.pure ()) ε :=
  not_indSecure_of_correct clear clear_correct _ (m := false) (m' := true) (by decide) rfl hε

/-- `PubK^eav` with fixed messages is the indistinguishability experiment. -/
example (b : Bool) :
    pubCpaExp clear ⟨PMF.pure (), fun _ _ => (false, true), fun _ c _ => c⟩ b =
      indExp clear (PMF.pure ()) (fun _ c _ => c) (pick (false, true) b) :=
  pubCpaExp_eq_indExp clear _ (fun _ _ => rfl) b

end Cslib.Crypto.SemanticSecurityTests
