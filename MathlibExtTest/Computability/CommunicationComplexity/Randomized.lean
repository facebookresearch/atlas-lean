/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.CommunicationComplexity.Randomized

/-!
# Tests for public-coin communication protocols
-/

namespace MathlibExtTest.Computability.CommunicationComplexity

open MathlibExt.Computability.CommunicationComplexity
open MathlibExt.Computability.CommunicationComplexity.Protocol

/-- The random-hash protocol with one-bit hashes errs with probability `1 / 2` on distinct
one-bit inputs, and costs at most two bits. -/
example : (eqHashProtocol 1 1).errorProb (eqFn 1) (fun _ => false) (fun _ => true) = 1 / 2 := by
  rw [errorProb_eqHashProtocol_of_ne]
  · norm_num
  · intro h; simpa using congrFun h 0

example : (eqHashProtocol 1 1).cost ≤ 2 := cost_eqHashProtocol_le 1 1

/-- With `k = 0` hash bits the protocol always answers "equal": error `1` on distinct inputs. -/
example : (eqHashProtocol 2 0).errorProb (eqFn 2) (fun _ => false) (fun _ => true) = 1 := by
  rw [errorProb_eqHashProtocol_of_ne]
  · norm_num
  · intro h; simpa using congrFun h 0

/-- The hypotheses of `newman_private_coins` are jointly satisfiable at the largest
allowed error `ε = 1 / 2`: the random-hash protocol with one-bit hashes on one-bit inputs, with a
nonempty set of random strings, has error at most `1 / 2` on every input. -/
example : ∀ x y : Fin 1 → Bool, ((eqHashProtocol 1 1).errorProb (eqFn 1) x y : ℝ) ≤ 1 / 2 := by
  intro x y
  by_cases h : x = y
  · subst h; rw [errorProb_eqHashProtocol_self]; norm_num
  · rw [errorProb_eqHashProtocol_of_ne h]; norm_num

example : Nonempty ((Fin 1 → Bool) → Fin 1 → Bool) := ⟨fun _ _ => false⟩

/-! The error probability needs a nonempty set of random strings: for an empty set, on which
every event would have probability `0`, it does not elaborate. -/

/--
error: failed to synthesize instance of type class
  Nonempty Empty

Hint: Adding the command `deriving instance Nonempty for Empty` may allow Lean to derive the missing instance.
-/
#guard_msgs in
noncomputable example : ℚ :=
  (⟨fun _ => .output false⟩ : PublicCoinProtocol (Fin 1 → Bool) (Fin 1 → Bool) Empty).errorProb
    (fun _ _ => true) (fun _ => false) (fun _ => false)

/-- Guard for the error range of `newman_private_coins`: without the bound `ε ≤ 1 / 2` the
statement is false, since for large `ε` the cost-0 constant protocol meets the hypothesis while
`log₂(n / ε²)` is negative. (Counterexample found by the reviewer of this change set.) -/
def NewmanWithoutErrorBound : Prop :=
  ∃ C₀ : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε →
    ∀ (g : (Fin n → Bool) → (Fin n → Bool) → Bool) (R : Type) [Fintype R] [Nonempty R]
      (P : PublicCoinProtocol (Fin n → Bool) (Fin n → Bool) R),
      (∀ x y, (P.errorProb g x y : ℝ) ≤ ε) →
      ∃ (RA RB : Type) (_ : Fintype RA) (_ : Fintype RB) (_ : Nonempty RA) (_ : Nonempty RB)
        (p : Protocol ((Fin n → Bool) × RA) ((Fin n → Bool) × RB)),
        (p.depth : ℝ) ≤ P.cost + Real.logb 2 (n / ε ^ 2) + C₀

theorem not_newmanWithoutErrorBound : ¬ NewmanWithoutErrorBound := by
  rintro ⟨C₀, h⟩
  set ε : ℝ := (2 : ℝ) ^ (|C₀| + 1) with hε
  have hεpos : 0 < ε := by positivity
  let P : PublicCoinProtocol (Fin 1 → Bool) (Fin 1 → Bool) Unit := ⟨fun _ => .output false⟩
  have herr : ∀ x y, (P.errorProb (fun _ _ => false) x y : ℝ) ≤ ε := by
    intro x y
    have h1 : (1 : ℝ) ≤ ε := by
      rw [hε]; exact Real.one_le_rpow (by norm_num) (by positivity)
    simp [P, PublicCoinProtocol.errorProb, Protocol.eval]
    linarith
  obtain ⟨RA, RB, _, _, _, _, p, hp⟩ := h 1 le_rfl ε hεpos _ Unit P herr
  have hcost : P.cost = 0 := by simp [P, PublicCoinProtocol.cost, Protocol.depth]
  have hlog : Real.logb 2 ((1 : ℕ) / ε ^ 2) = -2 * (|C₀| + 1) := by
    rw [hε, Nat.cast_one, one_div, Real.logb_inv, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num), Real.logb_rpow (by norm_num) (by norm_num)]
    push_cast; ring
  rw [hcost, hlog] at hp
  have : (0 : ℝ) ≤ p.depth := Nat.cast_nonneg _
  have hC : C₀ ≤ |C₀| := le_abs_self C₀
  have hC2 : 0 ≤ |C₀| := abs_nonneg C₀
  simp only [Nat.cast_zero] at hp
  linarith

end MathlibExtTest.Computability.CommunicationComplexity
