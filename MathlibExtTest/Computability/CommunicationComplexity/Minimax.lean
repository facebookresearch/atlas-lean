/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.CommunicationComplexity.Minimax

/-!
# Tests for Yao's minimax principle for communication complexity
-/

namespace MathlibExtTest.Computability.CommunicationComplexity.Minimax

open MathlibExt.Computability.CommunicationComplexity Convexity
open MathlibExt.Computability.CommunicationComplexity.Protocol

/-- Equality of one-bit strings: error `1 / 2` with two bits of randomized communication. -/
example : randComplexity (eqFn 1) (1 / 2) ≤ 2 := by
  simpa using randComplexity_eqFn_le 1 1

/-- Equality of `100`-bit strings with error `1 / 1024` in at most `11` bits, against `101`
bits deterministically. -/
example : randComplexity (eqFn 100) (1 / 2 ^ 10) ≤ 11 := randComplexity_eqFn_le 100 10

example : commComplexity (eqFn 100) = 101 := commComplexity_eqFn (by norm_num)

/-- The minimax principle applied to equality of one-bit strings with error `1 / 2`. -/
example : randComplexity (eqFn 1) (1 / 2) =
    ⨆ μ : StdSimplex ℝ ((Fin 1 → Bool) × (Fin 1 → Bool)), distComplexity (eqFn 1) μ (1 / 2) :=
  randComplexity_eq_iSup_distComplexity _ (by norm_num)

/-- Against the uniform distribution on pairs of one-bit strings, error `1 / 2` costs at most two
bits deterministically. -/
example : distComplexity (eqFn 1) (StdSimplex.barycenter (K := ℝ)) (1 / 2) ≤ 2 :=
  (distComplexity_le_randComplexity _ _ (by norm_num)).trans (by
    simpa using randComplexity_eqFn_le 1 1)

/-- The random-hash protocol, viewed as a randomized protocol, keeps its error `1 / 2` on
distinct one-bit inputs. -/
example : (eqHashProtocol 1 1).toRandomized.error (eqFn 1) (fun _ => false) (fun _ => true) =
    1 / 2 := by
  rw [PublicCoinProtocol.error_toRandomized, errorProb_eqHashProtocol_of_ne]
  · norm_num
  · intro h; simpa using congrFun h 0

/-- With error `0` every protocol in the support of a randomized protocol is exact. -/
theorem computes_of_error_eq_zero {X Y : Type*} {f : X → Y → Bool} (P : RandomizedProtocol X Y)
    (h : ∀ x y, P.error f x y ≤ 0) {p : Protocol X Y} (hp : p ∈ P.weights.support) :
    p.Computes f := by
  intro x y
  by_contra hne
  have hpos : 0 < P.weights p :=
    lt_of_le_of_ne (P.weights_nonneg p) (Ne.symm (Finsupp.mem_support_iff.1 hp))
  have hterm : P.weights p * errorIndicator p f x y ≤ P.error f x y := by
    unfold RandomizedProtocol.error Finsupp.sum
    exact Finset.single_le_sum (f := fun q => P.weights q * errorIndicator q f x y)
      (fun q _ => mul_nonneg (P.weights_nonneg q) (by unfold errorIndicator; split_ifs <;> norm_num))
      hp
  have h1 : errorIndicator p f x y = 1 := by simp [errorIndicator, hne]
  rw [h1, mul_one] at hterm
  linarith [h x y]

/-- A concrete positive value on both sides of Yao's minimax principle for communication: exact
randomized protocols for equality of one-bit strings need two bits, as deterministic ones do. -/
theorem randComplexity_eqFn_one_zero : randComplexity (eqFn 1) 0 = 2 := by
  refine le_antisymm ?_ ?_
  · refine Nat.sInf_le ⟨StdSimplex.single (eqProtocol 1), ?_, fun x y => ?_⟩
    · simpa [RandomizedProtocol.cost] using depth_eqProtocol_le 1
    · simp [RandomizedProtocol.error, errorIndicator, eqProtocol_computes 1 x y]
  · obtain ⟨P, hcost, herr⟩ := Nat.sInf_mem
      (s := {c | ∃ P : RandomizedProtocol (Fin 1 → Bool) (Fin 1 → Bool),
        P.cost ≤ c ∧ ∀ x y, P.error (eqFn 1) x y ≤ 0})
      ⟨_, StdSimplex.single (eqProtocol 1), le_rfl, fun x y => by
        simp [RandomizedProtocol.error, errorIndicator, eqProtocol_computes 1 x y]⟩
    obtain ⟨p, hp⟩ := P.support_weights_nonempty
    have h₁ := lt_depth_of_computes_eqFn le_rfl (computes_of_error_eq_zero P herr hp)
    have h₂ : p.depth ≤ P.cost := Finset.le_sup (f := Protocol.depth) hp
    unfold randComplexity
    omega

example : (⨆ μ : StdSimplex ℝ ((Fin 1 → Bool) × (Fin 1 → Bool)),
    distComplexity (eqFn 1) μ 0) = 2 := by
  rw [← randComplexity_eq_iSup_distComplexity _ le_rfl, randComplexity_eqFn_one_zero]

end MathlibExtTest.Computability.CommunicationComplexity.Minimax
