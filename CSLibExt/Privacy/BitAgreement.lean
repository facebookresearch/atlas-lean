/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.ApproximateDifferentialPrivacy
public import MathlibExt.Analysis.Fourier.BooleanCube
public import MathlibExt.Probability.ProbabilityMassFunction.Expectation
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.InformationTheory.Hamming
import CSLibExt.Privacy.HypothesisTesting
import MathlibExt.Analysis.Fourier.BooleanCubeInfluence
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Expected agreement on a private Boolean cube

Choose a uniform input word `x`, then draw one output word from `G x`.
Flipping input bit `i` exchanges agreement and disagreement at `i` while
preserving the uniform average. Event privacy on this pair therefore bounds
the mean number of agreements. The output bits need not be independent.

Dwork and Roth, *The Algorithmic Foundations of Differential Privacy* (2014),
§2.3, Definition 2.4 (pp. 17–18) and Proposition 2.1 (p. 19), give the event
inequality and postprocessing principle. The count bound below is deduced
for fixed-length rows with `ReplaceOne`, not for histogram add/remove adjacency.
-/

@[expose] public section

namespace CSLibExt.Privacy.DifferentialPrivacy

open BooleanCube
open scoped BigOperators

variable {n : ℕ} {G : BoolCube n → PMF (BoolCube n)} {ε δ : ℝ}

/-- The mean number of matching coordinates of a uniform Boolean input word and
one output word drawn conditionally from `G` at that input. -/
noncomputable def expectedBitAgreement (G : BoolCube n → PMF (BoolCube n)) : ℝ :=
  𝔼 x, (G x).expect fun y => ∑ i, if y i = x i then 1 else 0

private def bitEvent (i : Fin n) (b : Bool) : Finset (BoolCube n) :=
  Finset.univ.filter fun y => y i = b

private noncomputable def matchMass (G : BoolCube n → PMF (BoolCube n))
    (i : Fin n) (x : BoolCube n) : ℝ :=
  ∑ y ∈ bitEvent i (x i), (G x y).toReal

private theorem matchMass_le_flip (h : IsApproxDP G ReplaceOne ε δ)
    (i : Fin n) (x : BoolCube n) :
    matchMass G i x ≤ Real.exp ε * (1 - matchMass G i (flipCoord x i)) + δ := by
  have adj : ReplaceOne x (flipCoord x i) := by
    have only_i {j : Fin n} (hj : x j ≠ flipCoord x i j) : j = i :=
      by_contra fun hji => hj (flipCoord_apply_of_ne x hji).symm
    exact fun _ hj _ hk => (only_i hj).trans (only_i hk).symm
  have hd := (HypothesisTesting.isApproxDPFin_iff_isApproxDP _ _ G ReplaceOne ε δ).mpr h
  have hc : (bitEvent i (x i))ᶜ = bitEvent i (flipCoord x i i) := by
    ext y
    simp only [Finset.mem_compl, bitEvent, Finset.mem_filter, Finset.mem_univ, true_and,
      flipCoord_apply_self]
    cases x i <;> cases y i <;> decide
  have hs := HypothesisTesting.pmf_sum_add_compl _ (G (flipCoord x i)) (bitEvent i (x i))
  rw [hc] at hs
  exact (hd.2.2 x (flipCoord x i) adj (bitEvent i (x i))).trans_eq (by
    unfold matchMass
    rw [eq_sub_of_add_eq hs])

private theorem mean_matchMass_le (h : IsApproxDP G ReplaceOne ε δ) (i : Fin n) :
    (𝔼 x, matchMass G i x) ≤ (Real.exp ε + δ) / (1 + Real.exp ε) := by
  have hab := Finset.expect_le_expect (s := Finset.univ) fun x _ => matchMass_le_flip h i x
  rw [Finset.expect_add_distrib, ← Finset.mul_expect, Finset.expect_sub_distrib,
    expect_comp_flipCoord] at hab
  simp only [Finset.expect_const, Finset.univ_nonempty] at hab
  apply (le_div_iff₀ (by positivity)).mpr
  linarith only [hab]

/-- An `(ε, δ)`-private PMF mechanism for replacement of one bit agrees with a
uniform input on at most `n * (exp ε + δ) / (1 + exp ε)` coordinates in expectation.
The bound includes the empty cube and assumes no independence among output bits. -/
theorem expectedBitAgreement_le (h : IsApproxDP G ReplaceOne ε δ) :
    expectedBitAgreement G ≤ n * (Real.exp ε + δ) / (1 + Real.exp ε) := by
  unfold expectedBitAgreement
  simp_rw [PMF.expect_sum, PMF.expect_indicator_decide]
  rw [Finset.expect_sum_comm]
  calc
    ∑ i, (𝔼 x, matchMass G i x) ≤ ∑ _ : Fin n, (Real.exp ε + δ) / (1 + Real.exp ε) :=
      Finset.sum_le_sum fun i _ => mean_matchMass_le h i
    _ = _ := by simp [mul_div_assoc]

/-- Let `x` be uniform on the `n`-bit cube and draw one word `y` from `G x`.
If `G` is `(ε, δ)`-differentially private for one-coordinate replacement,
the expected Hamming distance between `x` and `y` is at least `n * (1 - δ) / (1 + exp ε)`. -/
theorem le_expectedHammingDist (h : IsApproxDP G ReplaceOne ε δ) :
    n * (1 - δ) / (1 + Real.exp ε) ≤ 𝔼 x, (G x).expect fun y => (hammingDist x y : ℝ) := by
  have hc (x y : BoolCube n) : (hammingDist x y : ℝ) +
      (∑ i, if y i = x i then (1 : ℝ) else 0) = n := by
    simp only [hammingDist, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, ← Finset.sum_add_distrib]
    trans ∑ _ : Fin n, (1 : ℝ)
    · exact Finset.sum_congr rfl fun i _ => by by_cases hi : y i = x i <;> simp_all [eq_comm]
    · simp
  have he : (𝔼 x, (G x).expect fun y => (hammingDist x y : ℝ)) + expectedBitAgreement G = n := by
    unfold expectedBitAgreement
    rw [← Finset.expect_add_distrib]
    simp_rw [← PMF.expect_add]
    change (𝔼 x, (G x).expect fun y => (hammingDist x y : ℝ) +
      ∑ i, if y i = x i then (1 : ℝ) else 0) = n
    simp only [hc, PMF.expect_const, Fintype.expect_const]
  have ha := expectedBitAgreement_le h
  have hp : 0 < 1 + Real.exp ε := by positivity
  have ha' := (le_div_iff₀ hp).mp ha
  apply (div_le_iff₀ hp).mpr
  nlinarith only [ha', he, congrArg (· * (1 + Real.exp ε)) he]

/-- Sample a discrete release `M x` on a uniform `n`-bit input `x`, then draw one
word using a randomized postprocessor `k` that sees only the release. If this word
matches `x` on more than `n * (exp ε + δ) / (1 + exp ε)` coordinates in expectation,
`M` is not `(ε, δ)`-differentially private for one-coordinate replacement. -/
theorem not_isApproxDP_of_lt_expectedBitAgreement_bind {A : Type*}
    (M : BoolCube n → PMF A) (k : A → PMF (BoolCube n))
    (h : n * (Real.exp ε + δ) / (1 + Real.exp ε) <
      expectedBitAgreement (fun x => (M x).bind k)) : ¬IsApproxDP M ReplaceOne ε δ :=
  fun hM => h.not_ge (expectedBitAgreement_le (isApproxDP_bind hM k))

end CSLibExt.Privacy.DifferentialPrivacy
