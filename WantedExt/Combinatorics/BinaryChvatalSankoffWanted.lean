/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Algorithms.Lean.DynamicProgramming.LongestCommonSubsequence
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Subadditive
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.LiminfLimsup

@[expose] public section

open scoped BigOperators

namespace MathlibExt.Combinatorics.BinaryChvatalSankoffWanted

/-!
# Binary Chvátal--Sankoff constant and catalogue bounds

Source: Optimization Problems, `constants/31a.md`, at revision
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`; Chvátal and Sankoff,
*Longest common subsequences of two random sequences* (1975), 306--315;
Dančík (1994); Dančík and Paterson (1995); Lueker (2009);
Heineman et al., arXiv:2407.10925v1 (2024).

The constant is the limit of the expected LCS length of two independent
uniform binary strings, divided by their length. Finite-level bounds and
superadditivity prove ordinary-limit existence. The deep numerical bounds
below are proof requests, not axioms or completed proofs. Their terminating
decimals are exact rational endpoints, as in the frozen catalogue.

The catalogue's additional `0.79970` claim is explicitly AI and computer
assisted (unverified). Its proposition is recorded separately; no proof or
current resolution status is asserted. Historical computational certificates
are not replayed here. The source specifies no conjectured exact value, so
these known bounds are not registered as open conjectures.
-/

noncomputable section


/-- A binary string with exactly `n` ordered coordinates. -/
abbrev BinaryString (n : ℕ) := Fin n → Bool

/-- An ordered pair of binary strings, the finite sample space for the source
expectation. -/
abbrev BinaryStringPair (n : ℕ) := BinaryString n × BinaryString n

/-- `z` is an order-preserving common subsequence of the two binary strings.
Using `List.Sublist` retains repeated symbols and their multiplicities. -/
def IsCommonSubsequence {n : ℕ} (z : List Bool)
    (x y : BinaryString n) : Prop :=
  z.Sublist (List.ofFn x) ∧ z.Sublist (List.ofFn y)

/-- The lengths admitted by common subsequences of `x` and `y`. -/
def commonSubsequenceLengths {n : ℕ} (x y : BinaryString n) : Set ℕ :=
  {k | ∃ z : List Bool, IsCommonSubsequence z x y ∧ z.length = k}

/-- The longest-common-subsequence length, computed by the proved CSLib
dynamic-programming implementation. -/
def lcsLength {n : ℕ} (x y : BinaryString n) : ℕ :=
  (Cslib.Algorithms.Lean.longestCommonSubsequence
    (List.ofFn x) (List.ofFn y)).ret.1

/-- `lcsLength` is attained and is the maximum common-subsequence length. -/
theorem lcsLength_isGreatest {n : ℕ} (x y : BinaryString n) :
    IsGreatest (commonSubsequenceLengths x y) (lcsLength x y) := by
  let result := (Cslib.Algorithms.Lean.longestCommonSubsequence
    (List.ofFn x) (List.ofFn y)).ret
  have h := Cslib.Algorithms.Lean.longestCommonSubsequence_correct
    (List.ofFn x) (List.ofFn y)
  change result.2.length = result.1 ∧
    result.2.Sublist (List.ofFn x) ∧ result.2.Sublist (List.ofFn y) ∧
      (∀ z : List Bool, z.Sublist (List.ofFn x) → z.Sublist (List.ofFn y) →
        z.length ≤ result.2.length) at h
  constructor
  · exact ⟨result.2, ⟨h.2.1, h.2.2.1⟩, h.1⟩
  · intro k hk
    obtain ⟨z, hz, rfl⟩ := hk
    change z.length ≤ result.1
    exact (h.2.2.2 z hz.1 hz.2).trans_eq h.1

/-- A longest common subsequence exists with the reported length, and every
other common subsequence is no longer. -/
theorem exists_longestCommonSubsequence {n : ℕ} (x y : BinaryString n) :
    ∃ z : List Bool,
      IsCommonSubsequence z x y ∧ z.length = lcsLength x y ∧
        ∀ w : List Bool, IsCommonSubsequence w x y → w.length ≤ z.length := by
  obtain ⟨z, hz, hlen⟩ := (lcsLength_isGreatest x y).1
  exact ⟨z, hz, hlen, fun w hw =>
    (lcsLength_isGreatest x y).2 ⟨w, hw, rfl⟩ |>.trans_eq hlen.symm⟩

/-- No common subsequence is longer than either input string. -/
theorem lcsLength_le {n : ℕ} (x y : BinaryString n) : lcsLength x y ≤ n := by
  obtain ⟨z, hz, hlen, _⟩ := exists_longestCommonSubsequence x y
  rw [← hlen]
  simpa using hz.1.length_le

/-- Mathematical `Nat.findGreatest` characterization used to export proof
tasks without depending on the CSLib implementation module. -/
theorem lcsLength_eq_findGreatest {n : ℕ} (x y : BinaryString n) :
    lcsLength x y =
      (by
        classical
        exact Nat.findGreatest (fun k => k ∈ commonSubsequenceLengths x y) n) := by
  classical
  apply le_antisymm
  · exact Nat.le_findGreatest (lcsLength_le x y) (lcsLength_isGreatest x y).1
  · apply (lcsLength_isGreatest x y).2
    apply Nat.findGreatest_spec (m := 0) (n := n)
    · exact Nat.zero_le _
    · exact ⟨[], by simp [IsCommonSubsequence], rfl⟩

/-- All ordered pairs of length-`n` binary strings. -/
def uniformBinaryStringPairs (n : ℕ) : Finset (BinaryStringPair n) :=
  Finset.univ

/-- The exact uniform expectation of LCS length over the finite product sample
space. Each ordered pair has weight `1 / |BinaryStringPair n|`. -/
def expectedLCSLength (n : ℕ) : ℝ :=
  (∑ pair ∈ uniformBinaryStringPairs n,
      (lcsLength pair.1 pair.2 : ℝ)) /
    (Fintype.card (BinaryStringPair n) : ℝ)

/-- Expected LCS length is nonnegative. -/
theorem expectedLCSLength_nonneg (n : ℕ) : 0 ≤ expectedLCSLength n := by
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro pair _
    exact Nat.cast_nonneg _
  · exact Nat.cast_nonneg _

/-- Expected LCS length is at most the common input length. -/
theorem expectedLCSLength_le (n : ℕ) : expectedLCSLength n ≤ n := by
  have hcard : (0 : ℝ) < Fintype.card (BinaryStringPair n) :=
    Nat.cast_pos.mpr Fintype.card_pos
  rw [expectedLCSLength, div_le_iff₀ hcard]
  calc
    (∑ pair ∈ uniformBinaryStringPairs n,
        (lcsLength pair.1 pair.2 : ℝ)) ≤
        ∑ _pair ∈ uniformBinaryStringPairs n, (n : ℝ) := by
      apply Finset.sum_le_sum
      intro pair _
      exact Nat.cast_le.mpr (lcsLength_le pair.1 pair.2)
    _ = (n : ℝ) * Fintype.card (BinaryStringPair n) := by
      simp [uniformBinaryStringPairs, mul_comm]

/-- The normalized expectation, with the irrelevant initial index made
explicit instead of relying on totalized `0 / 0`. -/
def normalizedExpectedLCS (n : ℕ) : ℝ :=
  if n = 0 then 0 else expectedLCSLength n / (n : ℝ)

/-- Every normalized expectation lies in the source's trivial interval
`[0,1]`. -/
theorem normalizedExpectedLCS_mem_Icc (n : ℕ) :
    normalizedExpectedLCS n ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hn : n = 0
  · simp [normalizedExpectedLCS, hn]
  · simp only [normalizedExpectedLCS, hn, ↓reduceIte]
    constructor
    · exact div_nonneg (expectedLCSLength_nonneg n) (Nat.cast_nonneg n)
    · rw [div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
      exact expectedLCSLength_le n

/-- The bounded real liminf of normalized expectations. The source's ordinary
limit-existence theorem below identifies this value with the ordinary limit;
unlike `Filter.limUnder`, this definition does not select an arbitrary fallback
when convergence has not yet been supplied. -/
noncomputable def binaryChvatalSankoffConstant : ℝ :=
  Filter.liminf normalizedExpectedLCS Filter.atTop

/-- Source notation `C₃₁ₐ`. -/
noncomputable abbrev C31a : ℝ :=
  binaryChvatalSankoffConstant

/-- Chvátal and Sankoff's source-reported theorem that the ordinary limit
exists. -/
def chvatalSankoffLimitExists : Prop :=
  ∃ c : ℝ, Filter.Tendsto normalizedExpectedLCS Filter.atTop (nhds c)

/-- The bounded liminf lies in the source's trivial interval `[0,1]`. -/
theorem binaryChvatalSankoffConstant_mem_Icc :
    C31a ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · apply Filter.le_liminf_of_le
      ((Filter.isBoundedUnder_of_eventually_le
        (Filter.Eventually.of_forall fun n =>
          (normalizedExpectedLCS_mem_Icc n).2)).isCoboundedUnder_flip)
    exact Filter.Eventually.of_forall fun n => (normalizedExpectedLCS_mem_Icc n).1
  · apply Filter.liminf_le_of_frequently_le
    · exact Filter.Frequently.of_forall fun n => (normalizedExpectedLCS_mem_Icc n).2
    · exact Filter.isBoundedUnder_of_eventually_ge
        (Filter.Eventually.of_forall fun n => (normalizedExpectedLCS_mem_Icc n).1)

/-- The trivial exact upper endpoint `C₃₁ₐ ≤ 1`. -/
def trivialUpperBound : Prop :=
  C31a ≤ 1

/-- Dančík--Paterson's exact upper endpoint `0.837623`. -/
def dancikPatersonUpperBound : Prop :=
  C31a ≤ (837623 : ℝ) / 1000000

/-- Lueker's computer-assisted exact upper endpoint `0.826280`. -/
def luekerUpperBound : Prop :=
  C31a ≤ (826280 : ℝ) / 1000000

/-- The trivial exact lower endpoint `0 ≤ C₃₁ₐ`. -/
def trivialLowerBound : Prop :=
  0 ≤ C31a

/-- Chvátal--Sankoff's strict positive lower bound. -/
def chvatalSankoffStrictPositive : Prop :=
  0 < C31a

/-- Dančík's computer-assisted exact lower endpoint `0.773911`. -/
def dancikLowerBound : Prop :=
  (773911 : ℝ) / 1000000 ≤ C31a

/-- Lueker's computer-assisted exact lower endpoint `0.788071`. -/
def luekerLowerBound : Prop :=
  (788071 : ℝ) / 1000000 ≤ C31a

/-- Heineman et al.'s computer-assisted exact lower endpoint `0.792665992`. -/
def heinemanLowerBound : Prop :=
  (792665992 : ℝ) / 1000000000 ≤ C31a

/-- The source-reported 2026 claim `0.79970 ≤ C₃₁ₐ`, explicitly marked
AI and computer assisted (unverified). This declaration records the claim and
does not verify or prove it. -/
def sourceReportedUnverified2026LowerBound : Prop :=
  (79970 : ℝ) / 100000 ≤ C31a

/-- Source: uniform independent binary-string model; concatenation
identifies two independent pairs with a pair of the combined length. -/
def appendBinaryStringPairEquiv (m n : ℕ) :
    BinaryStringPair m × BinaryStringPair n ≃ BinaryStringPair (m + n) where
  toFun pair :=
    ((Fin.appendEquiv m n) (pair.1.1, pair.2.1),
      (Fin.appendEquiv m n) (pair.1.2, pair.2.2))
  invFun pair :=
    ((((Fin.appendEquiv m n).symm pair.1).1,
      ((Fin.appendEquiv m n).symm pair.2).1),
      (((Fin.appendEquiv m n).symm pair.1).2,
      ((Fin.appendEquiv m n).symm pair.2).2))
  left_inv pair := by
    rcases pair with ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩
    simp
  right_inv pair := by
    rcases pair with ⟨x, y⟩
    apply Prod.ext
    · exact (Fin.appendEquiv m n).apply_symm_apply x
    · exact (Fin.appendEquiv m n).apply_symm_apply y

/-- Source: common subsequences concatenate without changing their order. -/
theorem lcsLength_append_le {m n : ℕ}
    (x₁ y₁ : BinaryString m) (x₂ y₂ : BinaryString n) :
    lcsLength x₁ y₁ + lcsLength x₂ y₂ ≤
      lcsLength (Fin.append x₁ x₂) (Fin.append y₁ y₂) := by
  classical
  obtain ⟨z₁, hz₁, hlen₁⟩ := (lcsLength_isGreatest x₁ y₁).1
  obtain ⟨z₂, hz₂, hlen₂⟩ := (lcsLength_isGreatest x₂ y₂).1
  apply (lcsLength_isGreatest
    (Fin.append x₁ x₂) (Fin.append y₁ y₂)).2
  refine ⟨z₁ ++ z₂, ?_, ?_⟩
  · constructor
    · simpa only [List.ofFn_fin_append] using hz₁.1.append hz₂.1
    · simpa only [List.ofFn_fin_append] using hz₁.2.append hz₂.2
  · simp [hlen₁, hlen₂]

/-- Under the source's existence theorem, the normalized expectations tend to
the selected constant. -/
theorem tendsto_binaryChvatalSankoffConstant
    (h : chvatalSankoffLimitExists) :
    Filter.Tendsto normalizedExpectedLCS Filter.atTop
      (nhds binaryChvatalSankoffConstant) := by
  obtain ⟨c, hc⟩ := h
  rw [binaryChvatalSankoffConstant, hc.liminf_eq]
  exact hc

/-- Fekete's lemma turns expected-LCS superadditivity into the source's
ordinary-limit-existence statement. The nonlocal superadditivity premise is
kept explicit here. -/
theorem chvatalSankoffLimitExists_of_superadditive
    (h : ∀ m n : ℕ,
      expectedLCSLength m + expectedLCSLength n ≤ expectedLCSLength (m + n)) :
    chvatalSankoffLimitExists := by
  let u : ℕ → ℝ := fun n => -expectedLCSLength n
  have hsub : Subadditive u := by
    intro m n
    simpa only [u, neg_add] using neg_le_neg (h m n)
  have hbdd : BddBelow (Set.range fun n : ℕ => u n / (n : ℝ)) := by
    refine ⟨-1, ?_⟩
    rintro _ ⟨n, rfl⟩
    by_cases hn : n = 0
    · simp [hn, u]
    · have hdiv : expectedLCSLength n / (n : ℝ) ≤ 1 := by
        rw [div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
        exact expectedLCSLength_le n
      calc
        -1 ≤ -(expectedLCSLength n / (n : ℝ)) := neg_le_neg hdiv
        _ = u n / (n : ℝ) := by simp only [u, neg_div]
  have ht : Filter.Tendsto (fun n : ℕ => -(u n / (n : ℝ))) Filter.atTop
      (nhds (-hsub.lim)) :=
    (hsub.tendsto_lim hbdd).neg
  have ht' : Filter.Tendsto
      (fun n : ℕ => expectedLCSLength n / (n : ℝ)) Filter.atTop
      (nhds (-hsub.lim)) := by
    rw [show (fun n : ℕ => expectedLCSLength n / (n : ℝ)) =
        (fun n : ℕ => -(u n / (n : ℝ))) by
      funext n
      simp only [u, neg_div, neg_neg]]
    exact ht
  refine ⟨-hsub.lim, ht'.congr' ?_⟩
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  simp [normalizedExpectedLCS, hn.ne']

/-- The trivial endpoints follow from the proved finite-level bounds. -/
theorem trivialLowerBound_holds : trivialLowerBound :=
  binaryChvatalSankoffConstant_mem_Icc.1

/-- The trivial upper endpoint follows from the proved finite-level bounds. -/
theorem trivialUpperBound_holds : trivialUpperBound :=
  binaryChvatalSankoffConstant_mem_Icc.2

/-- Expected binary LCS length is superadditive under concatenation. Adapted
from the verified gpt-5.6-sol proof in task T292145496. -/
theorem expectedLCSLength_superadditive :
    ∀ m n : ℕ,
      expectedLCSLength m + expectedLCSLength n ≤ expectedLCSLength (m + n) := by
  intro m n
  let sumLCS := fun k : ℕ =>
    ∑ pair : BinaryStringPair k,
      (lcsLength pair.1 pair.2 : ℝ)
  let cardPairs := fun k : ℕ => (Fintype.card (BinaryStringPair k) : ℝ)
  have hpointwise (pair : BinaryStringPair m × BinaryStringPair n) :
      (lcsLength pair.1.1 pair.1.2 : ℝ) +
          lcsLength pair.2.1 pair.2.2 ≤
        lcsLength
          (appendBinaryStringPairEquiv m n pair).1
          (appendBinaryStringPairEquiv m n pair).2 := by
    exact_mod_cast lcsLength_append_le
      pair.1.1 pair.1.2 pair.2.1 pair.2.2
  have hsum :
      sumLCS m * cardPairs n + cardPairs m * sumLCS n ≤ sumLCS (m + n) := by
    calc
      sumLCS m * cardPairs n + cardPairs m * sumLCS n =
          ∑ pair : BinaryStringPair m × BinaryStringPair n,
            ((lcsLength pair.1.1 pair.1.2 : ℝ) +
              lcsLength pair.2.1 pair.2.2) := by
            simp [sumLCS, cardPairs, Fintype.sum_prod_type,
              Finset.sum_add_distrib, Finset.sum_const, Finset.mul_sum,
              mul_comm]
      _ ≤ ∑ pair : BinaryStringPair m × BinaryStringPair n,
            (lcsLength
              (appendBinaryStringPairEquiv m n pair).1
              (appendBinaryStringPairEquiv m n pair).2 : ℝ) := by
            exact Finset.sum_le_sum fun pair _ => hpointwise pair
      _ = sumLCS (m + n) := by
            exact Fintype.sum_equiv (appendBinaryStringPairEquiv m n)
              (fun pair =>
                (lcsLength
                  (appendBinaryStringPairEquiv m n pair).1
                  (appendBinaryStringPairEquiv m n pair).2 : ℝ))
              (fun pair => (lcsLength pair.1 pair.2 : ℝ))
              (fun _ => rfl)
  have hcard : cardPairs (m + n) = cardPairs m * cardPairs n := by
    change (Fintype.card (BinaryStringPair (m + n)) : ℝ) =
      (Fintype.card (BinaryStringPair m) : ℝ) *
        (Fintype.card (BinaryStringPair n) : ℝ)
    norm_cast
    exact (Fintype.card_congr (appendBinaryStringPairEquiv m n)).symm.trans
      (Fintype.card_prod _ _)
  have hcard_m : 0 < cardPairs m := by
    simp [cardPairs]
  have hcard_n : 0 < cardPairs n := by
    simp [cardPairs]
  simp only [expectedLCSLength, uniformBinaryStringPairs]
  change sumLCS m / cardPairs m + sumLCS n / cardPairs n ≤
    sumLCS (m + n) / cardPairs (m + n)
  rw [hcard]
  calc
    sumLCS m / cardPairs m + sumLCS n / cardPairs n =
        (sumLCS m * cardPairs n + cardPairs m * sumLCS n) /
          (cardPairs m * cardPairs n) := by
      field_simp
    _ ≤ sumLCS (m + n) / (cardPairs m * cardPairs n) :=
      (div_le_div_iff_of_pos_right (mul_pos hcard_m hcard_n)).2 hsum


/-- The source-reported ordinary limit exists unconditionally. -/
theorem chvatalSankoffLimitExists_holds : chvatalSankoffLimitExists :=
  chvatalSankoffLimitExists_of_superadditive expectedLCSLength_superadditive

/-- Source: Dančík--Paterson (1995), catalogue upper bound `0.837623`.
Known literature result; its proof is not supplied here. -/
theorem_wanted dancikPatersonUpperBound_wanted : dancikPatersonUpperBound

/-- Source: Lueker (2009), catalogue computer-assisted upper bound `0.826280`.
Known literature result; its proof and certificate are not supplied here. -/
theorem_wanted luekerUpperBound_wanted : luekerUpperBound

/-- Source: Chvátal--Sankoff (1975), catalogue strict lower bound `> 0`.
Known literature result; its proof is not supplied here. -/
theorem_wanted chvatalSankoffStrictPositive_wanted : chvatalSankoffStrictPositive

/-- Source: Dančík (1994), catalogue computer-assisted lower bound `0.773911`.
Known literature result; its proof and certificate are not supplied here. -/
theorem_wanted dancikLowerBound_wanted : dancikLowerBound

/-- Source: Lueker (2009), catalogue computer-assisted lower bound `0.788071`.
Known literature result; its proof and certificate are not supplied here. -/
theorem_wanted luekerLowerBound_wanted : luekerLowerBound

/-- Source: Heineman et al., arXiv:2407.10925v1 (2024), catalogue
computer-assisted lower bound `0.792665992`. Known literature result;
its proof and certificate are not supplied here. -/
theorem_wanted heinemanLowerBound_wanted : heinemanLowerBound

end
end MathlibExt.Combinatorics.BinaryChvatalSankoffWanted
