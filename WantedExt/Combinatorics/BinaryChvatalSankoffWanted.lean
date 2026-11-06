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


/-- **Binary strings.** For a natural number $n$, a binary string of length $n$ is a function
from $\{0, 1, \dots, n - 1\}$ to $\{\mathrm{false}, \mathrm{true}\}$, that is, a sequence of $n$
bits listed in order. -/
abbrev BinaryString (n : ℕ) := Fin n → Bool

/-- **Pairs of binary strings.** For a natural number $n$, a pair of binary strings of length $n$
is an ordered pair $(x, y)$ of binary strings $x$ and $y$, each of length $n$. These pairs form
the finite sample space over which expected longest common subsequence lengths are taken. -/
abbrev BinaryStringPair (n : ℕ) := BinaryString n × BinaryString n

/-- **Common subsequence.** For binary strings $x$ and $y$ of length $n$, a finite sequence of bits
$z$ is a common subsequence of $x$ and $y$ if $z$ is obtained both from $x$ and from $y$ by
deleting some (possibly no) entries and keeping the remaining entries in order.

Repeated symbols are kept with their multiplicities. -/
def IsCommonSubsequence {n : ℕ} (z : List Bool)
    (x y : BinaryString n) : Prop :=
  z.Sublist (List.ofFn x) ∧ z.Sublist (List.ofFn y)

/-- **Lengths of common subsequences.** For binary strings $x$ and $y$ of length $n$, the set of
natural numbers $k$ such that some binary list of length $k$ is a common subsequence of $x$
and $y$. -/
def commonSubsequenceLengths {n : ℕ} (x y : BinaryString n) : Set ℕ :=
  {k | ∃ z : List Bool, IsCommonSubsequence z x y ∧ z.length = k}

/-- **Length of a longest common subsequence.** For binary strings $x$ and $y$ of length $n$,
$\mathrm{LCS}(x, y)$ is the length returned by the dynamic-programming algorithm for the longest
common subsequence, applied to $x$ and $y$ read as lists of bits.

This value is the greatest length of a common subsequence of $x$ and $y$. -/
def lcsLength {n : ℕ} (x y : BinaryString n) : ℕ :=
  (Cslib.Algorithms.Lean.longestCommonSubsequence
    (List.ofFn x) (List.ofFn y)).ret.1

/-- **The LCS length is the maximum common-subsequence length.** For binary strings $x$ and $y$ of
length $n$, let $\mathrm{LCS}(x, y)$ be the length returned by the dynamic-programming algorithm
for the longest common subsequence on $x$ and $y$. Then some common subsequence of $x$ and $y$
has length $\mathrm{LCS}(x, y)$, and every common subsequence of $x$ and $y$ has length at most
$\mathrm{LCS}(x, y)$. -/
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

/-- **Existence of a longest common subsequence.** For binary strings $x$ and $y$ of length $n$,
there is a binary list $z$ that is a common subsequence of $x$ and $y$, whose length equals the
LCS length of $x$ and $y$, and such that every common subsequence $w$ of $x$ and $y$ has length at
most the length of $z$. -/
theorem exists_longestCommonSubsequence {n : ℕ} (x y : BinaryString n) :
    ∃ z : List Bool,
      IsCommonSubsequence z x y ∧ z.length = lcsLength x y ∧
        ∀ w : List Bool, IsCommonSubsequence w x y → w.length ≤ z.length := by
  obtain ⟨z, hz, hlen⟩ := (lcsLength_isGreatest x y).1
  exact ⟨z, hz, hlen, fun w hw =>
    (lcsLength_isGreatest x y).2 ⟨w, hw, rfl⟩ |>.trans_eq hlen.symm⟩

/-- **The LCS length is at most the string length.** For binary strings $x$ and $y$ of length $n$,
the length $\mathrm{LCS}(x, y)$ of a longest common subsequence satisfies
$\mathrm{LCS}(x, y) \le n$. -/
theorem lcsLength_le {n : ℕ} (x y : BinaryString n) : lcsLength x y ≤ n := by
  obtain ⟨z, hz, hlen, _⟩ := exists_longestCommonSubsequence x y
  rw [← hlen]
  simpa using hz.1.length_le

/-- **The LCS length as a bounded maximum.** For binary strings $x$ and $y$ of length $n$, the
length $\mathrm{LCS}(x, y)$ of a longest common subsequence equals the largest $k \le n$ such that
$x$ and $y$ have a common subsequence of length $k$ (such $k$ exist, since the empty sequence is a
common subsequence). -/
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

/-- **The finite set of pairs of binary strings.** For a natural number $n$, this is the finite
set of all ordered pairs $(x, y)$ of binary strings $x$ and $y$ of length $n$. -/
def uniformBinaryStringPairs (n : ℕ) : Finset (BinaryStringPair n) :=
  Finset.univ

/-- **Expected length of a longest common subsequence.** For $n \in \mathbb{N}$, the expected LCS
length $E_n$ is the average of $\mathrm{LCS}(x, y)$, the length of a longest common subsequence of
$x$ and $y$, over all ordered pairs $(x, y)$ of binary strings of length $n$: it is the sum of
$\mathrm{LCS}(x, y)$ over these pairs divided by their number $4^n$. Equivalently, $E_n$ is the
expectation of $\mathrm{LCS}(x, y)$ for two independent uniformly random binary strings $x$, $y$
of length $n$. -/
def expectedLCSLength (n : ℕ) : ℝ :=
  (∑ pair ∈ uniformBinaryStringPairs n,
      (lcsLength pair.1 pair.2 : ℝ)) /
    (Fintype.card (BinaryStringPair n) : ℝ)

/-- **Expected LCS length is nonnegative.** For every $n$, the expected length of a longest common
subsequence of two independent uniformly random binary strings of length $n$ is at least $0$. -/
theorem expectedLCSLength_nonneg (n : ℕ) : 0 ≤ expectedLCSLength n := by
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro pair _
    exact Nat.cast_nonneg _
  · exact Nat.cast_nonneg _

/-- **Expected LCS length is at most the string length.** For every $n$, the expected length of a
longest common subsequence of two independent uniformly random binary strings of length $n$ is at
most $n$. -/
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

/-- **Normalized expected LCS length.** For $n \ge 1$, the normalized expected LCS length at $n$
is $E_n / n$, where $E_n$ is the expected length of a longest common subsequence of two
independent uniformly random binary strings of length $n$. At $n = 0$ it is defined to be $0$. -/
def normalizedExpectedLCS (n : ℕ) : ℝ :=
  if n = 0 then 0 else expectedLCSLength n / (n : ℝ)

/-- **Normalized expected LCS lengths lie in $[0,1]$.** For every natural number $n$, the
normalized expected LCS length at $n$ (the expected length of a longest common subsequence of
two independent uniformly random binary strings of length $n$, divided by $n$, and $0$ for
$n = 0$) lies in the closed interval $[0,1]$. -/
theorem normalizedExpectedLCS_mem_Icc (n : ℕ) :
    normalizedExpectedLCS n ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hn : n = 0
  · simp [normalizedExpectedLCS, hn]
  · simp only [normalizedExpectedLCS, hn, ↓reduceIte]
    constructor
    · exact div_nonneg (expectedLCSLength_nonneg n) (Nat.cast_nonneg n)
    · rw [div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
      exact expectedLCSLength_le n

/-- **Binary Chvátal–Sankoff constant.** Let $L_n$ be the length of a longest common subsequence
of two independent uniformly random binary strings of length $n$. The binary Chvátal–Sankoff
constant is the real number $\liminf_{n \to \infty} \mathbb{E}[L_n]/n$.

For every $n \ge 1$ the quotient $\mathbb{E}[L_n]/n$ lies in $[0, 1]$, so this limit inferior is
finite. By the theorem of Chvátal and Sankoff the sequence converges, so the constant equals the
ordinary limit $\lim_{n \to \infty} \mathbb{E}[L_n]/n$; defining it as a limit inferior avoids
choosing an arbitrary value before convergence is known. -/
noncomputable def binaryChvatalSankoffConstant : ℝ :=
  Filter.liminf normalizedExpectedLCS Filter.atTop

/-- **Catalogue notation for the binary Chvátal–Sankoff constant.** Let $L_n$ be the length of a
longest common subsequence of two independent uniformly random binary strings of length $n$.
The notation $C_{31a}$ stands for the binary Chvátal–Sankoff constant
$\liminf_{n \to \infty} \mathbb{E}[L_n]/n$. -/
noncomputable abbrev C31a : ℝ :=
  binaryChvatalSankoffConstant

/-- **Statement of the Chvátal–Sankoff limit theorem.** Let $L_n$ be the length of a longest
common subsequence of two independent uniformly random binary strings of length $n$. This
proposition asserts that the sequence $\mathbb{E}[L_n]/n$ converges to a real number as
$n \to \infty$. Chvátal and Sankoff proved that it holds. -/
def chvatalSankoffLimitExists : Prop :=
  ∃ c : ℝ, Filter.Tendsto normalizedExpectedLCS Filter.atTop (nhds c)

/-- **Trivial bounds for the binary Chvátal–Sankoff constant.** Let $L_n$ be the length of a
longest common subsequence of two independent uniformly random binary strings of length $n$, and
let $C_{31a} = \liminf_{n \to \infty} \mathbb{E}[L_n]/n$ be the binary Chvátal–Sankoff constant.
Then $0 \le C_{31a} \le 1$. -/
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

/-- **Trivial upper bound for the binary Chvátal–Sankoff constant.** Let $C_{31a}$ be the
binary Chvátal–Sankoff constant: the limit inferior as $n \to \infty$ of $E_n / n$, where $E_n$
is the expected length of a longest common subsequence of two independent uniformly random
binary strings of length $n$. This is the proposition $C_{31a} \le 1$. -/
def trivialUpperBound : Prop :=
  C31a ≤ 1

/-- **Statement of the Dančík–Paterson upper bound.** The proposition that the binary
Chvátal–Sankoff constant $\gamma$ satisfies $\gamma \le 0.837623$. Here $\gamma$ is the limit
inferior, as $n \to \infty$, of $\mathbb{E}[L_n]/n$, where $L_n$ is the length of a longest common
subsequence of two independent uniformly random binary strings of length $n$. -/
def dancikPatersonUpperBound : Prop :=
  C31a ≤ (837623 : ℝ) / 1000000

/-- **Statement of Lueker's upper bound.** The proposition that the binary
Chvátal–Sankoff constant $C_{31a}$ is at most $0.826280$. -/
def luekerUpperBound : Prop :=
  C31a ≤ (826280 : ℝ) / 1000000

/-- **Statement of the trivial lower bound.** The proposition that the binary Chvátal–Sankoff
constant $C_{31a}$ satisfies $0 \le C_{31a}$. -/
def trivialLowerBound : Prop :=
  0 ≤ C31a

/-- **Statement of the Chvátal–Sankoff positivity bound.** The proposition that the binary
Chvátal–Sankoff constant $\gamma$ is strictly positive, $0 < \gamma$. Here $\gamma$ is the limit
inferior, as $n \to \infty$, of $\mathbb{E}[L_n]/n$, where $L_n$ is the length of a longest common
subsequence of two independent uniformly random binary strings of length $n$. -/
def chvatalSankoffStrictPositive : Prop :=
  0 < C31a

/-- **Statement of Dančík's lower bound.** The proposition that the binary Chvátal–Sankoff
constant $\gamma$ satisfies $0.773911 \le \gamma$. Here $\gamma$ is the limit inferior, as
$n \to \infty$, of $\mathbb{E}[L_n]/n$, where $L_n$ is the length of a longest common
subsequence of two independent uniformly random binary strings of length $n$. -/
def dancikLowerBound : Prop :=
  (773911 : ℝ) / 1000000 ≤ C31a

/-- **Statement of Lueker's lower bound.** The proposition that the binary
Chvátal–Sankoff constant $C_{31a}$ is at least $0.788071$. -/
def luekerLowerBound : Prop :=
  (788071 : ℝ) / 1000000 ≤ C31a

/-- **Statement of the Heineman et al. lower bound.** For each $n$, let $E_n$ be the expected
length of a longest common subsequence of two independent uniformly random binary strings of
length $n$, and let $C$, the binary Chvátal–Sankoff constant, be the limit inferior of $E_n / n$
as $n \to \infty$. This is the proposition $0.792665992 \le C$.

Heineman et al. obtained this computer-assisted bound; the decimal is an exact rational endpoint. -/
def heinemanLowerBound : Prop :=
  (792665992 : ℝ) / 1000000000 ≤ C31a

/-- **Statement of the reported 2026 lower bound $0.79970$.** The proposition that the binary
Chvátal–Sankoff constant $C_{31a}$ is at least $0.79970$.

This bound was reported in 2026 as AI and computer assisted and has not been verified. -/
def sourceReportedUnverified2026LowerBound : Prop :=
  (79970 : ℝ) / 100000 ≤ C31a

/-- **Concatenation of binary string pairs.** For natural numbers $m$ and $n$, sending a pair
$(x_1, y_1)$ of binary strings of length $m$ together with a pair $(x_2, y_2)$ of binary strings
of length $n$ to the pair $(x_1 x_2, y_1 y_2)$ of concatenations is a bijection from the product
of the set of pairs of length-$m$ binary strings and the set of pairs of length-$n$ binary
strings onto the set of pairs of binary strings of length $m + n$. Its inverse splits each
string of length $m + n$ into its first $m$ and its last $n$ symbols.

Source: uniform independent binary-string model; concatenation
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

/-- **Superadditivity of the LCS length under concatenation.** Write $\mathrm{LCS}(x, y)$ for the
length of a longest common subsequence of binary strings $x$ and $y$ of equal length. Let
$x_1, y_1$ be binary strings of length $m$ and $x_2, y_2$ binary strings of length $n$, and write
$x_1x_2$ and $y_1y_2$ for the concatenated strings of length $m + n$. Then
$\mathrm{LCS}(x_1, y_1) + \mathrm{LCS}(x_2, y_2) \le \mathrm{LCS}(x_1x_2, y_1y_2)$.

Source: common subsequences concatenate without changing their order. -/
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

/-- **Any limit of the normalized expected LCS lengths is the binary Chvátal–Sankoff constant.**
If the normalized expected LCS lengths converge to some real number as $n \to \infty$, then they
converge to the binary Chvátal–Sankoff constant $C_{31a}$, which is defined as their limit
inferior. -/
theorem tendsto_binaryChvatalSankoffConstant
    (h : chvatalSankoffLimitExists) :
    Filter.Tendsto normalizedExpectedLCS Filter.atTop
      (nhds binaryChvatalSankoffConstant) := by
  obtain ⟨c, hc⟩ := h
  rw [binaryChvatalSankoffConstant, hc.liminf_eq]
  exact hc

/-- **Superadditivity implies the binary LCS limit exists.** For each natural number $n$, let $E_n$
be the expected length of a longest common subsequence of two independent uniformly random binary
strings of length $n$. If $E_m + E_n \le E_{m+n}$ for all natural numbers $m$ and $n$, then the
sequence $(E_n / n)_{n \ge 1}$ converges to a real number as $n \to \infty$.

The proof applies Fekete's lemma. -/
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

/-- **The binary Chvátal–Sankoff constant is nonnegative.** The binary Chvátal–Sankoff constant
$C_{31a}$ satisfies $0 \le C_{31a}$. -/
theorem trivialLowerBound_holds : trivialLowerBound :=
  binaryChvatalSankoffConstant_mem_Icc.1

/-- **The binary Chvátal–Sankoff constant is at most one.** The binary Chvátal–Sankoff constant
$C_{31a}$ satisfies $C_{31a} \le 1$. -/
theorem trivialUpperBound_holds : trivialUpperBound :=
  binaryChvatalSankoffConstant_mem_Icc.2

/-- **Superadditivity of the expected LCS length.** Let $E_n$ be the expected length of a longest
common subsequence of two independent uniformly random binary strings of length $n$. Then for all
natural numbers $m$ and $n$, $E_m + E_n \le E_{m+n}$.

Source: adapted from the verified gpt-5.6-sol proof in task T292145496. -/
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


/-- **Chvátal–Sankoff theorem: the binary LCS limit exists.** Let $L_n$ be the length of a longest
common subsequence of two independent uniformly random binary strings of length $n$. Then the
sequence $\mathbb{E}[L_n]/n$ converges to a real number as $n \to \infty$. -/
theorem chvatalSankoffLimitExists_holds : chvatalSankoffLimitExists :=
  chvatalSankoffLimitExists_of_superadditive expectedLCSLength_superadditive

/-- **Dančík–Paterson upper bound for the binary Chvátal–Sankoff constant.** The binary
Chvátal–Sankoff constant $\gamma$ satisfies $\gamma \le 0.837623$, where $\gamma$ is the limit
inferior, as $n \to \infty$, of $\mathbb{E}[L_n]/n$ and $L_n$ is the length of a longest common
subsequence of two independent uniformly random binary strings of length $n$.

Source: Dančík--Paterson (1995), catalogue upper bound `0.837623`.
Known literature result; its proof is not supplied here. -/
theorem_wanted dancikPatersonUpperBound_wanted : dancikPatersonUpperBound

/-- **Lueker's upper bound for the binary Chvátal–Sankoff constant.** The binary Chvátal–Sankoff
constant $C_{31a}$ is at most $0.826280$.

Source: Lueker (2009), catalogue computer-assisted upper bound `0.826280`.
Known literature result; its proof and certificate are not supplied here. -/
theorem_wanted luekerUpperBound_wanted : luekerUpperBound

/-- **The binary Chvátal–Sankoff constant is positive.** Let $L_n$ be the length of a longest
common subsequence of two independent uniformly random binary strings of length $n$. The binary
Chvátal–Sankoff constant $C_{31a} = \liminf_{n \to \infty} \mathbb{E}[L_n]/n$ satisfies
$C_{31a} > 0$.

Source: Chvátal--Sankoff (1975), catalogue strict lower bound `> 0`.
Known literature result; its proof is not supplied here. -/
theorem_wanted chvatalSankoffStrictPositive_wanted : chvatalSankoffStrictPositive

/-- **Dančík's lower bound for the binary Chvátal–Sankoff constant.** The binary
Chvátal–Sankoff constant $\gamma$ satisfies $0.773911 \le \gamma$, where $\gamma$ is the limit
inferior, as $n \to \infty$, of $\mathbb{E}[L_n]/n$ and $L_n$ is the length of a longest common
subsequence of two independent uniformly random binary strings of length $n$.

Source: Dančík (1994), catalogue computer-assisted lower bound `0.773911`.
Known literature result; its proof and certificate are not supplied here. -/
theorem_wanted dancikLowerBound_wanted : dancikLowerBound

/-- **Lueker's lower bound for the binary Chvátal–Sankoff constant.** For each $n$, let $E_n$ be
the expected length of a longest common subsequence of two independent uniformly random binary
strings of length $n$, and let $C$, the binary Chvátal–Sankoff constant, be the limit inferior of
$E_n / n$ as $n \to \infty$. Then $0.788071 \le C$.

Source: Lueker (2009), catalogue computer-assisted lower bound `0.788071`.
Known literature result; its proof and certificate are not supplied here. -/
theorem_wanted luekerLowerBound_wanted : luekerLowerBound

/-- **Heineman et al. lower bound for the binary Chvátal–Sankoff constant.** For each $n$, let
$E_n$ be the expected length of a longest common subsequence of two independent uniformly random
binary strings of length $n$, and let $C$, the binary Chvátal–Sankoff constant, be the limit
inferior of $E_n / n$ as $n \to \infty$. Then $0.792665992 \le C$.

Source: Heineman et al., arXiv:2407.10925v1 (2024), catalogue
computer-assisted lower bound `0.792665992`. Known literature result;
its proof and certificate are not supplied here. -/
theorem_wanted heinemanLowerBound_wanted : heinemanLowerBound

end
end MathlibExt.Combinatorics.BinaryChvatalSankoffWanted
