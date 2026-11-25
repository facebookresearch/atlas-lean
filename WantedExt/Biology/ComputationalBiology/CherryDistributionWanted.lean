/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Cherries of a uniform random unrooted binary phylogenetic tree

A *cherry* of an unrooted binary phylogenetic tree is a pair of distinct leaves adjacent to a
common vertex. Under the uniform model every unrooted binary phylogenetic tree on `n` labeled
taxa, up to label-preserving isomorphism, has probability `1 / (2 n - 5)‼`. Let `C_n` be the
number of cherries of such a random tree. For `n ≥ 4`, McKenzie and Steel (2000, Theorem 4,
crediting Hendy and Penny for (a) and Steel and Penny, Steel for (b)) state

* (a) `P[C_n = k] = n! (n - 2)! (n - 4)! 2 ^ (n - 2 k) / ((n - 2 k)! (2 n - 4)! k! (k - 2)!)`
  for `k ≥ 2` (the formula is defined for `2 ≤ k ≤ n / 2`);
* (b) `E[C_n] = n (n - 1) / (2 (2 n - 5))` and
  `Var[C_n] = n (n - 1) (n - 4) (n - 5) / (2 (2 n - 5) ^ 2 (2 n - 7))`;

and Corollary 5, proved with an extended Pólya urn central limit theorem, states
`(C_n - n / 4) / √(n / 16) → N(0, 1)` in distribution. The Yule-model results of the same paper
are not recorded here.

Trees and their count `(2 n - 5)‼` are those of
`MathlibExt.Combinatorics.Enumerative.UnrootedBinaryTreeCount` (`UnrootedBinaryTree`,
`UnrootedBinaryTree.Iso`, `nat_card_unrootedBinaryTree`). A random tree is a uniformly random
isomorphism class; an event about the cherry count is the set of classes containing a tree with
that cherry count (`classesWith`). The cherry count is invariant under label-preserving
isomorphism, so this is the usual event.

Sources: A. McKenzie and M. Steel, "Distributions of cherries for two models of trees",
Mathematical Biosciences 164 (2000) 81–92, doi:10.1016/S0025-5564(99)00060-7, Section 4.2,
Theorem 4 and Corollary 5; M. D. Hendy and D. Penny, "Branch and bound algorithms to determine
minimal evolutionary trees", Mathematical Biosciences 59 (1982) 277–290; M. Steel and D. Penny,
"Distributions of tree comparison metrics: some new results", Systematic Biology 42 (1993)
126–141.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.UnrootedBinaryTreeCount
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.CherryDistributionWanted

open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount
open Filter Topology ProbabilityTheory
open scoped Nat

/-- The number of **cherries** of `T`: the two-element sets of taxa whose leaves are both
adjacent to a common vertex. -/
noncomputable def cherryCount {X : Type} (T : UnrootedBinaryTree X) : ℕ :=
  Nat.card {s : Finset X // s.card = 2 ∧ ∃ v : T.V, ∀ x ∈ s, T.G.Adj (T.label x : T.V) v}

/-- The unrooted binary phylogenetic trees on the taxa `Fin n`, up to label-preserving
isomorphism. There are `(2 n - 5)‼` of them for `n ≥ 3` (`nat_card_unrootedBinaryTree`). -/
abbrev TreeClass (n : ℕ) : Type 1 :=
  Quot (UnrootedBinaryTree.Iso (X := Fin n))

/-- The isomorphism classes containing a tree whose cherry count satisfies `P`. -/
def classesWith (n : ℕ) (P : ℕ → Prop) : Set (TreeClass n) :=
  {q | ∃ T : UnrootedBinaryTree (Fin n), Quot.mk _ T = q ∧ P (cherryCount T)}

/-- The probability, under the uniform model on `n` taxa, that the cherry count satisfies `P`:
the proportion of isomorphism classes with that property. -/
noncomputable def uniformProb (n : ℕ) (P : ℕ → Prop) : ℝ :=
  (Nat.card (classesWith n P) : ℝ) / Nat.card (TreeClass n)

/-- The mean of the cherry count under the uniform model on `n` taxa. A tree on `n` taxa has at
most `n.choose 2` cherries, so the sum runs over every possible value. -/
noncomputable def cherryMean (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n.choose 2 + 1), (k : ℝ) * uniformProb n (· = k)

/-- The variance of the cherry count under the uniform model on `n` taxa. -/
noncomputable def cherryVariance (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n.choose 2 + 1), ((k : ℝ) - cherryMean n) ^ 2 * uniformProb n (· = k)

/-- **Distribution of the cherry count** (McKenzie and Steel 2000, Theorem 4(a), due to Hendy
and Penny 1982): under the uniform model on `n ≥ 4` taxa, for `2 ≤ k` with `2 k ≤ n`,
`P[C_n = k] = n! (n - 2)! (n - 4)! 2 ^ (n - 2 k) / ((n - 2 k)! (2 n - 4)! k! (k - 2)!)`.

Source: McKenzie and Steel (2000), Theorem 4(a). -/
public theorem_wanted uniformProb_cherryCount_eq (n k : ℕ) (hn : 4 ≤ n) (hk : 2 ≤ k)
    (hkn : 2 * k ≤ n) :
    uniformProb n (· = k) =
      ((n ! * (n - 2)! * (n - 4)! * 2 ^ (n - 2 * k) : ℕ) : ℝ) /
        ((n - 2 * k)! * (2 * n - 4)! * k ! * (k - 2)! : ℕ)

/-- **Mean cherry count** (McKenzie and Steel 2000, Theorem 4(b), due to Steel and Penny 1993):
under the uniform model on `n ≥ 4` taxa, `E[C_n] = n (n - 1) / (2 (2 n - 5))`.

Source: McKenzie and Steel (2000), Theorem 4(b). -/
public theorem_wanted cherryMean_eq (n : ℕ) (hn : 4 ≤ n) :
    cherryMean n = (n : ℝ) * (n - 1) / (2 * (2 * n - 5))

/-- **Variance of the cherry count** (McKenzie and Steel 2000, Theorem 4(b), via Steel 1988):
under the uniform model on `n ≥ 4` taxa,
`Var[C_n] = n (n - 1) (n - 4) (n - 5) / (2 (2 n - 5) ^ 2 (2 n - 7))`.

Source: McKenzie and Steel (2000), Theorem 4(b). -/
public theorem_wanted cherryVariance_eq (n : ℕ) (hn : 4 ≤ n) :
    cherryVariance n =
      (n : ℝ) * (n - 1) * (n - 4) * (n - 5) / (2 * (2 * n - 5) ^ 2 * (2 * n - 7))

/-- **Normal limit of the cherry count** (McKenzie and Steel 2000, Corollary 5): under the uniform
model, `(C_n - n / 4) / √(n / 16)` converges in distribution to the standard normal law, that is,
for every real `x` the probability that it is at most `x` tends to the standard normal
distribution function at `x`.

Source: McKenzie and Steel (2000), Corollary 5. -/
public theorem_wanted tendsto_uniformProb_normalized_cherryCount (x : ℝ) :
    Tendsto (fun n : ℕ =>
        uniformProb n (fun c => ((c : ℝ) - n / 4) / Real.sqrt (n / 16) ≤ x))
      atTop (𝓝 (cdf (gaussianReal 0 1) x))

end WantedExt.Biology.ComputationalBiology.CherryDistributionWanted
