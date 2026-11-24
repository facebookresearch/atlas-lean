/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Partition ordinals: from triangles to larger cliques (Erdős Problem 118)

Erdős Problem 118: let `α` be a cardinal, ordinal or order type such that every two-colouring of
`K_α` contains a red `K_α` or a blue `K_3`. For every `n ≥ 3`, must every two-colouring of `K_α`
contain a red `K_α` or a blue `K_n`? That is, does `α → (α, 3)²` imply `α → (α, n)²`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.PartitionOrdinalTriangleCliqueErdosProblem118Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #118, https://www.erdosproblems.com/118 (status
DISPROVED). UnsolvedMath record UM-30006730 (`EP-118`), dataset ulamai/UnsolvedMath v1.8.0.

Stated for ordinals `α` (in `Ordinal.{0}`): the counterexamples are countable ordinals, so refuting
the ordinal case refutes the general question. A red `K_α` is a set of order type `α`, the image of
a strictly increasing map from the ordinals below `α` into themselves. formal-conjectures has no
statement.
-/

/-- **Ordinal partition relation.** For an ordinal $\alpha$ and a natural number $n$, the partition
relation $\alpha \to (\alpha, n)^2$ holds when every colouring of the pairs $x < y$ of ordinals
below $\alpha$ in red and blue has a red set of order type $\alpha$ or a blue set of size $n$:
either there is a strictly increasing map $f$ from the ordinals below $\alpha$ to the ordinals
below $\alpha$ such that the pair $\{f(x), f(y)\}$ is red for all $x < y < \alpha$, or there is a
set of $n$ ordinals below $\alpha$ all of whose pairs are blue. -/
def PartitionRel (α : Ordinal.{0}) (n : ℕ) : Prop :=
  ∀ c : Ordinal.{0} → Ordinal.{0} → Bool,
    (∃ f : Ordinal.{0} → Ordinal.{0}, StrictMonoOn f (Set.Iio α) ∧ (∀ x < α, f x < α) ∧
      ∀ x < α, ∀ y < α, x < y → c (f x) (f y) = true) ∨
    (∃ s : Finset Ordinal.{0}, s.card = n ∧ (∀ x ∈ s, x < α) ∧
      ∀ x ∈ s, ∀ y ∈ s, x < y → c x y = false)

/-- **Erdős Problem 118 for ordinals.** The statement that for every ordinal $\alpha$ satisfying
the partition relation $\alpha \to (\alpha, 3)^2$ and every natural number $n \ge 3$, the ordinal
$\alpha$ also satisfies $\alpha \to (\alpha, n)^2$. -/
def partitionOrdinalTriangleImpliesClique : Prop :=
  ∀ α : Ordinal.{0}, PartitionRel α 3 → ∀ n : ℕ, 3 ≤ n → PartitionRel α n

/--
**Erdős Problem 118 fails for ordinals.** There exist an ordinal $\alpha$ satisfying the partition
relation $\alpha \to (\alpha, 3)^2$ and a natural number $n \ge 3$ such that $\alpha$ does not
satisfy $\alpha \to (\alpha, n)^2$.

Schipperus and Darby independently answered the question in the negative. A concrete
counterexample is $\alpha = \omega^{\omega^2}$ with $n = 5$: Schipperus proved
$\omega^{\omega^\beta} \to (\omega^{\omega^\beta}, 3)^2$ when $\beta$ is a sum of two additively
indecomposable ordinals (here $\beta = 1 + 1$), and Larson proved
$\omega^{\omega^\beta} \not\to (\omega^{\omega^\beta}, 5)^2$ for every $\beta$ that is not
additively indecomposable.

Source: T. F. Bloom, Erdős Problems, Problem #118, https://www.erdosproblems.com/118 (status
DISPROVED); resolution: R. Schipperus, Countable partition ordinals, Ann. Pure Appl. Logic 161
(2010), 1195-1215; C. Darby, Negative partition relations for ordinals ω^{ω^α}, J. Combin. Theory
Ser. B 76 (1999), 205-222; J. A. Larson, An ordinal partition avoiding pentagrams, J. Symbolic Logic
65 (2000), 969-978, erdosproblems.com/118: answered no independently by Schipperus and Darby; for α
= ω^{ω²}: ω^{ω²} → (ω^{ω²}, 3)² (Schipperus: ω^{ω^β} → (ω^{ω^β}, 3)² when β is a sum of two
additively indecomposable ordinals) and ω^{ω²} ↛ (ω^{ω²}, 5)² (Larson, main theorem: ω^{ω^β} ↛
(ω^{ω^β}, 5)² for β not additively indecomposable; zbMATH 0967.03042); Hajnal-Larson, Handbook of
Set Theory, Chapter 2.9.
-/
public theorem_wanted partitionOrdinalTriangleImpliesClique_refuted :
    ¬ partitionOrdinalTriangleImpliesClique

end MathlibExt.Combinatorics.PartitionOrdinalTriangleCliqueErdosProblem118Wanted
