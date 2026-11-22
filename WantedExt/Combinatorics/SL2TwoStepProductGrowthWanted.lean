/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.SL2TwoStepProductGrowthWanted

/-!
# Two-step product growth in SL₂(Fₚ)

[AIM-COMBINATORICS-0241] Problem 3.4 (Brought by B. Green, originally stated by A. Venkatesh).
Source collection: AIM Problem Lists; AIM domain: Combinatorics;
Workshop: Recent trends in additive combinatorics.
Source URL: https://aimath.org/WWN/additivecomb/additivecomb.pdf
Canonical location: aim-combinatorics-notes.json notes[240]; Canonical tag: problem.

Source statement: Let A ⊆ SL₂(Fₚ) satisfy |A| ∼ p^{5/2}. Does it follow that |A·A| > p^{5/2+δ}?

Clause list (every hypothesis, side condition, and quantifier domain):
1. p : ℕ with Nat.Prime p; Fₚ is ZMod p.
2. Ambient group SL₂(Fₚ) is Matrix.SpecialLinearGroup (Fin 2) (ZMod p).
3. A : Finset of SL₂(Fₚ), i.e. A ⊆ SL₂(Fₚ).
4. |A| is Finset.card A, cast to ℝ for comparison.
5. Threshold p^{5/2} is Real.rpow (p : ℝ) (5/2 : ℝ).
6. Comparability |A| ∼ p^{5/2} is (1/C)*p^{5/2} ≤ |A| ∧ |A| ≤ C*p^{5/2} for a fixed C : ℝ with 1 ≤ C.
7. Product set A·A is Finset.image₂ (·*·) A A.
8. |A·A| is Finset.card of the product set, cast to ℝ.
9. Growth threshold p^{5/2+δ} is Real.rpow (p : ℝ) (5/2+δ) with δ : ℝ, 0 < δ.
10. Conclusion is strict inequality |A·A| > p^{5/2+δ}.
11. Quantifiers: ∀ C ≥ 1, ∃ δ > 0, ∃ P0 : ℕ, ∀ prime p ≥ P0, ∀ A, (comparability → growth); one shared δ and one shared threshold P0, independent of p and A, allowed to depend on C; eventual large-p reading of the asymptotic question.
12. Formalized as a Prop-valued definition; resolved true, asserted by `conjecture_holds` below.
-/

/-- **Product set of a finite set.** For a finite subset $A$ of a type with a multiplication, the
product set $A \cdot A$ is the finite set $\{ab : a, b \in A\}$ of all products of two elements
of $A$.

Source: AIM-COMBINATORICS-0241, Problem 3.4, aim-combinatorics-notes.json notes[240]. -/
@[nolint defsWithUnderscore]
def AIMCombinatorics0241_prodSet {G : Type*} [Mul G] [DecidableEq G] (A : Finset G) : Finset G :=
  Finset.image₂ (· * ·) A A

/-- **Two-step product growth in $\mathrm{SL}_2(\mathbb{F}_p)$ (AIM Problem 3.4).** The statement
that for every real $C \ge 1$ there are a real $\delta > 0$ and a natural number $P_0$ such that
for every prime $p \ge P_0$ and every finite subset $A$ of $\mathrm{SL}_2(\mathbb{F}_p)$, where
$\mathbb{F}_p = \mathbb{Z}/p\mathbb{Z}$, with $C^{-1} p^{5/2} \le |A| \le C p^{5/2}$, the product
set $A \cdot A = \{ab : a, b \in A\}$ satisfies $|A \cdot A| > p^{5/2 + \delta}$.

This is a large-$p$ reading of the question of Green, after Venkatesh: if
$A \subseteq \mathrm{SL}_2(\mathbb{F}_p)$ satisfies $|A| \sim p^{5/2}$, does it follow that
$|A \cdot A| > p^{5/2 + \delta}$?

Source: AIM-COMBINATORICS-0241, Problem 3.4, aim-combinatorics-notes.json notes[240],
https://aimath.org/WWN/additivecomb/additivecomb.pdf. -/
noncomputable def conjecture : Prop :=
  ∀ C : ℝ, 1 ≤ C →
    ∃ δ : ℝ, 0 < δ ∧
      ∃ P0 : ℕ, ∀ p : ℕ, P0 ≤ p → Nat.Prime p →
        ∀ A : Finset (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)),
          (((1 / C) * Real.rpow (p : ℝ) (5 / 2 : ℝ) ≤ (A.card : ℝ)) ∧
            ((A.card : ℝ) ≤ C * Real.rpow (p : ℝ) (5 / 2 : ℝ)) →
          Real.rpow (p : ℝ) (5 / 2 + δ) < ((AIMCombinatorics0241_prodSet A).card : ℝ))

/--
**Sets of size about $p^{5/2}$ in $\mathrm{SL}_2(\mathbb{F}_p)$ grow under multiplication.** For
every real $C \ge 1$ there are a real $\delta > 0$ and a natural number $P_0$ such that for every
prime $p \ge P_0$ and every finite subset $A$ of $\mathrm{SL}_2(\mathbb{F}_p)$, where
$\mathbb{F}_p = \mathbb{Z}/p\mathbb{Z}$, with $C^{-1} p^{5/2} \le |A| \le C p^{5/2}$, the product
set $A \cdot A = \{ab : a, b \in A\}$ satisfies $|A \cdot A| > p^{5/2 + \delta}$.

Every nontrivial representation of $\mathrm{SL}_2(\mathbb{F}_p)$ has dimension at least
$(p-1)/2$, and the product-mixing bound of Gowers and Babai–Nikolov–Pyber then gives
$|A \cdot A| \gg p^3$ for such $A$, so every $\delta < 1/2$ works. This answers AIM
additive-combinatorics Problem 3.4 (Green, after Venkatesh).

Source: N.
Nikolov and L. Pyber, Product decompositions of quasirandom groups and a Jordan type theorem,
arXiv:math/0703343, https://arxiv.org/abs/math/0703343. Moved from
`OpenConjectures/Combinatorics/SL2TwoStepProductGrowth`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.SL2TwoStepProductGrowthWanted
