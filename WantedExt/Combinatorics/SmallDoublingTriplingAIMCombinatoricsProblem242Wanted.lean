/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Small doubling does not force small tripling in groups (AIM additive combinatorics, Problem 3.5)

AIM workshop Recent trends in additive combinatorics, Problem 3.5 (T. Tao): let `A` be a finite
subset of a (not necessarily abelian) group. Given that `A · A` is small, is `A · A · A` necessarily
small, too?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.SmallDoublingTriplingAIMCombinatoricsProblem242Wanted

/-!
Source: AIM workshop Recent trends in additive combinatorics (2004), problem list collected by E.
Croot and V. F. Lev, https://aimath.org/WWN/additivecomb/additivecomb.pdf, Problem 3.5 (T. Tao) and
Tao's comment. UnsolvedMath record UM-20001117 (`AIM-COMBINATORICS-0242`), dataset
ulamai/UnsolvedMath v1.8.0.

'Small' is read uniformly: the claim is that `|A · A| ≤ K |A|` implies `|A · A · A| ≤ f(K) |A|` for
one function `f`, for all finite nonempty subsets of all groups (in `Type`). The comment's follow-up
questions (a large subset `A' ⊆ A` with `A'A'A'` small; an inverse theorem when `|AA| < 2|A|`) are
not formalized. The refutation needs a family of such sets with `|A · A · A| / |A|` unbounded (for
instance `H` a point stabilizer in the affine group of `𝔽_p`, where `|A · A| ≤ 3 |A|` and `H x H`
has `(p - 1)²` elements), not one finite group.
-/

open scoped Pointwise

/-- **Tao's small-doubling question (AIM Problem 3.5).** The proposition that small doubling
forces small tripling uniformly in all groups: there is a function $f : \mathbb{R} \to \mathbb{R}$
such that for every group $G$, every finite nonempty subset $A \subseteq G$ and every real number
$K$, if $|A \cdot A| \le K |A|$ then $|A \cdot A \cdot A| \le f(K) |A|$. Here
$A \cdot A = \{ab : a, b \in A\}$ and $A \cdot A \cdot A = \{abc : a, b, c \in A\}$. -/
def smallDoublingImpliesSmallTripling : Prop :=
  ∃ f : ℝ → ℝ, ∀ (G : Type) [Group G] [DecidableEq G] (A : Finset G) (K : ℝ), A.Nonempty →
    ((A * A).card : ℝ) ≤ K * A.card → ((A * A * A).card : ℝ) ≤ f K * A.card

/--
**Small doubling does not imply small tripling.** There is no function
$f : \mathbb{R} \to \mathbb{R}$ such that for every group $G$, every finite nonempty subset
$A \subseteq G$ and every real number $K$ with $|A \cdot A| \le K |A|$ one has
$|A \cdot A \cdot A| \le f(K) |A|$. Here $A \cdot A = \{ab : a, b \in A\}$ and
$A \cdot A \cdot A = \{abc : a, b, c \in A\}$.

B. Green and M.-C. Chang pointed out the counterexample $A = H \cup \{x\}$ with $H$ a finite
non-normal subgroup and $x$ outside the normalizer of $H$: then $|A \cdot A|$ is comparable to
$|A|$, while $|A \cdot A \cdot A|$ can be much larger.

Source: AIM workshop Recent trends in
additive combinatorics (2004), problem list collected by E. Croot and V. F. Lev,
https://aimath.org/WWN/additivecomb/additivecomb.pdf, Problem 3.5 (T. Tao) and Tao's comment;
resolution: Tao's comment on Problem 3.5 in the AIM problem list (counterexample pointed out by B.
Green and M.-C. Chang); T. Tao, Product set estimates for non-commutative groups, Combinatorica 28
(2008), 547-594, arXiv:math/0601431, comment to Problem 3.5: 'the problem as stated is false, as it
follows by considering A = H ∪ {x} where H is a non-normal subgroup and x is not in the normalizer
of H'; Tao's paper, Section 1 ('if A is the union of a subgroup and a point, then A · A will be
small, but higher products such as A · A · A can be large') and Section 3 (A = H ∪ {x}, H a finite
subgroup, x outside its normalizer: A² has size comparable to A, but A³ can be much larger),
https://aimath.org/WWN/additivecomb/additivecomb.pdf.
-/
public theorem_wanted smallDoublingImpliesSmallTripling_refuted :
    ¬ smallDoublingImpliesSmallTripling

end MathlibExt.Combinatorics.SmallDoublingTriplingAIMCombinatoricsProblem242Wanted
