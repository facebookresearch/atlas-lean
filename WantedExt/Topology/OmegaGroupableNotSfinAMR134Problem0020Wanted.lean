/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# S_fin(Ω, Ω^gp) versus (Ω Ω^gp) (Tsaban, Milestone Problem 10.6)

B. Tsaban, Selection principles in mathematics: A milestone of open problems, Problem 10.6 (Tsaban,
The minimal cardinality where the Reznichenko property fails, Problem 8): is `S_fin(Ω, Ω^gp)`
equivalent to `(Ω Ω^gp)`?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.Topology.SelectionPrinciplesShared

@[expose] public section

namespace MathlibExt.Topology.OmegaGroupableNotSfinAMR134Problem0020Wanted

/-!
Source: B. Tsaban, Selection principles in mathematics: A milestone of open problems, Note di
Matematica 22 (2003/2004), arXiv:math/0312182, Problem 10.6 (B. Tsaban, Israel J. Math. 140 (2004),
367-374, Problem 8). UnsolvedMath record UM-00800648 (`AMR-134-0020`), dataset ulamai/UnsolvedMath
v1.8.0.

Sets of reals and covers follow the source's conventions: covers of `X` are nontrivial (`⋃ 𝒰 = X`,
`X ∉ 𝒰`), open in `X` and countable; `Ω` is the collection of open `ω`-covers, and `Ω^gp` is the
collection of `Ω`-groupable members of `Ω` (Section 10: a partition into finite sets `𝓕ₙ` such that
for every infinite `A ⊆ ℕ` the sets `⋃ 𝓕ₙ`, `n ∈ A`, form an `ω`-cover). The definitions repeat
those of the OpenConjectures helper `AMR134Problem0004.Helper.SelectionPrinciples`.
-/

open MathlibExt.Topology.SelectionPrinciplesShared

/-- Tsaban, Milestone Problem 10.6 (Tsaban, Israel J. Math. 140 (2004), Problem 8): for sets of
reals `X`, `S_fin(Ω, Ω^gp)` is equivalent to `(Ω Ω^gp)`. -/
def sfinOmegaGroupableIffChoose : Prop :=
  ∀ X : Set ℝ, Sfin (omegaCovers X) (omegaGroupableCovers X) ↔
    Choose (omegaCovers X) (omegaGroupableCovers X)

/--
Resolved false: the problem list's Notes added in proof record Sakai's theorem that the Baire space
(a set of reals, homeomorphic to the irrationals) satisfies `(B_Ω B_Ω^gp)`, hence `(Ω Ω^gp)`, while
it is not even Menger, so it fails `S_fin(Ω, Ω^gp)`. Source: B. Tsaban, Selection principles in
mathematics: A milestone of open problems, Note di Matematica 22 (2003/2004), arXiv:math/0312182,
Problem 10.6 (B. Tsaban, Israel J. Math. 140 (2004), 367-374, Problem 8); resolution: M. Sakai, Weak
Fréchet-Urysohn property in function spaces, as recorded in the problem list's Notes added in proof
(arXiv:math/0312182), Notes added in proof: 'Sakai showed that the answer for Problem 10.6 is No, in
the following strong sense: ... every analytic set of reals (and, in particular, the Baire space
ℕ^ℕ) satisfies (B_Ω B_Ω^gp). But we know that ℕ^ℕ does not even satisfy Menger's property U_fin(O,
O)', https://arxiv.org/abs/math/0312182.
-/
public theorem_wanted sfinOmegaGroupableIffChoose_refuted : ¬ sfinOmegaGroupableIffChoose

end MathlibExt.Topology.OmegaGroupableNotSfinAMR134Problem0020Wanted
