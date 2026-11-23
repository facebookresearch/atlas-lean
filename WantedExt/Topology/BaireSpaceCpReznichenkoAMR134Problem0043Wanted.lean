/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Reznichenko property of C_p of the Baire space (Tsaban, Milestone Problem 16.2)

B. Tsaban, Selection principles in mathematics: A milestone of open problems, Problem 16.2 (Sakai,
Question 3.6): does `C_p(ℕ^ℕ)` have the Reznichenko property?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.Topology.SelectionPrinciplesShared

@[expose] public section

namespace MathlibExt.Topology.BaireSpaceCpReznichenkoAMR134Problem0043Wanted

/-!
Source: B. Tsaban, Selection principles in mathematics: A milestone of open problems, Note di
Matematica 22 (2003/2004), arXiv:math/0312182, Problem 16.2 (M. Sakai, Question 3.6). UnsolvedMath
record UM-00800671 (`AMR-134-0043`), dataset ulamai/UnsolvedMath v1.8.0.

The source writes `C_p(\NN)`, `\NN` being its notation for the Baire space `ℕ^ℕ` (the UnsolvedMath
record shows `C_p(ℕ)`; `C_p(ℕ) = ℝ^ℕ` is metrizable, so that reading would be trivial). `ℕ^ℕ` is `ℕ
→ ℕ` with the product of discrete topologies. `C_p(X)` is the set of continuous real functions on
`X` with the subspace topology of the product `ℝ^X` (pointwise convergence). The Reznichenko (weak
Fréchet-Urysohn) property is the one defined in the source's Section 16 (Malykhin and Tironi): for
`A ⊆ Y` and `y ∈ cl A \ A` there is a countably infinite pairwise disjoint family of finite subsets
of `A` such that every neighbourhood of `y` meets all but finitely many of them; it is written with
an `ℕ`-indexed family, so finitely many members may be empty. The definitions repeat those of the
OpenConjectures entry for Problem 16.1 (`AMR134Problem0042`).
-/

open MathlibExt.Topology.SelectionPrinciplesShared

/-- Tsaban, Milestone Problem 16.2 (Sakai, Question 3.6): `C_p(ℕ^ℕ)` has the Reznichenko property,
where `ℕ^ℕ` is the Baire space `ℕ → ℕ` (product topology, `ℕ` discrete). -/
def baireSpaceCpReznichenko : Prop :=
  HasReznichenkoProperty (Cp (ℕ → ℕ))

/--
Resolved true: `C_p(ℕ^ℕ)` has the Reznichenko property. The problem list's Notes added in proof
record Sakai's theorem that every analytic set of reals, in particular `ℕ^ℕ`, satisfies `(B_Ω
B_Ω^gp)`, and that this answers the problem in the affirmative. Source: B. Tsaban, Selection
principles in mathematics: A milestone of open problems, Note di Matematica 22 (2003/2004),
arXiv:math/0312182, Problem 16.2 (M. Sakai, Question 3.6); resolution: M. Sakai, Weak
Fréchet-Urysohn property in function spaces, as recorded in the problem list's Notes added in proof
(arXiv:math/0312182), Notes added in proof: Sakai proved that every analytic set of reals, in
particular the Baire space ℕ^ℕ, satisfies (B_Ω B_Ω^gp), and 'This also answers Problem 16.2 in the
affirmative' (Section 16 of the list: if X satisfies (Ω Ω^gp) then C_p(X) has the Reznichenko
property, by Sakai's characterization), https://arxiv.org/abs/math/0312182.
-/
public theorem_wanted baireSpaceCpReznichenko_holds : baireSpaceCpReznichenko

end MathlibExt.Topology.BaireSpaceCpReznichenkoAMR134Problem0043Wanted
