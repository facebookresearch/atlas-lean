/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hopficity of profinite completions (Kourovka Notebook Problem 6.30)

Kourovka Notebook, Problem 6.30 (O. V. Mel'nikov), marked solved in the 21st issue: let G be a
residually finite Hopfian group, and let Ĝ be its profinite completion. Is Ĝ necessarily Hopfian (in
topological sense)?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

@[expose] public section

namespace MathlibExt.GroupTheory.ProfiniteCompletionHopfianKourovka6Problem30Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 6.30 (O. V. Mel'nikov). UnsolvedMath record
UM-00700376 (`KOU-6.30`), dataset ulamai/UnsolvedMath v1.8.0.

Hopfian means that every surjective endomorphism is injective; for the profinite completion
(Mathlib's `ProfiniteGrp.ProfiniteCompletion.completion`) the endomorphisms are the continuous ones.
Residually finite is Mathlib's `Group.ResiduallyFinite`.
-/

/-- Kourovka 6.30 (O. V. Mel'nikov): the profinite completion of a residually finite Hopfian group
is Hopfian as a topological group: every continuous surjective endomorphism is injective. -/
def profiniteCompletionHopfian : Prop :=
  ∀ (G : Type) [Group G], Group.ResiduallyFinite G →
    (∀ f : G →* G, Function.Surjective f → Function.Injective f) →
    ∀ f : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ*
        ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G),
      Function.Surjective f → Function.Injective f

/--
Resolved false: Brescia, Ingrosso and Trombetti (2026) show that for pairwise distinct odd primes
`qᵢ` the abelian group `⨁ ℤ[1/qᵢ]` is residually finite and Hopfian while its profinite completion
is not topologically Hopfian (Main Theorem: `Â` is topologically Hopfian iff `A/pA` is finite for
every prime `p`); the 21st issue marks 6.30 solved with this answer. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Problem 6.30 (O. V. Mel'nikov); resolution: M. Brescia, E. Ingrosso and
M. Trombetti, Hopficity of profinite completions of abelian groups, arXiv:2607.19193 (2026), Main
Theorem (Â is topologically Hopfian iff A/pA is finite for every prime p) and the following example:
for pairwise distinct odd primes qᵢ, G = ⨁ Z[1/qᵢ] is residually finite and Hopfian but Ĝ is not
topologically Hopfian; marked solved (No, not always) in the 21st issue of the Kourovka Notebook,
https://arxiv.org/abs/2607.19193.
-/
public theorem_wanted profiniteCompletionHopfian_refuted : ¬ profiniteCompletionHopfian

end MathlibExt.GroupTheory.ProfiniteCompletionHopfianKourovka6Problem30Wanted
