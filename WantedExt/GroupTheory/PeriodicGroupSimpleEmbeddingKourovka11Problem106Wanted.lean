/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Embedding periodic groups in simple periodic groups (Kourovka Notebook Problem 11.106)

Kourovka Notebook, Archive of Solved Problems, Problem 11.106 (R. Phillips): can every periodic
group be embedded in a simple periodic group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

namespace MathlibExt.GroupTheory.PeriodicGroupSimpleEmbeddingKourovka11Problem106Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.106 (R.
Phillips). UnsolvedMath record UM-00700798 (`KOU-11.106`), dataset ulamai/UnsolvedMath v1.8.0.

Periodic means that every element has finite order; the given group and the simple periodic group
are taken in `Type`, and an embedding is an injective homomorphism.
-/

/-- Kourovka 11.106 (R. Phillips): every periodic group embeds in a simple periodic group. -/
def periodicGroupEmbedsInSimplePeriodic : Prop :=
  ∀ (G : Type) [Group G], (∀ g : G, IsOfFinOrder g) →
    ∃ (S : Type) (_ : Group S), IsSimpleGroup S ∧ (∀ s : S, IsOfFinOrder s) ∧
      ∃ f : G →* S, Function.Injective f

/--
Resolved true: the Kourovka Archive answers 11.106 "Yes", citing Olshanskii (1992), "Embedding
periodic groups in simple periodic groups": every periodic group embeds in a simple periodic group.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.106 (R.
Phillips); resolution: A. Yu. Olshanskii, Embedding periodic groups in simple periodic groups, Ukr.
Mat. Zh. 44 (1992), 845-847 (Russian); English translation: Ukrain. Math. J. 44 (1992), 761-763,
Kourovka Archive, Problem 11.106 ("Yes").
-/
public theorem_wanted periodicGroupEmbedsInSimplePeriodic_holds :
    periodicGroupEmbedsInSimplePeriodic

end MathlibExt.GroupTheory.PeriodicGroupSimpleEmbeddingKourovka11Problem106Wanted
