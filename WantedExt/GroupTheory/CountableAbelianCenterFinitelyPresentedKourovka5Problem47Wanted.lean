/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Countable abelian groups in centres of finitely presented groups (Kourovka Notebook Problem 5.47)

Kourovka Notebook, Problem 5.47 (V. N. Remeslennikov), marked solved in the 21st issue: is every
countable abelian group embeddable in the center of some finitely presented group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FinitelyPresentedGroup

@[expose] public section

namespace MathlibExt.GroupTheory.CountableAbelianCenterFinitelyPresentedKourovka5Problem47Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 5.47 (V. N. Remeslennikov). UnsolvedMath
record UM-00700328 (`KOU-5.47`), dataset ulamai/UnsolvedMath v1.8.0.

Finitely presented is Mathlib's `Group.IsFinitelyPresented`; an embedding into the center is an
injective homomorphism with image in `Subgroup.center G`. The problem is in the main list of the
21st issue, marked solved.
-/

/-- Kourovka 5.47 (V. N. Remeslennikov): every countable abelian group embeds in the center of
some finitely presented group. -/
def countableAbelianEmbedsInCenter : Prop :=
  ∀ (A : Type) [CommGroup A] [Countable A], ∃ (G : Type) (_ : Group G)
    (_ : Group.IsFinitelyPresented G) (f : A →* G), Function.Injective f ∧
      ∀ a : A, f a ∈ Subgroup.center G

/--
Resolved true: Ould Houcine (J. Algebra 307 (2007), Corollary 3 of the author's version) proves that
some finitely presented group `H` with soluble word problem contains in its centre a copy of every
countable abelian group; the Kourovka Notebook (21st issue) marks 5.47 solved, "Yes, it is". Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Problem 5.47 (V. N. Remeslennikov); resolution: A. Ould
Houcine, Embeddings in finitely presented groups which preserve the center, J. Algebra 307 (2007),
no. 1, 1-23, Corollary 3 (author's version, abstract and §1): there exists a finitely presented
group H with soluble word problem such that every countable abelian group embeds in the centre of H;
the Kourovka Notebook (21st issue) marks 5.47 solved: Yes, it is,
http://math.univ-lyon1.fr/~ould/Fiches-papiers/embeddings.pdf.
-/
public theorem_wanted countableAbelianEmbedsInCenter_holds : countableAbelianEmbedsInCenter

end MathlibExt.GroupTheory.CountableAbelianCenterFinitelyPresentedKourovka5Problem47Wanted
