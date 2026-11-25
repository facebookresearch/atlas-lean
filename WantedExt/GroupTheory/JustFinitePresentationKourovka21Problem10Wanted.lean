/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Just finite presentations of finite groups (Kourovka Notebook Problem 21.10)

Kourovka Notebook, Problem 21.10 (Y. Barnea), marked solved in the 21st issue: we call a group
presentation finite if it represents a finite group. We say that a presentation is just finite if it
is finite and is no longer finite on removal of any relation from it. Is it true that every finite
group has a just finite presentation?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.PresentedGroup

@[expose] public section

namespace MathlibExt.GroupTheory.JustFinitePresentationKourovka21Problem10Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 21.10 (Y. Barnea). UnsolvedMath record
UM-00002519 (`KOU-21.10`), dataset ulamai/UnsolvedMath v1.8.0.

Presentations have finitely many generators `Fin n` and a finite set `R` of relators, as in the
resolving paper ("a finite presentation"); removing `r` gives `PresentedGroup (R.erase r)`.
-/

/-- **Barnea's question on just finite presentations (Kourovka 21.10).** The statement that every
finite group $G$ has a just finite presentation: a presentation $\langle X \mid R \rangle$ with $X$
and $R$ finite that defines $G$ and such that removing any single relator from $R$ gives a
presentation of an infinite group. -/
def finiteGroupHasJustFinitePresentation : Prop :=
  ∀ (G : Type) [Group G] [Finite G], ∃ (n : ℕ) (R : Finset (FreeGroup (Fin n))),
    Nonempty (PresentedGroup (R : Set (FreeGroup (Fin n))) ≃* G) ∧
    ∀ r ∈ R, Infinite (PresentedGroup ((R.erase r : Finset (FreeGroup (Fin n))) :
      Set (FreeGroup (Fin n))))

/--
**Every finite group has a just finite presentation.** For every finite group $G$ there are a
natural number $n$ and a finite subset $R$ of the free group on $n$ generators $x_1, \dots, x_n$
such that the group $\langle x_1, \dots, x_n \mid R \rangle$ is isomorphic to $G$ and, for every
$r \in R$, the group $\langle x_1, \dots, x_n \mid R \setminus \{r\} \rangle$ is infinite. That is,
the answer to Kourovka Problem 21.10 is positive.

Lackenby's paper acknowledges assistance from the Google DeepMind AI co-mathematician tool.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 21.10 (Y. Barnea);
resolution: M. Lackenby, Every finite group admits a just finite presentation, preprint,
arXiv:2605.10402 (2026), Theorem 1: every finite group admits a finite, just finite presentation (a
consequence of Theorem 2 on just-(FA) presentations); Kourovka Notebook (21st issue), Problem 21.10:
Yes, it is true, https://arxiv.org/abs/2605.10402.
-/
public theorem_wanted finiteGroupHasJustFinitePresentation_holds :
    finiteGroupHasJustFinitePresentation

end MathlibExt.GroupTheory.JustFinitePresentationKourovka21Problem10Wanted
