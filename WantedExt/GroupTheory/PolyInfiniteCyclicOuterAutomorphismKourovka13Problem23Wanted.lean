/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Outer automorphisms of poly-infinite-cyclic groups (Kourovka Notebook Problem 13.23)

Kourovka Notebook, Problem 13.23 (F. de Giovanni), marked solved in the 21st issue: let the group
`G` have a finite normal series with infinite cyclic factors. Is it true that `G` has a non-trivial
outer automorphism?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.End
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.PolyInfiniteCyclicOuterAutomorphismKourovka13Problem23Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 13.23 (F. de Giovanni). UnsolvedMath record
UM-00700941 (`KOU-13.23`), dataset ulamai/UnsolvedMath v1.8.0.

A finite normal series consists of subgroups `1 = H₀ ≤ ⋯ ≤ Hₙ = G`, each normal in `G`, here with
infinite cyclic factors. `G` is required to be nontrivial: the trivial group has such a series (`n =
0`) and no outer automorphism. A non-trivial outer automorphism is an automorphism that is not
inner.
-/

/-- **Normal series with infinite cyclic factors.** A group $G$ has a normal series with infinite
cyclic factors when there are a natural number $n$ and subgroups
$1 = H_0 \le H_1 \le \cdots \le H_n = G$, each normal in $G$, such that every factor
$H_{i+1}/H_i$ is infinite cyclic. -/
def HasNormalSeriesInfiniteCyclicFactors (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (H : Fin (n + 1) → Subgroup G), H 0 = ⊥ ∧ H (Fin.last n) = ⊤ ∧
    (∀ i, (H i).Normal) ∧ ∀ i : Fin n, H i.castSucc ≤ H i.succ ∧
      ∃ _ : ((H i.castSucc).subgroupOf (H i.succ)).Normal,
        IsCyclic (H i.succ ⧸ (H i.castSucc).subgroupOf (H i.succ)) ∧
          Infinite (H i.succ ⧸ (H i.castSucc).subgroupOf (H i.succ))

/-- **Outer automorphisms of groups with an infinite cyclic normal series (Kourovka 13.23).** The
conjecture that every nontrivial group with a normal series with infinite cyclic factors has an
automorphism that is not inner.

This is Kourovka Problem 13.23 (F. de Giovanni). -/
def polyInfiniteCyclicHasOuterAutomorphism : Prop :=
  ∀ (G : Type) [Group G], Nontrivial G → HasNormalSeriesInfiniteCyclicFactors G →
    ∃ φ : MulAut G, ∀ g : G, φ ≠ MulAut.conj g

/--
**Only inner automorphisms despite an infinite cyclic normal series (Kourovka 13.23 refuted).**
There is a nontrivial group $G$ with a normal series with infinite cyclic factors such that every
automorphism of $G$ is inner. So the conjecture of Kourovka Problem 13.23 is false.

Brescia, Ingrosso and Trombetti construct a torsion-free group $G$ of Hirsch length $14$ with a
series $1 = G_0 \trianglelefteq \cdots \trianglelefteq G_{14} = G$ of normal subgroups of $G$
with infinite cyclic factors and $\mathrm{Out}(G) = 1$; the Kourovka Notebook (21st issue)
marks 13.23 solved, "No, not always".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 13.23 (F. de Giovanni); resolution: M.
Brescia, E. Ingrosso and M. Trombetti, A torsion-free supersoluble group with trivial outer
automorphism group, preprint (2026), arXiv:2607.11775, abstract: a torsion-free group of Hirsch
length 14 with a series 1 = G_0 ◁ ⋯ ◁ G_14 = G of normal subgroups of G with infinite cyclic
factors and Out(G) = 1; the Kourovka Notebook (21st issue) marks 13.23 solved,
https://arxiv.org/abs/2607.11775.
-/
public theorem_wanted polyInfiniteCyclicHasOuterAutomorphism_refuted :
    ¬ polyInfiniteCyclicHasOuterAutomorphism

end MathlibExt.GroupTheory.PolyInfiniteCyclicOuterAutomorphismKourovka13Problem23Wanted
