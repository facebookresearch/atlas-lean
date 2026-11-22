/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Kernels and complements of Frobenius groups (Kourovka Notebook Problem 6.53)

Kourovka Notebook, Archive of Solved Problems, Problem 6.53 (V. P. Shunkov): a group G = F ⋊ H is a
Frobenius group with kernel F and complement H if H ∩ Hᵍ = 1 for any g ∈ G \ H and F \ {1} = G \ ⋃
Hᵍ. What can be said about the kernel and the complement of a Frobenius group? In particular, which
groups can be kernels? complements?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Ker
public import WantedExt.GroupTheory.FrobeniusGroupShared

@[expose] public section

namespace MathlibExt.GroupTheory.FrobeniusKernelComplementKourovka6Problem53Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.53 (V. P.
Shunkov). UnsolvedMath record UM-00700395 (`KOU-6.53`), dataset ulamai/UnsolvedMath v1.8.0.

Frobenius groups are `IsFrobeniusGroup F H` of `FrobeniusGroupShared`, the definition of Problem
6.53: `G = F ⋊ H` with `H ∩ Hᵍ = 1` for `g ∉ H` and `F \ {1} = G \ ⋃ Hᵍ`, plus non-trivial `F` and
`H` (with `H = 1` every group would be the kernel of the Frobenius group `G ⋊ 1`, with `F = 1` every
group would be a complement). The targets are Bludov's two theorems as the zbMATH review Zbl
0941.20027 states them: every group embeds in the kernel of some Frobenius group, and under such an
embedding the complement can be any right-ordered group. Right-orderable means some linear order
invariant under right multiplication; the trivial group is excluded since complements are
non-trivial.
-/

open MathlibExt.GroupTheory.FrobeniusGroupShared (IsFrobeniusGroup)

/-- Kourovka 6.53 (V. P. Shunkov), first answer: every group embeds into the kernel of some
Frobenius group. -/
def everyGroupEmbedsInFrobeniusKernel : Prop :=
  ∀ (K : Type) [Group K], ∃ (G : Type) (_ : Group G) (F H : Subgroup G), IsFrobeniusGroup F H ∧
    ∃ ι : K →* G, Function.Injective ι ∧ ι.range ≤ F

/-- Kourovka 6.53 (V. P. Shunkov), second answer in Bludov's form: for every group `K` and every
non-trivial right-orderable group `R` (some linear order invariant under right multiplication)
there is a Frobenius group whose complement is isomorphic to `R` and whose kernel contains a copy
of `K`. -/
def embedsInFrobeniusKernelWithRightOrderableComplement : Prop :=
  ∀ (K R : Type) [Group K] [Group R], Nontrivial R →
    (∃ _ : LinearOrder R, ∀ a b c : R, a ≤ b → a * c ≤ b * c) →
    ∃ (G : Type) (_ : Group G) (F H : Subgroup G), IsFrobeniusGroup F H ∧
      (∃ ι : K →* G, Function.Injective ι ∧ ι.range ≤ F) ∧ Nonempty (H ≃* R)

/--
Resolved true: Bludov (1997) proves that every group embeds into the kernel of some Frobenius group,
the first answer of the Kourovka Archive to 6.53. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 6.53 (V. P. Shunkov); resolution: V. V. Bludov, On Frobenius
groups, Siberian Math. J. 38, no. 6 (1997), 1054-1056, zbMATH review Zbl 0941.20027: (1) every group
embeds in the kernel of some Frobenius group; (2) under such embedding, the complement can be chosen
to be any right-ordered group; Kourovka Archive, Problem 6.53: every group can be embedded into the
kernel of a Frobenius group, and every right-orderable group can be a complement in a Frobenius
group (Bludov), https://doi.org/10.1007/BF02675933.
-/
public theorem_wanted everyGroupEmbedsInFrobeniusKernel_holds : everyGroupEmbedsInFrobeniusKernel

/--
Resolved true: Bludov (1997) proves that every group embeds into the kernel of a Frobenius group
whose complement is any prescribed non-trivial right-ordered group; in particular every non-trivial
right-orderable group is a Frobenius complement, the second answer of the Kourovka Archive to 6.53.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.53 (V. P.
Shunkov); resolution: V. V. Bludov, On Frobenius groups, Siberian Math. J. 38, no. 6 (1997),
1054-1056, zbMATH review Zbl 0941.20027: (1) every group embeds in the kernel of some Frobenius
group; (2) under such embedding, the complement can be chosen to be any right-ordered group;
Kourovka Archive, Problem 6.53: every group can be embedded into the kernel of a Frobenius group,
and every right-orderable group can be a complement in a Frobenius group (Bludov),
https://doi.org/10.1007/BF02675933.
-/
public theorem_wanted embedsInFrobeniusKernelWithRightOrderableComplement_holds :
    embedsInFrobeniusKernelWithRightOrderableComplement

end MathlibExt.GroupTheory.FrobeniusKernelComplementKourovka6Problem53Wanted
