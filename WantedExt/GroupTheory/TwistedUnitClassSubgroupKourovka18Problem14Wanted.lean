/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Twisted conjugacy classes of the identity that are subgroups (Kourovka Notebook Problem 18.14)

Kourovka Notebook, Problem 18.14 (V. G. Bardakov, M. V. Neshchadim, T. R. Nasybullov), marked solved
in the 21st issue: for `φ ∈ Aut G` let `[e]_φ = {g⁻¹ g^φ | g ∈ G}`. Conjecture: if `[e]_φ` is a
subgroup for every `φ ∈ Aut G`, then `G` is nilpotent; if in addition `G` is finitely generated,
then `G` is abelian.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.GroupTheory.TwistedUnitClassSubgroupKourovka18Problem14

@[expose] public section

namespace MathlibExt.GroupTheory.TwistedUnitClassSubgroupKourovka18Problem14Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.14 (V. G. Bardakov, M. V. Neshchadim, T.
R. Nasybullov). UnsolvedMath record UM-00701443 (`KOU-18.14`), dataset ulamai/UnsolvedMath v1.8.0.

`g^φ` is the image `φ g`, so `[e]_φ` is the range of `g ↦ g⁻¹ φ(g)`; "is a subgroup" means it is the
carrier of some `Subgroup G`. The conjecture has two assertions, stated as two targets (nilpotency
for all such groups; commutativity for finitely generated ones); the resolving paper refutes each
separately.
-/

/--
**Negative answer to the nilpotency assertion of Kourovka Problem 18.14.** There is a group $G$
that is not nilpotent although, for every automorphism $\varphi$ of $G$, the twisted conjugacy
class of the identity $[e]_\varphi = \{g^{-1}\varphi(g) : g \in G\}$ is a subgroup of $G$.

Nicotera's Corollary 3.1 gives such an infinite group, a restricted direct product of the finite
groups of Theorem 1.2 for pairwise distinct primes.

Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Problem 18.14 (V. G. Bardakov, M. V. Neshchadim, T. R.
Nasybullov); resolution: C. Nicotera, On finite groups in which the twisted conjugacy classes of the
unit element are subgroups, Arch. Math. 123 (2024), no. 3, 225-232, Theorem 1.2 (for every n and
every odd prime p, a finite p-group of class n in which [G, φ] is a subgroup for every φ ∈ Aut G)
and Corollary 3.1 (an infinite non-nilpotent group with this property); the Kourovka Notebook (21st
issue) marks 18.14 solved, https://doi.org/10.1007/s00013-024-02025-6.
-/
public theorem_wanted twistedUnitClassesSubgroupsImpliesNilpotent_refuted :
    ¬ twistedUnitClassesSubgroupsImpliesNilpotent

end MathlibExt.GroupTheory.TwistedUnitClassSubgroupKourovka18Problem14Wanted
