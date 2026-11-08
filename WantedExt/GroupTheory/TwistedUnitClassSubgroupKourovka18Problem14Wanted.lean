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
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Nilpotent

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

/-- The `φ`-twisted conjugacy class of the identity, `[e]_φ = {g⁻¹ φ(g) | g ∈ G}`. -/
def twistedUnitClass {G : Type} [Group G] (φ : G ≃* G) : Set G :=
  Set.range fun g : G => g⁻¹ * φ g

/-- Every set `[e]_φ`, `φ ∈ Aut G`, is a subgroup of `G`. -/
def AllTwistedUnitClassesSubgroups (G : Type) [Group G] : Prop :=
  ∀ φ : G ≃* G, ∃ H : Subgroup G, (H : Set G) = twistedUnitClass φ

/-- Kourovka 18.14 (V. G. Bardakov, M. V. Neshchadim, T. R. Nasybullov), first assertion of the
conjecture: a group `G` in which `[e]_φ` is a subgroup for every automorphism `φ` is nilpotent. -/
def twistedUnitClassesSubgroupsImpliesNilpotent : Prop :=
  ∀ (G : Type) [Group G], AllTwistedUnitClassesSubgroups G → Group.IsNilpotent G

/-- Kourovka 18.14, second assertion of the conjecture: a finitely generated group `G` in which
`[e]_φ` is a subgroup for every automorphism `φ` is abelian. -/
def twistedUnitClassesSubgroupsFGImpliesAbelian : Prop :=
  ∀ (G : Type) [Group G], Group.FG G → AllTwistedUnitClassesSubgroups G →
    ∀ x y : G, x * y = y * x

/--
Resolved false: Nicotera's Corollary 3.1 gives an infinite non-nilpotent group `G` in which `[e]_φ`
is a subgroup for every automorphism `φ` (a restricted direct product of the finite groups of
Theorem 1.2 for pairwise distinct primes), so the first assertion of Conjecture 18.14 fails. Source:
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

/--
Resolved false: Nicotera's Theorem 1.2 gives, for every `n` and every odd prime `p`, a finite (hence
finitely generated) `p`-group of nilpotency class `n` in which `[e]_φ` is a subgroup for every
automorphism `φ`; for `n ≥ 2` it is not abelian, so the second assertion fails (as do finite
non-abelian `p`-groups all of whose automorphisms are central, which Nicotera also cites). Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Problem 18.14 (V. G. Bardakov, M. V. Neshchadim, T. R.
Nasybullov); resolution: C. Nicotera, On finite groups in which the twisted conjugacy classes of the
unit element are subgroups, Arch. Math. 123 (2024), no. 3, 225-232, Theorem 1.2 (for every n and
every odd prime p, a finite p-group of class n in which [G, φ] is a subgroup for every φ ∈ Aut G)
and Corollary 3.1 (an infinite non-nilpotent group with this property); the Kourovka Notebook (21st
issue) marks 18.14 solved, https://doi.org/10.1007/s00013-024-02025-6.
-/
public theorem_wanted twistedUnitClassesSubgroupsFGImpliesAbelian_refuted :
    ¬ twistedUnitClassesSubgroupsFGImpliesAbelian

end MathlibExt.GroupTheory.TwistedUnitClassSubgroupKourovka18Problem14Wanted
