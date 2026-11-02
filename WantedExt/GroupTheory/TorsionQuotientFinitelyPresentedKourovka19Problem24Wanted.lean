/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Quotients by torsion of finitely presented groups (Kourovka Notebook Problem 19.24)

Kourovka Notebook, Archive of Solved Problems, Problem 19.24 (M. Chiodo, R. Vyas): for a group `G`
let `Tor(G)` be the normal closure of the torsion elements. Does there exist a finitely presented
group `G` such that `G / Tor(G)` is not finitely presented?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FinitelyPresentedGroup

@[expose] public section

namespace MathlibExt.GroupTheory.TorsionQuotientFinitelyPresentedKourovka19Problem24Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.24 (M.
Chiodo, R. Vyas). UnsolvedMath record UM-00701572 (`KOU-19.24`), dataset ulamai/UnsolvedMath v1.8.0.

Finite presentability is Mathlib's `Group.IsFinitelyPresented`; `G : Type`.
-/

/-- **Torsion closure.** For a group $G$, $\mathrm{Tor}(G)$ is the normal closure in $G$ of the set
of elements of finite order of $G$. -/
abbrev torsionClosure (G : Type*) [Group G] : Subgroup G :=
  Subgroup.normalClosure {g : G | IsOfFinOrder g}

/-- **Kourovka Problem 19.24 (torsion quotients of finitely presented groups).** The statement,
asked by M. Chiodo and R. Vyas, that there exists a finitely presented group $G$ such that
$G / \mathrm{Tor}(G)$ is not finitely presented, where $\mathrm{Tor}(G)$ is the normal closure of
the set of elements of finite order of $G$. -/
def existsFinitelyPresentedTorsionQuotientNotFinitelyPresented : Prop :=
  ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧
    ¬ Group.IsFinitelyPresented (G ⧸ torsionClosure G)

/--
**Torsion quotients of finitely presented groups need not be finitely presented.** There exists
a finitely presented group $G$ such that $G / \mathrm{Tor}(G)$ is not finitely presented, where
$\mathrm{Tor}(G)$ is the normal closure of the set of elements of finite order of $G$.

The Kourovka Archive answers Problem 19.24 "Yes, such groups exist": Leary and Minasyan
(Constructions 3.1 and 3.2) give a soluble example and a virtually torsion-free example.

Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.24 (M. Chiodo, R. Vyas);
resolution: I. J. Leary and A. Minasyan, A note on torsion length and torsion subgroups, J. Group
Theory 26 (2023), no. 4, 741-750 (arXiv:2112.14546), Section 3, Construction 3.1 (Abels' finitely
presented soluble group H modulo an infinite cyclic central subgroup C: G = H / C has G / Tor(G) ≅ H
/ Z(H), which is not finitely presented) and Construction 3.2 (a virtually torsion-free example
built from Bestvina-Brady groups); Kourovka Archive, Problem 19.24: Yes, such groups exist, one
soluble and one virtually torsion-free, https://arxiv.org/abs/2112.14546.
-/
public theorem_wanted existsFinitelyPresentedTorsionQuotientNotFinitelyPresented_holds :
    existsFinitelyPresentedTorsionQuotientNotFinitelyPresented

end MathlibExt.GroupTheory.TorsionQuotientFinitelyPresentedKourovka19Problem24Wanted
