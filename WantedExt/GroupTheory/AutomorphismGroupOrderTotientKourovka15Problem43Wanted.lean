/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Orders of automorphism groups versus Euler's function (Kourovka Notebook Problem 15.43)

Kourovka Notebook, Archive of Solved Problems, Problem 15.43 (M. Deaconescu): let `G` be a finite
group of order `n`. (a) Is it true that `|Aut G| ≥ φ(n)`, where `φ` is Euler's function? (b) Is `G`
cyclic if `|Aut G| = φ(n)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Totient

@[expose] public section

namespace MathlibExt.GroupTheory.AutomorphismGroupOrderTotientKourovka15Problem43Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.43 (M.
Deaconescu). UnsolvedMath record UM-00701131 (`KOU-15.43`), dataset ulamai/UnsolvedMath v1.8.0.

`Aut G` is `MulAut G` and `φ` is `Nat.totient`; both parts are stated for all finite groups in
`Type`.
-/

/-- **Deaconescu's totient lower bound conjecture (Kourovka 15.43(a)).** The statement that every
finite group $G$ satisfies $\varphi(|G|) \le |\mathrm{Aut}(G)|$, where $\varphi$ is Euler's totient
function and $\mathrm{Aut}(G)$ is the group of automorphisms of $G$. -/
def totientLeAutOrder : Prop :=
  ∀ (G : Type) [Group G] [Finite G], (Nat.card G).totient ≤ Nat.card (MulAut G)

/-- **Deaconescu's cyclicity conjecture (Kourovka 15.43(b)).** The statement that every finite group
$G$ with $|\mathrm{Aut}(G)| = \varphi(|G|)$ is cyclic, where $\varphi$ is Euler's totient function
and $\mathrm{Aut}(G)$ is the group of automorphisms of $G$. -/
def autOrderEqTotientImpliesCyclic : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card (MulAut G) = (Nat.card G).totient → IsCyclic G

/--
**Deaconescu's totient lower bound conjecture fails (Kourovka 15.43(a)).** Not every finite group
$G$ satisfies $\varphi(|G|) \le |\mathrm{Aut}(G)|$: there is a finite group $G$ with
$|\mathrm{Aut}(G)| < \varphi(|G|)$, where $\varphi$ is Euler's totient function and
$\mathrm{Aut}(G)$ is the group of automorphisms of $G$.

Bray and Wilson prove more than is stated here: the ratio $|\mathrm{Aut}(G)| / \varphi(|G|)$ can be
made arbitrarily small.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.43 (M.
Deaconescu); resolution: J. N. Bray and R. A. Wilson, On the orders of automorphism groups of finite
groups, Bull. London Math. Soc. 37 (2005), no. 3, 381-385, main results (groups with |Aut G| <
φ(|G|), infinitely many non-cyclic groups with |Aut G| = φ(|G|), and |Aut G|/φ(|G|) arbitrarily
small); Kourovka Archive, Problem 15.43 (both answers negative),
https://webspace.maths.qmul.ac.uk/j.n.bray/web/Publ/AutG/.
-/
public theorem_wanted totientLeAutOrder_refuted : ¬ totientLeAutOrder

/--
**Deaconescu's cyclicity conjecture fails (Kourovka 15.43(b)).** Not every finite group $G$ with
$|\mathrm{Aut}(G)| = \varphi(|G|)$ is cyclic: there is a non-cyclic finite group $G$ with
$|\mathrm{Aut}(G)| = \varphi(|G|)$, where $\varphi$ is Euler's totient function and
$\mathrm{Aut}(G)$ is the group of automorphisms of $G$.

Bray and Wilson prove more than is stated here: there are infinitely many such non-cyclic groups.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.43 (M.
Deaconescu); resolution: J. N. Bray and R. A. Wilson, On the orders of automorphism groups of finite
groups, Bull. London Math. Soc. 37 (2005), no. 3, 381-385, main results (groups with |Aut G| <
φ(|G|), infinitely many non-cyclic groups with |Aut G| = φ(|G|), and |Aut G|/φ(|G|) arbitrarily
small); Kourovka Archive, Problem 15.43 (both answers negative),
https://webspace.maths.qmul.ac.uk/j.n.bray/web/Publ/AutG/.
-/
public theorem_wanted autOrderEqTotientImpliesCyclic_refuted : ¬ autOrderEqTotientImpliesCyclic

end MathlibExt.GroupTheory.AutomorphismGroupOrderTotientKourovka15Problem43Wanted
