/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LERF solvable groups and Baumslag-Solitar subgroups (Kourovka Notebook Problem 16.2)

Kourovka Notebook, Archive of Solved Problems, Problem 16.2 (R. C. Alperin): a group `G` is
subgroup-separable if for any subgroup `H` and `x ∉ H` there is a homomorphism `f` to a finite group
with `f(x) ∉ f(H)`. Is it true that a finitely generated solvable group is locally
subgroup-separable if and only if it does not contain a solvable Baumslag-Solitar group `BS(1, n) =
⟨a, b | b a b⁻¹ = aⁿ⟩`, `n > 1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.SolvableLERFBaumslagSolitarKourovka16Problem2Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.2 (R. C.
Alperin). UnsolvedMath record UM-00701194 (`KOU-16.2`), dataset ulamai/UnsolvedMath v1.8.0.

Locally subgroup-separable is the problem's separability condition for finitely generated subgroups
(LERF), as in the resolving paper: Button states Problem 16.2 as asking whether a finitely generated
solvable group is LERF if and only if it does not contain `BS(1, m)` for `m > 1`. For all subgroups
the condition characterizes the polycyclic groups among finitely generated solvable groups (the
problem's background, Alperin). Containing `BS(1, n)` means having a subgroup isomorphic to it,
stated as an injective homomorphism from the presented group.
-/

/-- **The Baumslag–Solitar group BS(1, n).** For a natural number $n$, $\mathrm{BS}(1, n)$ is the
group with presentation $\langle a, b \mid b a b^{-1} = a^n \rangle$. -/
abbrev BS1 (n : ℕ) : Type :=
  PresentedGroup ({FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0 ^ n)⁻¹} :
    Set (FreeGroup (Fin 2)))

/-- **Separable subgroup.** A subgroup $H$ of a group $G$ is separable when for every element
$x \in G$ with $x \notin H$ there are a finite group $F$ and a group homomorphism
$f \colon G \to F$ with $f(x) \notin f(H)$. -/
def IsSeparableSubgroup {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∀ x : G, x ∉ H → ∃ (F : Type) (_ : Group F) (_ : Finite F) (f : G →* F), f x ∉ H.map f

/-- **Locally subgroup-separable (LERF) group.** A group $G$ is locally subgroup-separable, or
LERF, when every finitely generated subgroup of $G$ is separable. -/
def IsLocallySubgroupSeparable (G : Type) [Group G] : Prop :=
  ∀ H : Subgroup G, H.FG → IsSeparableSubgroup H

/-- **Kourovka Problem 16.2 (R. C. Alperin).** A finitely generated solvable group $G$ is locally
subgroup-separable if and only if there is no $n > 1$ such that $G$ has a subgroup isomorphic to
the Baumslag–Solitar group $\mathrm{BS}(1, n)$. -/
def solvableLERFIffNoBaumslagSolitar : Prop :=
  ∀ (G : Type) [Group G], Group.FG G → Group.IsSolvable G →
    (IsLocallySubgroupSeparable G ↔ ¬ ∃ n : ℕ, 1 < n ∧ ∃ f : BS1 n →* G, Function.Injective f)

/--
**Kourovka Problem 16.2 has a negative answer.** There is a finitely generated solvable group $G$
for which the following two conditions are not equivalent: $G$ is locally subgroup-separable;
there is no $n > 1$ such that $G$ has a subgroup isomorphic to the Baumslag–Solitar group
$\mathrm{BS}(1, n)$.

Button's counterexample is the solvable ascending HNN extension of
$\mathbb{Z} \times \mathbb{Z} = \langle u, v \rangle$ by the injective endomorphism
$u \mapsto u^5 v^{-1}$, $v \mapsto u^2$: it is not locally subgroup-separable but contains no
$\mathrm{BS}(1, m)$ with $m \ne 0, \pm 1$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.2 (R. C.
Alperin); resolution: J. O. Button, Strictly ascending HNN extensions in soluble groups, Ricerche
di Matematica 61 (2012), no. 1, 139-145, arXiv:1004.0197, Theorem 2.1 and the remark after it
(the soluble ascending HNN extension G = ⟨t, ℤ × ℤ⟩ with θ(u) = u⁵v⁻¹, θ(v) = u² is not LERF and
contains no BS(1, m), m ≠ 0, ±1, so the answer to Problem 16.2 is no); Kourovka Archive, Problem
16.2 (No, it is not), https://arxiv.org/abs/1004.0197.
-/
public theorem_wanted solvableLERFIffNoBaumslagSolitar_refuted : ¬ solvableLERFIffNoBaumslagSolitar

end MathlibExt.GroupTheory.SolvableLERFBaumslagSolitarKourovka16Problem2Wanted
