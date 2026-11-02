/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Quasi-identities and geometric equivalence of groups (Kourovka Notebook Problem 14.71)

Kourovka Notebook, Archive of Solved Problems, Problem 14.71 (B. I. Plotkin): groups `G` and `H` are
geometrically equivalent if `cl_G(T) = cl_H(T)` for every free group `F` of finite rank and every `T
⊆ F`, where `cl_G(T)` is the intersection of the kernels of all homomorphisms `F → G` vanishing on
`T`. If two groups have the same quasi-identities, are they geometrically equivalent?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.QuasiIdentitiesGeometricEquivalenceKourovka14Problem71Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.71 (B. I.
Plotkin). UnsolvedMath record UM-00701056 (`KOU-14.71`), dataset ulamai/UnsolvedMath v1.8.0.

Homomorphisms `F_n → G` are given by the images of the basis; `T` ranges over all subsets (possibly
infinite), which is where the two notions can differ. Quasi-identities are `∀ x (w₁ = 1 ∧ ⋯ ∧ wₖ = 1
→ w = 1)` with finitely many premises.
-/

/-- **Quasi-identities of groups.** A quasi-identity consists of a natural number $n$, a finite
list of premises $w_1, \dots, w_k$ and a conclusion $w$, all elements of the free group $F_n$ on
the unknowns $x_0, \dots, x_{n-1}$. It stands for the formula
$\forall x_0, \dots, x_{n-1}\, (w_1 = 1 \wedge \dots \wedge w_k = 1 \to w = 1)$. -/
structure QuasiIdentity where
  /-- The number of unknowns. -/
  n : ℕ
  /-- The premises `w₁, …, wₖ`. -/
  premises : List (FreeGroup (Fin n))
  /-- The conclusion `w`. -/
  conclusion : FreeGroup (Fin n)

/-- **Satisfaction of a quasi-identity in a group.** Let $q$ be a quasi-identity with unknowns
$x_0, \dots, x_{n-1}$, premises $w_1, \dots, w_k$ and conclusion $w$, all in the free group $F_n$
on $x_0, \dots, x_{n-1}$. For $g_0, \dots, g_{n-1}$ in a group $G$ and $u \in F_n$, write
$u(g_0, \dots, g_{n-1})$ for the image of $u$ under the homomorphism $F_n \to G$ sending each
$x_j$ to $g_j$. Then $q$ holds in $G$ when for all $g_0, \dots, g_{n-1} \in G$ with
$w_i(g_0, \dots, g_{n-1}) = 1$ for every premise $w_i$, also $w(g_0, \dots, g_{n-1}) = 1$. -/
def QuasiIdentity.HoldsIn (q : QuasiIdentity) (G : Type*) [Group G] : Prop :=
  ∀ x : Fin q.n → G, (∀ w ∈ q.premises, FreeGroup.lift x w = 1) →
    FreeGroup.lift x q.conclusion = 1

/-- **Closure of a set of words with respect to a group.** Let $G$ be a group, let $F_n$ be the
free group on the basis $x_0, \dots, x_{n-1}$, and let $T \subseteq F_n$. The $G$-closure
$\mathrm{cl}_G(T)$ is the set of $w \in F_n$ such that $\mu(w) = 1$ for every homomorphism
$\mu : F_n \to G$ with $\mu(t) = 1$ for all $t \in T$, that is, the intersection of the kernels
of all homomorphisms $F_n \to G$ that vanish on $T$. -/
def gClosure (G : Type*) [Group G] {n : ℕ} (T : Set (FreeGroup (Fin n))) :
    Set (FreeGroup (Fin n)) :=
  {w | ∀ x : Fin n → G, (∀ t ∈ T, FreeGroup.lift x t = 1) → FreeGroup.lift x w = 1}

/-- **Geometrically equivalent groups.** Two groups $G$ and $H$ are geometrically equivalent
(B. I. Plotkin) when $\mathrm{cl}_G(T) = \mathrm{cl}_H(T)$ for every natural number $n$ and
every subset $T$ of the free group $F_n$ of rank $n$, where $\mathrm{cl}_G(T)$ is the
$G$-closure of $T$: the intersection of the kernels of all homomorphisms $F_n \to G$ that
vanish on $T$. -/
def GeometricallyEquivalent (G H : Type*) [Group G] [Group H] : Prop :=
  ∀ (n : ℕ) (T : Set (FreeGroup (Fin n))), gClosure G T = gClosure H T

/-- **Plotkin's problem on quasi-identities and geometric equivalence.** The proposition
(Kourovka Problem 14.71, B. I. Plotkin) that any two groups $G$ and $H$ satisfying the same
quasi-identities, meaning that every quasi-identity holds in $G$ if and only if it holds in $H$,
are geometrically equivalent. -/
def sameQuasiIdentitiesImpliesGeometricallyEquivalent : Prop :=
  ∀ (G H : Type) [Group G] [Group H], (∀ q : QuasiIdentity, q.HoldsIn G ↔ q.HoldsIn H) →
    GeometricallyEquivalent G H

/--
**Groups with the same quasi-identities need not be geometrically equivalent.** The statement
of Kourovka Problem 14.71 is false: there are groups $G$ and $H$ such that every quasi-identity
holds in $G$ if and only if it holds in $H$, but $G$ and $H$ are not geometrically equivalent.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 14.71 (B. I. Plotkin); resolution: V. V. Bludov, Abstracts of the 7th Int. Conf. Groups and
Group Rings, Supraśl, 1999, p. 6; R. Göbel and S. Shelah, Proc. Amer. Math. Soc. 130 (2002),
673-674; A. G. Myasnikov and V. N. Remeslennikov, J. Algebra 234 (2000), no. 1, 225-276, Kourovka
Archive, Problem 14.71 (answer: No, not always).
-/
public theorem_wanted sameQuasiIdentitiesImpliesGeometricallyEquivalent_refuted :
    ¬ sameQuasiIdentitiesImpliesGeometricallyEquivalent

end MathlibExt.GroupTheory.QuasiIdentitiesGeometricEquivalenceKourovka14Problem71Wanted
