/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite presentability in the torsion-free quasivariety (Kourovka Notebook Problem 18.17)

Kourovka Notebook, Archive of Solved Problems, Problem 18.17 (O. V. Belegradek): is there a
torsion-free group which is finitely presented in the quasivariety of torsion-free groups but not
finitely presentable in the variety of all groups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FinitelyPresentedGroup

@[expose] public section

namespace MathlibExt.GroupTheory.TorsionFreeQuasivarietyPresentationKourovka18Problem17Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.17 (O. V.
Belegradek). UnsolvedMath record UM-00701446 (`KOU-18.17`), dataset ulamai/UnsolvedMath v1.8.0.

In a quasivariety `𝔎` the group presented by `⟨X | S⟩` is `F(X) ⧸ R`, with `R` the intersection of
all normal `N ⊇ S` with `F(X) ⧸ N ∈ 𝔎`. For torsion-free groups `F(X) ⧸ N` is torsion-free exactly
when `xᵏ ∈ N, k ≥ 1` implies `x ∈ N`, so `R` is the least such normal subgroup containing `S`.
Finitely presented in `𝔎` means `X` and `S` finite; the presentation is given by a surjection from
`FreeGroup (Fin n)` with kernel `R`. Finite presentability in the variety of all groups is Mathlib's
`Group.IsFinitelyPresented`.
-/

/-- **Relation subgroup of a torsion-free presentation.** Let $n$ be a natural number, let $F_n$ be
the free group on the $n$ letters $0, 1, \dots, n - 1$, and let $S$ be a subset of $F_n$. The
relation subgroup of $S$ in the quasivariety of torsion-free groups is the intersection of all
normal subgroups $N$ of $F_n$ that contain $S$ and satisfy the following: for every $x \in F_n$
and every integer $k \ge 1$, if $x^k \in N$ then $x \in N$. Equivalently, it is the least normal
subgroup $N$ of $F_n$ containing $S$ for which $F_n / N$ is torsion-free. -/
def torsionFreeRelations {n : ℕ} (S : Set (FreeGroup (Fin n))) : Subgroup (FreeGroup (Fin n)) :=
  sInf {N | N.Normal ∧ S ⊆ N ∧ ∀ (x : FreeGroup (Fin n)) (k : ℕ), 0 < k → x ^ k ∈ N → x ∈ N}

/-- **Groups finitely presented in the torsion-free quasivariety.** A group $G$ is finitely
presented in the quasivariety of torsion-free groups if there are a natural number $n$, a finite
subset $S$ of the free group $F_n$ on $n$ letters, and a surjective homomorphism
$f \colon F_n \to G$ whose kernel is the relation subgroup of $S$ in the quasivariety of
torsion-free groups. -/
def IsTorsionFreeFinitelyPresented (G : Type) [Group G] : Prop :=
  ∃ (n : ℕ) (S : Finset (FreeGroup (Fin n))) (f : FreeGroup (Fin n) →* G),
    Function.Surjective f ∧ f.ker = torsionFreeRelations (S : Set (FreeGroup (Fin n)))

/-- **Kourovka Problem 18.17 (statement).** The statement that there is a torsion-free group $G$ (no
element of $G$ other than the identity has finite order) that is finitely presented in the
quasivariety of torsion-free groups but is not a finitely presented group.

The problem was posed by O. V. Belegradek. -/
def torsionFreePresentedNotFinitelyPresented : Prop :=
  ∃ (G : Type) (_ : Group G), (∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g) ∧
    IsTorsionFreeFinitelyPresented G ∧ ¬ Group.IsFinitelyPresented G

/--
**Budkin's theorem (Kourovka Problem 18.17).** There is a torsion-free group $G$ (no element of $G$
other than the identity has finite order) that is finitely presented in the quasivariety of
torsion-free groups but is not a finitely presented group.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.17 (O. V.
Belegradek); resolution: A. I. Budkin, Siberian Electron. Math. Rep. 14 (2017), 937-945, Kourovka
Archive, Problem 18.17: Yes, there is, http://semr.math.nsc.ru.
-/
public theorem_wanted torsionFreePresentedNotFinitelyPresented_holds :
    torsionFreePresentedNotFinitelyPresented

end MathlibExt.GroupTheory.TorsionFreeQuasivarietyPresentationKourovka18Problem17Wanted
