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

/-- The relation subgroup of the presentation `⟨X | S⟩` in the quasivariety of torsion-free groups:
the least normal subgroup `N ⊇ S` of the free group `F(X)` with `F(X) ⧸ N` torsion-free, i.e. with
`xᵏ ∈ N → x ∈ N` for every `k ≥ 1`. -/
def torsionFreeRelations {n : ℕ} (S : Set (FreeGroup (Fin n))) : Subgroup (FreeGroup (Fin n)) :=
  sInf {N | N.Normal ∧ S ⊆ N ∧ ∀ (x : FreeGroup (Fin n)) (k : ℕ), 0 < k → x ^ k ∈ N → x ∈ N}

/-- `G` is finitely presented in the quasivariety of torsion-free groups: `G ≅ F(X) ⧸ R` for a
finite alphabet `X`, a finite set `S` of relators and `R = torsionFreeRelations S`. -/
def IsTorsionFreeFinitelyPresented (G : Type) [Group G] : Prop :=
  ∃ (n : ℕ) (S : Finset (FreeGroup (Fin n))) (f : FreeGroup (Fin n) →* G),
    Function.Surjective f ∧ f.ker = torsionFreeRelations (S : Set (FreeGroup (Fin n)))

/-- Kourovka 18.17 (O. V. Belegradek): there is a torsion-free group that is finitely presented in
the quasivariety of torsion-free groups but not finitely presentable in the variety of all
groups. -/
def torsionFreePresentedNotFinitelyPresented : Prop :=
  ∃ (G : Type) (_ : Group G), (∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g) ∧
    IsTorsionFreeFinitelyPresented G ∧ ¬ Group.IsFinitelyPresented G

/--
Resolved true: the Kourovka Archive answers 18.17 "Yes, there is" (A. I. Budkin, 2017): some
torsion-free group is finitely presented in the quasivariety of torsion-free groups but is not a
finitely presented group. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 18.17 (O. V. Belegradek); resolution: A. I. Budkin, Siberian Electron. Math. Rep. 14 (2017),
937-945, Kourovka Archive, Problem 18.17: Yes, there is, http://semr.math.nsc.ru.
-/
public theorem_wanted torsionFreePresentedNotFinitelyPresented_holds :
    torsionFreePresentedNotFinitelyPresented

end MathlibExt.GroupTheory.TorsionFreeQuasivarietyPresentationKourovka18Problem17Wanted
