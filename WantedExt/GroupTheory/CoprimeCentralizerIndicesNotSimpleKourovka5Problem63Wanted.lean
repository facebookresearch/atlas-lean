/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Elements with coprime centralizer indices (Kourovka Notebook Problem 5.63)

Kourovka Notebook, Archive of Solved Problems, Problem 5.63 (S. A. Chunikhin): prove that a finite
group is not simple if it contains two non-identity elements whose centralizers have coprime
indices.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

namespace MathlibExt.GroupTheory.CoprimeCentralizerIndicesNotSimpleKourovka5Problem63Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.63 (S. A.
Chunikhin). UnsolvedMath record UM-00700342 (`KOU-5.63`), dataset ulamai/UnsolvedMath v1.8.0.

Simple means non-abelian simple: in a cyclic group of prime order every centralizer has index `1`,
so the hypothesis holds there with `x = y`, and the claim is about non-abelian simple groups.
Mathlib's `IsSimpleGroup` includes non-triviality; non-abelian is written `∃ a b, a * b ≠ b * a`.
The elements `x`, `y` need not be distinct.
-/

/-- Kourovka 5.63 (S. A. Chunikhin): a finite group with two non-identity elements whose
centralizers have coprime indices is not a non-abelian simple group. -/
def coprimeCentralizerIndicesNotSimple : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ x y : G, x ≠ 1 → y ≠ 1 →
      ¬ Nat.Coprime (Subgroup.centralizer ({x} : Set G)).index
        (Subgroup.centralizer ({y} : Set G)).index

/--
Resolved true: the Kourovka Archive records 5.63 as proved modulo the classification of finite
simple groups by Kazarin (1984): no finite non-abelian simple group has two non-identity elements
whose centralizers have coprime indices. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 5.63 (S. A. Chunikhin); resolution: L. S. Kazarin, On a problem of S. A.
Chunikhin, in: Investigations in Group Theory, Sverdlovsk, 1984, 81-99 (Russian), main theorem as
stated in the zbMATH review Zbl 0591.20018: if G is a known finite simple group (a Chevalley group,
an alternating group or one of the 26 sporadic groups) and |G : C_G(x)| is coprime to |G : C_G(y)|,
then x = 1 or y = 1, which answers Chunikhin's question modulo the classification; Kourovka Archive,
Problem 5.63: This has been proved mod CFSG (Kazarin), https://zbmath.org/?q=an:0591.20018.
-/
public theorem_wanted coprimeCentralizerIndicesNotSimple_holds : coprimeCentralizerIndicesNotSimple

end MathlibExt.GroupTheory.CoprimeCentralizerIndicesNotSimpleKourovka5Problem63Wanted
