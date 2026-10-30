/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Endomorphisms determined by their values at two elements (Kourovka Notebook Problem 13.66)

Kourovka Notebook, Archive of Solved Problems, Problem 13.66 (V. E. Shpil'rain): let `F` be a (a)
free, (b) free metabelian group of finite rank, and `M` the set of endomorphisms of `F` with
non-cyclic images. Can one choose `g, h ∈ F` such that `φ, ψ ∈ M`, `φ(g) = ψ(g)` and `φ(h) = ψ(h)`
imply `φ = ψ`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.EndomorphismsDeterminedByTwoElementsKourovka13Problem66Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.66 (V. E.
Shpil'rain). UnsolvedMath record UM-00700984 (`KOU-13.66`), dataset ulamai/UnsolvedMath v1.8.0.

Ranks `n` are arbitrary finite; for `n ≤ 1` every image is cyclic, so (a) is vacuous there. (a) is
stated for every rank; (b) is stated for every rank and refuted, which says that for some finite
rank no such pair exists ("not always"). The free metabelian group of rank `n` is `F_n / F_n''`.
-/

/-- The free metabelian group `F_n / F_n''` of rank `n`. -/
abbrev FreeMetabelianGroup (n : ℕ) : Type :=
  FreeGroup (Fin n) ⧸ derivedSeries (FreeGroup (Fin n)) 2

/-- Two elements `g, h ∈ F` determine every endomorphism of `F` with non-cyclic image: if `φ`, `ψ`
have non-cyclic images and agree at `g` and at `h`, then `φ = ψ`. -/
def DeterminedByTwoElements (F : Type) [Group F] : Prop :=
  ∃ g h : F, ∀ φ ψ : F →* F, ¬ IsCyclic φ.range → ¬ IsCyclic ψ.range → φ g = ψ g →
    φ h = ψ h → φ = ψ

/-- Kourovka 13.66(a) (V. E. Shpil'rain): for every finite rank `n`, the endomorphisms of the free
group `F_n` with non-cyclic images are determined by their values at some two elements. -/
def freeGroupEndomorphismsDeterminedByTwoElements : Prop :=
  ∀ n : ℕ, DeterminedByTwoElements (FreeGroup (Fin n))

/-- Kourovka 13.66(b) (V. E. Shpil'rain): for every finite rank `n`, the endomorphisms of the free
metabelian group `M_n` with non-cyclic images are determined by their values at some two
elements. -/
def freeMetabelianEndomorphismsDeterminedByTwoElements : Prop :=
  ∀ n : ℕ, DeterminedByTwoElements (FreeMetabelianGroup n)

/--
Resolved true: the Kourovka Archive answers 13.66(a) "Yes, one can", citing Lee: for every finite
rank, endomorphisms of the free group with non-cyclic images are determined by their values at
suitable `g` and `h`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 13.66 (V. E. Shpil'rain); resolution: (a) D. Lee, J. Algebra 247 (2002), no. 2, 509-540; (b)
E. I. Timoshenko, Math. Notes 62 (1998), no. 5-6, 767-770, Kourovka Archive, Problem 13.66 (answers:
a) Yes, one can; b) No, not always).
-/
public theorem_wanted freeGroupEndomorphismsDeterminedByTwoElements_holds :
    freeGroupEndomorphismsDeterminedByTwoElements

/--
Resolved false: the Kourovka Archive answers 13.66(b) "No, not always", citing Timoshenko: for some
finite rank `n`, no two elements of the free metabelian group `M_n` determine all endomorphisms of
`M_n` with non-cyclic images. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 13.66 (V. E. Shpil'rain); resolution: (a) D. Lee, J. Algebra 247 (2002), no. 2,
509-540; (b) E. I. Timoshenko, Math. Notes 62 (1998), no. 5-6, 767-770, Kourovka Archive, Problem
13.66 (answers: a) Yes, one can; b) No, not always).
-/
public theorem_wanted freeMetabelianEndomorphismsDeterminedByTwoElements_refuted :
    ¬ freeMetabelianEndomorphismsDeterminedByTwoElements

end MathlibExt.GroupTheory.EndomorphismsDeterminedByTwoElementsKourovka13Problem66Wanted
