/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Definable subgroups of free groups (Bestvina, Questions in Geometric Group Theory, Q 3.10)

M. Bestvina, Questions in Geometric Group Theory, Section 3.2 (Definable sets in `Fₙ`, Zlil Sela), Q
3.10: conjecture: the only definable subgroups of `Fₙ` are cyclic and the entire group.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.ModelTheory.Definability
public import MathlibExt.ModelTheory.GroupLanguage

@[expose] public section

namespace MathlibExt.ModelTheory.DefinableSubgroupsFreeGroupAMR10Problem0310Wanted

/-!
Source: M. Bestvina, Questions in Geometric Group Theory (updated July 2004), Q 3.10 (Zlil Sela),
https://www.math.utah.edu/~bestvina/eprints/questions-updated.pdf. UnsolvedMath record UM-01100310
(`AMR-010-0310`), dataset ulamai/UnsolvedMath v1.8.0.

The language of groups is MathlibExt's `groupLanguage` (function symbols `1`, `⁻¹`, `*`, no
relations) with its canonical structure `groupLanguageStructure`; a subgroup is definable if some
first-order formula, with elements of `Fₙ` allowed as parameters, defines it (`Set.Definable₁` over
`Set.univ`). This is the setting of Kharlampovich–Myasnikov, whose language has the generators of
`F` as constants, which is the same since every element is a term in them. `Fₙ` is `FreeGroup (Fin
n)` with `n ≥ 2` (non-abelian); cyclic subgroups include the trivial one.
-/

open FirstOrder Language

/-- Bestvina Q 3.10 (Sela): for `n ≥ 2`, every subgroup of the free group `F_n` that is first-order
definable (in the language of groups `groupLanguage`, with parameters from `F_n`) is cyclic or all
of `F_n`. -/
def definableSubgroupsCyclicOrTop : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ H : Subgroup (FreeGroup (Fin n)),
    letI := groupLanguageStructure (FreeGroup (Fin n))
    (Set.univ : Set (FreeGroup (Fin n))).Definable₁ groupLanguage (H : Set (FreeGroup (Fin n))) →
      IsCyclic H ∨ H = ⊤

/--
Resolved true: Kharlampovich and Myasnikov proved that proper non-cyclic subgroups of a non-abelian
free group of finite rank are not definable (with constants), answering Malcev's question; Perin,
Pillay, Sklinos and Tent reproved it for torsion-free hyperbolic groups. Source: M. Bestvina,
Questions in Geometric Group Theory (updated July 2004), Q 3.10 (Zlil Sela),
https://www.math.utah.edu/~bestvina/eprints/questions-updated.pdf; resolution: O. Kharlampovich and
A. Myasnikov, Definable sets in a hyperbolic group, Internat. J. Algebra Comput. 23 (2013), 91-110,
arXiv:1111.0577; also C. Perin, A. Pillay, R. Sklinos and K. Tent, On groups and fields
interpretable in torsion-free hyperbolic groups, Münster J. Math. 7 (2014), Kharlampovich–Myasnikov,
Theorem 1: "Proper non-cyclic subgroups of F and G are not definable", for F a non-abelian free
group with finite basis and formulas in the language with the generators of F as constants; answers
Malcev's 1965 question (Kourovka 1.19), https://arxiv.org/abs/1111.0577.
-/
public theorem_wanted definableSubgroupsCyclicOrTop_holds : definableSubgroupsCyclicOrTop

end MathlibExt.ModelTheory.DefinableSubgroupsFreeGroupAMR10Problem0310Wanted
