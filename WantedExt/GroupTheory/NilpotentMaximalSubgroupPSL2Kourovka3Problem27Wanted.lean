/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite simple groups with a nilpotent maximal subgroup (Kourovka Notebook Problem 3.27)

Kourovka Notebook, Archive of Solved Problems, Problem 3.27 (J. G. Thompson; V. D. Mazurov): is
every finite simple group with a nilpotent maximal subgroup isomorphic to some `PSL₂(q)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

@[expose] public section

namespace MathlibExt.GroupTheory.NilpotentMaximalSubgroupPSL2Kourovka3Problem27Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.27 (J. G.
Thompson; V. D. Mazurov). UnsolvedMath record UM-00700178 (`KOU-3.27`), dataset ulamai/UnsolvedMath
v1.8.0.

Simple groups are non-abelian (`ℤ/p` has the nilpotent maximal subgroup `1`). Maximal subgroups are
coatoms of the subgroup lattice; `PSL₂(q)` is `Matrix.ProjectiveSpecialLinearGroup (Fin 2) F` for
the field `F` of order `q`, stated with an arbitrary finite field.
-/

/-- Kourovka 3.27 (J. G. Thompson; V. D. Mazurov): every finite nonabelian simple group with a
nilpotent maximal subgroup is isomorphic to `PSL₂(q)` for some prime power `q`, i.e. to
`PSL₂(F)` for some finite field `F`. -/
def simpleWithNilpotentMaximalIsPSL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    (∃ M : Subgroup G, IsCoatom M ∧ Group.IsNilpotent M) →
    ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)

/--
Resolved true: the Kourovka Archive answers 3.27 "Yes, it is", citing Baumann (J. Algebra 38
(1976)): a finite non-abelian simple group with a nilpotent maximal subgroup is isomorphic to
`PSL₂(q)` for some prime power `q`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 3.27 (J. G. Thompson; V. D. Mazurov); resolution: B. Baumann, J. Algebra 38
(1976), 119-135, Kourovka Archive, Problem 3.27: Yes, it is, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted simpleWithNilpotentMaximalIsPSL2_holds : simpleWithNilpotentMaximalIsPSL2

end MathlibExt.GroupTheory.NilpotentMaximalSubgroupPSL2Kourovka3Problem27Wanted
