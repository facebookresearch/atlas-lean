/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Indecomposable projective modules over integral group rings (Kourovka Notebook Problem 8.34)

Kourovka Notebook, Archive of Solved Problems, Problem 8.34 (P. A. Linnell): let `G` be a finite
group. Is it true that indecomposable projective `ℤG`-modules are finitely generated (and hence
locally free)?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import WantedExt.GroupTheory.LocalizedGroupRingProjectiveKrullSchmidtKourovka4Problem55Wanted

@[expose] public section

namespace MathlibExt.Algebra.IndecomposableProjectiveGroupRingKourovka8Problem34Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.34 (P. A.
Linnell). UnsolvedMath record UM-00700486 (`KOU-8.34`), dataset ulamai/UnsolvedMath v1.8.0.

`ℤG` is `MonoidAlgebra ℤ G` and modules are left modules in `Type`. Indecomposable is
`IsIndecomposable` of the Kourovka 4.55 entry, reused here: nonzero and not the internal direct sum
of two nonzero submodules. The parenthetical "and hence locally free" is a consequence of finite
generation (Swan) and is not stated.
-/

open MathlibExt.GroupTheory.LocalizedGroupRingProjectiveKrullSchmidtKourovka4Problem55Wanted
  (IsIndecomposable)

/-- Deprecated alias of Kourovka 4.55's `IsIndecomposable`, the same definition, which the
statement below now uses. -/
@[deprecated (since := "2026-10-23")]
alias IsIndecomposableModule :=
  GroupTheory.LocalizedGroupRingProjectiveKrullSchmidtKourovka4Problem55Wanted.IsIndecomposable

/-- Kourovka 8.34 (P. A. Linnell): for a finite group `G`, every indecomposable projective
`ℤG`-module is finitely generated. -/
def indecomposableProjectiveIntegralGroupRingFG : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Type) [AddCommGroup P] [Module (MonoidAlgebra ℤ G) P],
    Module.Projective (MonoidAlgebra ℤ G) P → IsIndecomposable (MonoidAlgebra ℤ G) P →
      Module.Finite (MonoidAlgebra ℤ G) P

/--
Resolved true: the Kourovka Archive answers 8.34 "Yes, it is", citing Remark 2.13 and Corollary 4.2
of Příhoda, Fair-sized projective modules (2010), whose results on infinitely generated projective
modules apply to integral group rings of finite groups. Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 8.34 (P. A. Linnell); resolution: P. Příhoda, Fair-sized
projective modules, Rend. Sem. Mat. Univ. Padova 123 (2010), 141-167, Kourovka Archive, Problem
8.34: Yes, it is; see Remark 2.13 and Corollary 4.2 in Příhoda's paper,
https://doi.org/10.4171/RSMUP/123-7.
-/
public theorem_wanted indecomposableProjectiveIntegralGroupRingFG_holds :
    indecomposableProjectiveIntegralGroupRingFG

end MathlibExt.Algebra.IndecomposableProjectiveGroupRingKourovka8Problem34Wanted
