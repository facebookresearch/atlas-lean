/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Direct summands of direct sums of finitely generated modules (Kourovka Notebook Problem 2.33)

Kourovka Notebook, Archive of Solved Problems, Problem 2.33 (V. I. Kuz'minov): is a direct summand
of a direct sum of finitely generated modules over a Noetherian ring again a direct sum of finitely
generated modules?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

namespace MathlibExt.Algebra.DirectSummandFGModulesKourovka2Problem33Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.33 (V. I.
Kuz'minov). UnsolvedMath record UM-00700107 (`KOU-2.33`), dataset ulamai/UnsolvedMath v1.8.0.

Rings are associative with `1` and not necessarily commutative; Noetherian is Mathlib's
`IsNoetherianRing` (ascending chain condition on left ideals) and modules are left modules. A direct
summand is a complemented submodule `N` of `⨁ i, M i`; both families are indexed by arbitrary types.
The resolving ring is the integral group ring `ℤG` of a finite non-soluble group `G`, which is
Noetherian on both sides.
-/

/-- Kourovka 2.33 (V. I. Kuz'minov): over a Noetherian ring `R`, every direct summand `N` of a
direct sum `⨁ i, M i` of finitely generated left `R`-modules is isomorphic to a direct sum of
finitely generated left `R`-modules. -/
def directSummandOfSumOfFGModulesIsSumOfFG : Prop :=
  ∀ (R : Type) [Ring R] [IsNoetherianRing R] (ι : Type) (M : ι → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)], (∀ i, Module.Finite R (M i)) →
    ∀ N : Submodule R (DirectSum ι M), (∃ N' : Submodule R (DirectSum ι M), IsCompl N N') →
      ∃ (κ : Type) (P : κ → Type) (_ : ∀ k, AddCommGroup (P k)) (_ : ∀ k, Module R (P k)),
        (∀ k, Module.Finite R (P k)) ∧ Nonempty (N ≃ₗ[R] DirectSum κ P)

/--
Resolved false: the Kourovka Archive answers 2.33 "Not always", citing Linnell (1982). For a finite
non-soluble group `G`, Akasaki and Linnell found an infinitely generated projective `ℤG`-module `P`
that is not free; since every finitely generated projective `ℤG`-module is a generator, `P` has no
finitely generated direct summand, so `P`, a direct summand of a free module `⨁ ℤG`, is not a direct
sum of finitely generated modules (as recalled by Linnell, Puninski and Smith). Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.33 (V. I. Kuz'minov);
resolution: P. A. Linnell, Nonfree projective modules for integral group rings, Bull. London Math.
Soc. 14 (1982), 124-126; see also P. A. Linnell, G. Puninski and P. Smith, Idempotent ideals and
non-finitely generated projective modules over integral group rings of polycyclic-by-finite groups,
arXiv:math/0512446, Kourovka Archive, Problem 2.33: Not always (Linnell); Linnell-Puninski-Smith,
Introduction: for a finite non-soluble group G there is an infinitely generated projective ZG-module
that is not free and has no finitely generated direct summands, https://arxiv.org/abs/math/0512446.
-/
public theorem_wanted directSummandOfSumOfFGModulesIsSumOfFG_refuted :
    ¬ directSummandOfSumOfFGModulesIsSumOfFG

end MathlibExt.Algebra.DirectSummandFGModulesKourovka2Problem33Wanted
