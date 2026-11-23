/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_RingHom_bijective_of_surjective_of_smul_eq.lean`
and
`P2M/Sol/S_RingHom_bijective_of_surjective_of_smul_eq.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Ideal.Maps

@[expose] public section

namespace RingHom

/-- A surjective ring hom `g : S →+* T` that does not change scalar action
on a nontrivial free `S`-module is bijective.

The kernel of `g` annihilates the module, and a nontrivial free module
over a commutative ring has zero annihilator. -/
public theorem bijective_of_surjective_of_smul_eq {S T N : Type*}
    [CommRing S] [Ring T] [AddCommGroup N] [Module S N] [Module T N]
    [Module.Free S N] [Nontrivial N] (g : S →+* T)
    (hg : ∀ (s : S) (n : N), g s • n = s • n)
    (hsurj : Function.Surjective g) : Function.Bijective g := by
  refine ⟨?_, hsurj⟩
  rw [injective_iff_ker_eq_bot, eq_bot_iff]
  intro s hs
  have hann : s ∈ Module.annihilator S N :=
    Module.mem_annihilator.mpr fun n => by
      rw [← hg s n, RingHom.mem_ker.mp hs, zero_smul]
  rwa [(Module.annihilator_eq_bot (R := S) (M := N)).mpr inferInstance] at hann

end RingHom
