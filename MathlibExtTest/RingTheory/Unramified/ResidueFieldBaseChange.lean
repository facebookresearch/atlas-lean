/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_Algebra_FormallyUnramified_of_residueField_baseChange_of_finite.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.RingTheory.Unramified.ResidueFieldBaseChange

@[expose] public section

open scoped TensorProduct

private theorem exactSource (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S]
    (h : Algebra.FormallyUnramified (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] S)) :
    Algebra.FormallyUnramified R S :=
  Algebra.FormallyUnramified.of_residueField_baseChange_of_finite R S h

/-- The same criterion in a higher universe. -/
private theorem exactSourceTypeOne (R S : Type 1) [CommRing R] [IsLocalRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S]
    (h : Algebra.FormallyUnramified (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] S)) :
    Algebra.FormallyUnramified R S :=
  Algebra.FormallyUnramified.of_residueField_baseChange_of_finite R S h
