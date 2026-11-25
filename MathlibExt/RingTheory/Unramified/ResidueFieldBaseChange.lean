/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_FormallyUnramified_of_residueField_baseChange_of_finite.lean`
and
`P2M/Sol/S_Algebra_FormallyUnramified_of_residueField_baseChange_of_finite.lean`
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
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Unramified.Basic

@[expose] public section

open scoped TensorProduct

namespace Algebra.FormallyUnramified

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A finite algebra over a local ring is formally unramified if its
base change to the residue field is formally unramified. -/
public theorem of_residueField_baseChange_of_finite
    (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S]
    (h : Algebra.FormallyUnramified (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] S)) :
    Algebra.FormallyUnramified R S := by
  haveI : Module.Finite S Ω[S⁄R] := inferInstance
  haveI : Module.Finite R Ω[S⁄R] := Module.Finite.trans S _
  have e := KaehlerDifferential.tensorKaehlerEquivBase R (IsLocalRing.ResidueField R) S
    (IsLocalRing.ResidueField R ⊗[R] S)
  haveI : Subsingleton Ω[(IsLocalRing.ResidueField R ⊗[R] S)⁄(IsLocalRing.ResidueField R)] :=
    h.subsingleton_kaehlerDifferential
  haveI : Subsingleton (IsLocalRing.ResidueField R ⊗[R] Ω[S⁄R]) := e.toEquiv.subsingleton
  exact ⟨(IsLocalRing.subsingleton_tensorProduct (R := R) (M := Ω[S⁄R])).mp inferInstance⟩

end Algebra.FormallyUnramified
