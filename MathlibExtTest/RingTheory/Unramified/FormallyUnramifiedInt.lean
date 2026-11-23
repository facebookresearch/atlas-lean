/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Unramified.FormallyUnramifiedInt

@[expose] public section

/-- Consumer with the original binders. -/
example (B : Type*) [CommRing B] [Nontrivial B] [Module.Finite ℤ B] [Module.Flat ℤ B]
    [Algebra.FormallyUnramified ℤ B] : Nonempty (B →+* ℤ) :=
  Algebra.FormallyUnramified.nonempty_ringHom_int B

/-- `ℤ` itself satisfies the hypotheses and the identity is a witness. -/
example : Nonempty (ℤ →+* ℤ) := Algebra.FormallyUnramified.nonempty_ringHom_int ℤ

/-- `ℤ × ℤ` is also a witness-bearing example: a projection is a ring hom to
`ℤ`, so it is not a counterexample. -/
example : Nonempty (ℤ × ℤ →+* ℤ) := ⟨RingHom.fst ℤ ℤ⟩
