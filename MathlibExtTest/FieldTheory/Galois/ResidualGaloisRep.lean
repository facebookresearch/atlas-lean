/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Galois.ResidualGaloisRep

@[expose] public section

universe u

/-- Consumer with the original binders. -/
example {k : Type} [Field k] (ρ : ResidualGaloisRep k) (h2 : (2 : k) ≠ 0)
    (hirr : ρ.IsIrreducible) (hodd : ρ.IsOdd) :
    ρ.IsAbsolutelyIrreducible :=
  ρ.isAbsolutelyIrreducible_of_isIrreducible_of_isOdd h2 hirr hodd

/-- Higher-universe consumer. -/
example {k : Type (u + 1)} [Field k] (ρ : ResidualGaloisRep k)
    (h2 : (2 : k) ≠ 0) (hirr : ρ.IsIrreducible) (hodd : ρ.IsOdd) :
    ρ.IsAbsolutelyIrreducible :=
  ρ.isAbsolutelyIrreducible_of_isIrreducible_of_isOdd h2 hirr hodd

/-- Boundary: in characteristic `2`, `-1 = 1`, so the determinant condition
in the definition of oddness cannot distinguish a conjugation from the
identity in the way the proof uses; the hypothesis `(2 : k) ≠ 0` is the
characteristic restriction in the statement. -/
example : (2 : ZMod 2) = 0 := by decide
