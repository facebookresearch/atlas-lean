/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.ResidueChar
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

-- Original-binder consumer: a valuation subring of `AlgebraicClosure ℚ`
-- lying over `ℓ` has residue field of characteristic `ℓ`.
example (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime ℓ) : CharP (IsLocalRing.ResidueField A) ℓ :=
  ValuationSubring.charP_residueField_of_liesOverPrime A ℓ hA

-- Higher-universe consumer over a field in `Type 1`.
example {L : Type 1} [Field L] (A : ValuationSubring L) (ℓ : ℕ) [Fact ℓ.Prime]
    (hA : A.LiesOverPrime ℓ) : CharP (IsLocalRing.ResidueField A) ℓ :=
  ValuationSubring.charP_residueField_of_liesOverPrime A ℓ hA
