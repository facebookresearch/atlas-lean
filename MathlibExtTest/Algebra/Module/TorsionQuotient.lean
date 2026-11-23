/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Module.TorsionQuotient

@[expose] public section

example {K : Type*} [DivisionRing K] [CharZero K] {V : Type*} [AddCommGroup V]
    [Module K V] (L : Submodule ℤ V) [Module.Free ℤ L] [Module.Finite ℤ L]
    (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (V ⧸ L) (n : ℤ)) = n ^ Module.finrank ℤ L :=
  Submodule.natCard_torsionBy_quotient_eq_pow_finrank (K := K) L n hn

example (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (ℚ ⧸ (⊥ : Submodule ℤ ℚ)) (n : ℤ)) =
      n ^ Module.finrank ℤ (⊥ : Submodule ℤ ℚ) :=
  Submodule.natCard_torsionBy_quotient_eq_pow_finrank (K := ℚ) (⊥ : Submodule ℤ ℚ) n hn
