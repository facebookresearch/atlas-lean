/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RepresentationTheory.CuspidalGL2

@[expose] public section

open CuspidalType

-- Consumer with the original binders (characteristic zero supplies
-- `(q : K) ≠ 0` since `q` is prime).
example {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [CharZero K]
    {θ : (GaloisField q 2)ˣ →* Kˣ} {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ρ : Representation K (CuspidalType.GL2 q) V}
    (h : CuspidalType.IsCuspidalOfType θ ρ) :
    CuspidalType.IsCuspidalOfType θ ρ.dual :=
  h.dual (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)

-- Higher-universe consumer for the coefficient field and the module.
example {q : ℕ} [Fact q.Prime] {K : Type 1} [Field K] [CharZero K]
    {θ : (GaloisField q 2)ˣ →* Kˣ} {V : Type 1} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ρ : Representation K (CuspidalType.GL2 q) V}
    (h : CuspidalType.IsCuspidalOfType θ ρ) :
    CuspidalType.IsCuspidalOfType θ ρ.dual :=
  h.dual (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)

-- Positive characteristic different from `q` also works: for `q = 3` over
-- `ZMod 2`, `(3 : ZMod 2) = 1 ≠ 0`, so the averaging step still applies.
example [Fact (Nat.Prime 3)] {θ : (GaloisField 3 2)ˣ →* (ZMod 2)ˣ}
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) (CuspidalType.GL2 3) V}
    (h : CuspidalType.IsCuspidalOfType θ ρ) :
    CuspidalType.IsCuspidalOfType θ ρ.dual :=
  h.dual (by decide)

-- Boundary: the unipotent-averaging step needs `(q : K) ≠ 0`. In
-- characteristic `q` that scalar vanishes, so the hypothesis cannot be
-- dropped in general; characteristic zero is sufficient but not necessary.
example (q : ℕ) [Fact q.Prime] : ((q : ZMod q) : ZMod q) = 0 := by
  simp
