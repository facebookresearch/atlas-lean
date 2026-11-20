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

-- Consumer with the original binders.
example {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [CharZero K]
    {θ : (GaloisField q 2)ˣ →* Kˣ} {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ρ : Representation K (CuspidalType.GL2 q) V}
    (h : CuspidalType.IsCuspidalOfType θ ρ) :
    CuspidalType.IsCuspidalOfType θ ρ.dual :=
  h.dual

-- Higher-universe consumer for the coefficient field and the module.
example {q : ℕ} [Fact q.Prime] {K : Type 1} [Field K] [CharZero K]
    {θ : (GaloisField q 2)ˣ →* Kˣ} {V : Type 1} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ρ : Representation K (CuspidalType.GL2 q) V}
    (h : CuspidalType.IsCuspidalOfType θ ρ) :
    CuspidalType.IsCuspidalOfType θ ρ.dual :=
  h.dual

-- Boundary: the unipotent-averaging step divides by `q`; in characteristic
-- `q` the scalar `(q : K)` vanishes, so characteristic zero is essential.
example (q : ℕ) [Fact q.Prime] : ((q : ZMod q) : ZMod q) = 0 := by
  simp
