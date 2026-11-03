/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Submodule_natCard_torsionBy_quotient_eq_pow_finrank.lean`
and
`P2M/Sol/S_Submodule_natCard_torsionBy_quotient_eq_pow_finrank.lean`
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

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.ModN
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

universe u v

namespace Submodule.LatticeQuotientTorsion

variable {K : Type u} [DivisionRing K] [CharZero K]
variable {V : Type v} [AddCommGroup V] [Module K V]

private noncomputable def divN (n : ℕ) : V →+ V :=
  DistribSMul.toAddMonoidHom V ((n : K)⁻¹)

private theorem natCast_smul_divN {n : ℕ} (hn : n ≠ 0) (v : V) :
    (n : ℤ) • divN (K := K) n v = v := by
  have hK : (n : K) ≠ 0 := by exact_mod_cast hn
  simp only [divN, DistribSMul.toAddMonoidHom_apply]
  rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul K, smul_smul, mul_inv_cancel₀ hK,
    one_smul]

private theorem divN_natCast_smul {n : ℕ} (hn : n ≠ 0) (v : V) :
    divN (K := K) n ((n : ℤ) • v) = v := by
  have hK : (n : K) ≠ 0 := by exact_mod_cast hn
  simp only [divN, DistribSMul.toAddMonoidHom_apply]
  rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hK,
    one_smul]

variable (L : Submodule ℤ V)

private noncomputable def latticeDivQuot {n : ℕ} (hn : n ≠ 0) :
    L →ₗ[ℤ] torsionBy ℤ (V ⧸ L) (n : ℤ) where
  toFun w := ⟨Submodule.Quotient.mk (divN (K := K) n (w : V)), by
    rw [mem_torsionBy_iff]
    change (Submodule.Quotient.mk ((n : ℤ) • divN (K := K) n (w : V)) : V ⧸ L) = 0
    rw [natCast_smul_divN (K := K) hn]
    exact (Submodule.Quotient.mk_eq_zero L).mpr w.2⟩
  map_add' a b := by
    apply Subtype.ext
    change (Submodule.Quotient.mk (divN (K := K) n ((a + b : L) : V)) : V ⧸ L) =
      Submodule.Quotient.mk (divN (K := K) n (a : V))
        + Submodule.Quotient.mk (divN (K := K) n (b : V))
    rw [Submodule.coe_add, map_add, Submodule.Quotient.mk_add]
  map_smul' m a := by
    apply Subtype.ext
    change (Submodule.Quotient.mk (divN (K := K) n ((m • a : L) : V)) : V ⧸ L) =
      Submodule.Quotient.mk (m • divN (K := K) n (a : V))
    rw [Submodule.coe_smul, map_zsmul]

private theorem coe_latticeDivQuot {n : ℕ} (hn : n ≠ 0) (w : L) :
    ((latticeDivQuot (K := K) L hn w : torsionBy ℤ (V ⧸ L) (n : ℤ)) : V ⧸ L)
      = Submodule.Quotient.mk (divN (K := K) n (w : V)) := rfl

private theorem latticeDivQuot_surjective {n : ℕ} (hn : n ≠ 0) :
    Function.Surjective (latticeDivQuot (K := K) L hn) := by
  rintro ⟨x, hx⟩
  rw [mem_torsionBy_iff] at hx
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective L x
  have hvL : (n : ℤ) • v ∈ L := by
    rw [← Submodule.Quotient.mk_eq_zero]
    exact hx
  refine ⟨⟨(n : ℤ) • v, hvL⟩, Subtype.ext ?_⟩
  rw [coe_latticeDivQuot]
  change (Submodule.Quotient.mk (divN (K := K) n ((n : ℤ) • v)) : V ⧸ L)
      = Submodule.Quotient.mk v
  rw [divN_natCast_smul (K := K) hn]

private theorem ker_latticeDivQuot {n : ℕ} (hn : n ≠ 0) :
    LinearMap.ker (latticeDivQuot (K := K) L hn)
      = LinearMap.range (LinearMap.lsmul ℤ L (n : ℤ)) := by
  ext w
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hker
    have hcoe : ((latticeDivQuot (K := K) L hn w : torsionBy ℤ (V ⧸ L) (n : ℤ)) :
        V ⧸ L) = 0 := by
      rw [hker]; rfl
    rw [coe_latticeDivQuot, Submodule.Quotient.mk_eq_zero] at hcoe
    refine ⟨⟨divN (K := K) n (w : V), hcoe⟩, ?_⟩
    apply Subtype.ext
    change (n : ℤ) • divN (K := K) n (w : V) = (w : V)
    exact natCast_smul_divN (K := K) hn (w : V)
  · rintro ⟨μ, rfl⟩
    apply Subtype.ext
    rw [coe_latticeDivQuot, LinearMap.lsmul_apply]
    change (Submodule.Quotient.mk (divN (K := K) n ((n : ℤ) • (μ : V))) : V ⧸ L) = 0
    rw [divN_natCast_smul (K := K) hn, Submodule.Quotient.mk_eq_zero]
    exact μ.2

/-- The `n`-torsion of `V ⧸ L` is the quotient of the lattice `L` by `n`. -/
private noncomputable def latticeQuotTorsionEquiv {n : ℕ} (hn : n ≠ 0) :
    ModN L n ≃ₗ[ℤ] torsionBy ℤ (V ⧸ L) (n : ℤ) :=
  (Submodule.quotEquivOfEq _ _ (ker_latticeDivQuot (K := K) L hn).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (latticeDivQuot_surjective (K := K) L hn))

end Submodule.LatticeQuotientTorsion

namespace Submodule

/-- The `n`-torsion of the quotient of a vector space by a free finite
lattice has cardinality `n ^ finrank L`.

This counts torsion points: for a lattice `L` of rank `r` in a vector
space, the `n`-torsion subgroup of `V ⧸ L` has `n ^ r` elements. It is
used for torsion in abelian varieties and elliptic curves, for class group
computations, and for lattice index arguments. -/
theorem natCard_torsionBy_quotient_eq_pow_finrank {K : Type*} [DivisionRing K]
    [CharZero K] {V : Type*} [AddCommGroup V] [Module K V] (L : Submodule ℤ V)
    [Module.Free ℤ L] [Module.Finite ℤ L] (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (V ⧸ L) (n : ℤ)) = n ^ Module.finrank ℤ L := by
  have _ : NeZero n := ⟨hn⟩
  rw [← Nat.card_congr
    (Submodule.LatticeQuotientTorsion.latticeQuotTorsionEquiv (K := K) L hn).toEquiv,
    ModN.natCard_eq]

end Submodule
