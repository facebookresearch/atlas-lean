/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

import MathlibExt.KTheory.Ring.K2.StableSteinbergWeylRelations
public import MathlibExt.KTheory.Ring.K2.SteinbergSymbol

/-! # Index independence of the torus cocycle

The torus cocycle does not depend on the chosen pair of distinct indices.
-/

@[expose] public section

namespace AlgebraicKTheory.StableSteinberg

universe u

/-- The torus cocycle formed using an arbitrary ordered pair of distinct indices. -/
public def torusCocycleAt {F : Type u} [Field F]
    (i j : ℕ) (hij : i ≠ j) (u v : Fˣ) : StableSteinberg F :=
  torus i j hij u * torus i j hij v * (torus i j hij (u * v))⁻¹

private theorem torusCocycleAt_conj_w_ik {F : Type u} [Field F]
    (i j k : ℕ) (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j)
    (u v : Fˣ) :
    weyl i k hik (-1 : Fˣ) * torusCocycleAt i j hij u v *
        (weyl i k hik (-1 : Fˣ))⁻¹ =
      torusCocycleAt k j hkj u v := by
  change MulAut.conj (weyl i k hik (-1 : Fˣ)) (torusCocycleAt i j hij u v) =
    torusCocycleAt k j hkj u v
  simp only [torusCocycleAt, map_mul, map_inv]
  rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply,
    torus_conj_w_ik i j k hij hik hkj u,
    torus_conj_w_ik i j k hij hik hkj v,
    torus_conj_w_ik i j k hij hik hkj (u * v)]

private theorem torusCocycleAt_conj_w_jk {F : Type u} [Field F]
    (i j k : ℕ) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (u v : Fˣ) :
    weyl j k hjk (-1 : Fˣ) * torusCocycleAt i j hij u v *
        (weyl j k hjk (-1 : Fˣ))⁻¹ =
      torusCocycleAt i k hik u v := by
  change MulAut.conj (weyl j k hjk (-1 : Fˣ)) (torusCocycleAt i j hij u v) =
    torusCocycleAt i k hik u v
  simp only [torusCocycleAt, map_mul, map_inv]
  rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply,
    torus_conj_w_jk i j k hij hjk hik u,
    torus_conj_w_jk i j k hij hjk hik v,
    torus_conj_w_jk i j k hij hjk hik (u * v)]

private theorem conj_torusCocycle_eq_self {F : Type u} [Field F]
    (g : StableSteinberg F) (u v : Fˣ) :
    g * torusCocycle u v * g⁻¹ = torusCocycle u v := by
  have hComm :
      g * torusCocycle u v = torusCocycle u v * g :=
    (Subgroup.mem_center_iff.mp (torusCocycle_mem_center u v)) g
  rw [hComm, mul_assoc, mul_inv_cancel, mul_one]

/-- The torus cocycle is independent of the chosen ordered pair of distinct indices. -/
@[simp]
public theorem torusCocycleAt_eq_torusCocycle {F : Type u} [Field F]
    (i j : ℕ) (hij : i ≠ j) (u v : Fˣ) :
    torusCocycleAt i j hij u v = torusCocycle u v := by
  let k := i + j + 2
  have hik : i ≠ k := by omega
  have hjk : j ≠ k := by omega
  have h0k : (0 : ℕ) ≠ k := by omega
  have hk1 : k ≠ 1 := by omega
  have h01 : (0 : ℕ) ≠ 1 := by omega
  have hAt01 : torusCocycleAt 0 1 h01 u v = torusCocycle u v := by
    have h_eq : h01 = (by omega : (0 : ℕ) ≠ 1) := Subsingleton.elim _ _
    rw [h_eq]
    rfl
  have hk1_eq : torusCocycleAt k 1 hk1 u v = torusCocycle u v := by
    calc torusCocycleAt k 1 hk1 u v
        = weyl 0 k h0k (-1 : Fˣ) * torusCocycleAt 0 1 h01 u v *
            (weyl 0 k h0k (-1 : Fˣ))⁻¹ := by
          rw [← torusCocycleAt_conj_w_ik 0 1 k h01 h0k hk1 u v]
      _ = weyl 0 k h0k (-1 : Fˣ) * torusCocycle u v *
            (weyl 0 k h0k (-1 : Fˣ))⁻¹ := by rw [hAt01]
      _ = torusCocycle u v := conj_torusCocycle_eq_self _ u v
  by_cases hj1 : j = 1
  · subst hj1
    calc torusCocycleAt i 1 hij u v
        = weyl k i hik.symm (-1 : Fˣ) * torusCocycleAt k 1 hk1 u v *
            (weyl k i hik.symm (-1 : Fˣ))⁻¹ := by
          rw [← torusCocycleAt_conj_w_ik k 1 i hk1 hik.symm hij u v]
      _ = weyl k i hik.symm (-1 : Fˣ) * torusCocycle u v *
            (weyl k i hik.symm (-1 : Fˣ))⁻¹ := by rw [hk1_eq]
      _ = torusCocycle u v := conj_torusCocycle_eq_self _ u v
  · have h1j : (1 : ℕ) ≠ j := fun h => hj1 h.symm
    have h_kj : torusCocycleAt k j hjk.symm u v = torusCocycle u v := by
      calc torusCocycleAt k j hjk.symm u v
          = weyl 1 j h1j (-1 : Fˣ) * torusCocycleAt k 1 hk1 u v *
              (weyl 1 j h1j (-1 : Fˣ))⁻¹ := by
            rw [← torusCocycleAt_conj_w_jk k 1 j hk1 h1j hjk.symm u v]
        _ = weyl 1 j h1j (-1 : Fˣ) * torusCocycle u v *
              (weyl 1 j h1j (-1 : Fˣ))⁻¹ := by rw [hk1_eq]
        _ = torusCocycle u v := conj_torusCocycle_eq_self _ u v
    calc torusCocycleAt i j hij u v
        = weyl k i hik.symm (-1 : Fˣ) * torusCocycleAt k j hjk.symm u v *
            (weyl k i hik.symm (-1 : Fˣ))⁻¹ := by
          rw [← torusCocycleAt_conj_w_ik k j i hjk.symm hik.symm hij u v]
      _ = weyl k i hik.symm (-1 : Fˣ) * torusCocycle u v *
            (weyl k i hik.symm (-1 : Fˣ))⁻¹ := by rw [h_kj]
      _ = torusCocycle u v := conj_torusCocycle_eq_self _ u v

end AlgebraicKTheory.StableSteinberg

end
