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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergWeyl
public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteSupport

/-!
# Steinberg products when `1 + a * b = 0`

Relates an ordered pair of elementary Steinberg generators to a Weyl element
over an arbitrary ring when the coefficient is a unit. Over a field,
specializes the relation to `1 + a * b = 0` and proves membership of the
resulting products in the next finite stage.
-/

@[expose] public section
namespace AlgebraicKTheory
namespace StableSteinberg
universe u
variable {R : Type u} [Ring R]

/-- For `i ≠ j`, `u : Rˣ`: `x j i (-(u⁻¹)) * x i j u = x i j (-u) * weyl i j u`.
Proved from `weyl` def, `x_add`, `x_zero`, and associativity; characteristic-two safe. -/
public theorem x_ji_neg_inv_mul_x_ij (i j : ℕ) (hij : i ≠ j) (u : Rˣ) :
    x j i hij.symm (-(↑u⁻¹ : R)) * x i j hij (↑u : R) =
      x i j hij (-(↑u : R)) * weyl i j hij u := by
  have h_one : x i j hij (-(↑u : R)) * x i j hij (↑u : R) = 1 := by
    rw [x_add, neg_add_cancel, x_zero]
  calc x j i hij.symm (-(↑u⁻¹ : R)) * x i j hij (↑u : R)
      = 1 * _ := by rw [one_mul]
    _ = (x i j hij (-(↑u : R)) * x i j hij (↑u : R)) * _ := by rw [h_one]
    _ = x i j hij (-(↑u : R)) * (x i j hij (↑u : R) * _) := by rw [mul_assoc]
    _ = x i j hij (-(↑u : R)) *
        (x i j hij (↑u : R) * x j i hij.symm (-(↑u⁻¹ : R)) * x i j hij (↑u : R)) := by
        rw [← mul_assoc (x i j hij (↑u : R))
            (x j i hij.symm (-(↑u⁻¹ : R)))
            (x i j hij (↑u : R))]
    _ = x i j hij (-(↑u : R)) * weyl i j hij u := rfl

/-- For `[Field F]`, `i ≠ j`, `a b : F` with `1 + a * b = 0`, we have
`x j i b * x i j a = x i j (-a) * weyl i j (Units.mk0 a ha)` where `ha : a ≠ 0`
is derived from `h`. Derives `a ≠ 0` from field nontriviality, `b = -a⁻¹`,
builds the unit from `a`, and applies `x_ji_neg_inv_mul_x_ij`. Preserves factor
order and signs; characteristic-two safe. -/
public theorem x_ji_mul_x_ij_of_one_add_mul_eq_zero {F : Type u} [Field F]
    (i j : ℕ) (hij : i ≠ j) (a b : F) (h : 1 + a * b = 0) :
    let ha : a ≠ 0 := by
      intro ha0
      rw [ha0, zero_mul, add_zero] at h
      exact one_ne_zero h
    x j i hij.symm b * x i j hij a =
      x i j hij (-a) * weyl i j hij (Units.mk0 a ha) := by
  have ha : a ≠ 0 := by
    intro ha0
    rw [ha0, zero_mul, add_zero] at h
    exact one_ne_zero h
  have hab : a * b = -1 := by
    calc a * b = 0 + a * b := by rw [zero_add]
      _ = (-1 + 1) + a * b := by rw [neg_add_cancel]
      _ = -1 + (1 + a * b) := by rw [add_assoc]
      _ = -1 + 0 := by rw [h]
      _ = -1 := by rw [add_zero]
  have hb : b = -(a⁻¹) := by
    calc b = 1 * b := by rw [one_mul]
      _ = (a⁻¹ * a) * b := by rw [inv_mul_cancel₀ ha]
      _ = a⁻¹ * (a * b) := by rw [mul_assoc]
      _ = a⁻¹ * (-1) := by rw [hab]
      _ = -(a⁻¹) := by rw [mul_neg, mul_one]
  let u : Fˣ := Units.mk0 a ha
  have hu : (u : F) = a := rfl
  have hu_inv : (↑u⁻¹ : F) = a⁻¹ := rfl
  have hb' : b = -(↑u⁻¹ : F) := by
    calc b = -(a⁻¹) := hb
      _ = -(↑u⁻¹ : F) := by rw [hu_inv]
  have hx : x j i hij.symm b * x i j hij a =
      x j i hij.symm (-(↑u⁻¹ : F)) * x i j hij (↑u : F) := by
    rw [hb', hu]
  calc x j i hij.symm b * x i j hij a
      = x j i hij.symm (-(↑u⁻¹ : F)) * x i j hij (↑u : F) := hx
    _ = x i j hij (-(↑u : F)) * weyl i j hij u := x_ji_neg_inv_mul_x_ij i j hij u
    _ = x i j hij (-a) * weyl i j hij (Units.mk0 a ha) := by rw [hu]

/-- For `[Field F]`, `hi : i < n`, `u : Fˣ`, `weyl i n (Nat.ne_of_lt hi) u`
lies in `finiteStage (R := F) (n + 1)`. The `n + 1` bound is the minimal one
carrying both `i < n + 1` and `n < n + 1`; the statement is vacuous at
`n = 0`, characteristic-two safe, and asserts only subgroup membership, not
exact torus multiplicativity nor any boundary-torus intersection statement. -/
public theorem weyl_mem_finiteStage_succ {F : Type u} [Field F]
    (i n : ℕ) (hi : i < n) (u : Fˣ) :
    weyl (R := F) i n (Nat.ne_of_lt hi) u ∈ finiteStage (R := F) (n + 1) := by
  have hi_succ : i < n + 1 := Nat.lt_trans hi (Nat.lt_succ_self n)
  have hn_succ : n < n + 1 := Nat.lt_succ_self n
  have h1 : x (R := F) i n (Nat.ne_of_lt hi) (↑u : F) ∈ finiteStage (R := F) (n + 1) :=
    x_mem_finiteStage hi_succ hn_succ
  have h2 : x (R := F) n i ((Nat.ne_of_lt hi).symm) (-(↑u⁻¹ : F)) ∈
      finiteStage (R := F) (n + 1) :=
    x_mem_finiteStage hn_succ hi_succ
  have h3 : x (R := F) i n (Nat.ne_of_lt hi) (↑u : F) ∈ finiteStage (R := F) (n + 1) :=
    x_mem_finiteStage hi_succ hn_succ
  have hw : x (R := F) i n (Nat.ne_of_lt hi) (↑u : F) *
      x (R := F) n i ((Nat.ne_of_lt hi).symm) (-(↑u⁻¹ : F)) *
      x (R := F) i n (Nat.ne_of_lt hi) (↑u : F) ∈ finiteStage (R := F) (n + 1) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h3
  have heq : weyl (R := F) i n (Nat.ne_of_lt hi) u =
      x (R := F) i n (Nat.ne_of_lt hi) (↑u : F) *
      x (R := F) n i ((Nat.ne_of_lt hi).symm) (-(↑u⁻¹ : F)) *
      x (R := F) i n (Nat.ne_of_lt hi) (↑u : F) := rfl
  rw [heq]
  exact hw

/-- For `[Field F]`, `hi : i < n`, `a b : F` with `1 + a * b = 0`, the product
`x n i b * x i n a` lies in `finiteStage (R := F) (n + 1)`. The `n + 1` bound is
minimal for `i < n + 1` and `n < n + 1`; the claim is vacuous at `n = 0`,
characteristic-two safe, and asserts only subgroup membership, not exact torus
multiplicativity nor any boundary-torus intersection statement. -/
public theorem x_n_i_mul_x_i_n_mem_finiteStage_succ_of_one_add_mul_eq_zero
    {F : Type u} [Field F] (i n : ℕ) (hi : i < n) (a b : F)
    (h : 1 + a * b = 0) :
    x (R := F) n i ((Nat.ne_of_lt hi).symm) b * x (R := F) i n (Nat.ne_of_lt hi) a ∈
      finiteStage (R := F) (n + 1) := by
  have hij : i ≠ n := Nat.ne_of_lt hi
  have ha : a ≠ 0 := by
    intro ha0
    rw [ha0, zero_mul, add_zero] at h
    exact one_ne_zero h
  have heq : x (R := F) n i ((Nat.ne_of_lt hi).symm) b *
      x (R := F) i n (Nat.ne_of_lt hi) a =
      x (R := F) i n (Nat.ne_of_lt hi) (-a) *
      weyl (R := F) i n (Nat.ne_of_lt hi) (Units.mk0 a ha) :=
    x_ji_mul_x_ij_of_one_add_mul_eq_zero i n hij a b h
  rw [heq]
  have hi_succ : i < n + 1 := Nat.lt_trans hi (Nat.lt_succ_self n)
  have hn_succ : n < n + 1 := Nat.lt_succ_self n
  have hx : x (R := F) i n (Nat.ne_of_lt hi) (-a) ∈ finiteStage (R := F) (n + 1) :=
    x_mem_finiteStage hi_succ hn_succ
  have hw : weyl (R := F) i n (Nat.ne_of_lt hi) (Units.mk0 a ha) ∈
      finiteStage (R := F) (n + 1) :=
    weyl_mem_finiteStage_succ i n hi (Units.mk0 a ha)
  exact Subgroup.mul_mem _ hx hw

end StableSteinberg
end AlgebraicKTheory
end
