/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.BooleanCube
public import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Influences, variance and the noise operator on the Boolean cube

This file develops the basic analysis of real functions `f : BoolCube n → ℝ` on the Boolean
cube `{-1, 1}ⁿ` with the uniform distribution, on top of the Fourier characters `cubeChi` and
coefficients `boolFourierCoeff` of `MathlibExt.Analysis.Fourier.BooleanCube`. Expectations are
Mathlib's uniform averages `𝔼 x, f x` (`Finset.expect`).

## Main definitions

* `BooleanCube.flipCoord x i`: the point `x` with its `i`-th coordinate flipped (`x^{⊕i}`).
* `BooleanCube.boolInfluence f i`: the influence `Inf_i[f] = 𝔼ₓ[((f x - f x^{⊕i}) / 2)²]`.
* `BooleanCube.boolTotalInfluence f`: the total influence `I[f] = ∑ᵢ Inf_i[f]`.
* `BooleanCube.boolVariance f`: the variance `Var[f] = 𝔼ₓ[(f x - 𝔼 f)²]`.
* `BooleanCube.boolNoiseOp ρ f`: the noise operator `T_ρ f`.

## Main statements

* `BooleanCube.sum_boolFourierCoeff_mul_cubeChi`: Fourier inversion `f = ∑_S f̂(S) χ_S`.
* `BooleanCube.expect_mul_eq_sum_boolFourierCoeff_mul`: Plancherel, `𝔼[f g] = ∑_S f̂(S) ĝ(S)`.
  These two are the `boolFourierCoeff` forms of `BooleanCube.fourier_inversion` and
  `BooleanCube.fourier_plancherel`, which are stated for the `Finset`-indexed `fourierCoeff`.
* `BooleanCube.boolInfluence_eq_sum_sq`: `Inf_i[f] = ∑_{S ∋ i} f̂(S)²`.
* `BooleanCube.boolVariance_eq_sum_sq`: `Var[f] = ∑_{S ≠ ∅} f̂(S)²`.
* `BooleanCube.boolTotalInfluence_eq_sum_card_mul_sq`: `I[f] = ∑_S |S| f̂(S)²`.
* `BooleanCube.boolVariance_le_boolTotalInfluence`: the Poincaré inequality `Var[f] ≤ I[f]`.
* `BooleanCube.boolFourierCoeff_boolNoiseOp`: `(T_ρ f)^(S) = ρ^|S| f̂(S)`; in particular
  `T_1` is the identity (`boolNoiseOp_one`) and `T_0 f` is the constant `𝔼 f`
  (`boolNoiseOp_zero`).

## Implementation notes

The `bool` prefix follows `boolFourierCoeff`, the coefficient of a function on `BoolCube n`:
`BooleanCube.edgeInfluence` and `BooleanCube.totalInfluence` already name the influences of
set families in `MathlibExt.Analysis.Fourier.BooleanThresholds`.

## References

* R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014,
  Chapters 1 and 2.
-/

@[expose] public section

namespace BooleanCube

open scoped BigOperators

variable {n : ℕ}

/-! ### Coordinate flips -/

/-- The point `x` with its `i`-th coordinate flipped, written `x^{⊕i}`. -/
def flipCoord (x : BoolCube n) (i : Fin n) : BoolCube n :=
  Function.update x i (!x i)

/-- Flipping coordinate `i` negates that coordinate. -/
@[simp] theorem flipCoord_apply_self (x : BoolCube n) (i : Fin n) : flipCoord x i i = !x i :=
  Function.update_self ..

/-- Flipping coordinate `i` leaves every other coordinate unchanged. -/
@[simp] theorem flipCoord_apply_of_ne (x : BoolCube n) {i j : Fin n} (h : j ≠ i) :
    flipCoord x i j = x j :=
  Function.update_of_ne h ..

/-- Flipping the same coordinate twice is the identity. -/
@[simp] theorem flipCoord_flipCoord (x : BoolCube n) (i : Fin n) :
    flipCoord (flipCoord x i) i = x := by
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

/-- Flipping a fixed coordinate is an involution of the cube. -/
theorem flipCoord_involutive (i : Fin n) : Function.Involutive (flipCoord · i) :=
  fun x => flipCoord_flipCoord x i

/-- A flip moves every point. -/
theorem flipCoord_ne_self (x : BoolCube n) (i : Fin n) : flipCoord x i ≠ x := fun h => by
  simpa using congrFun h i

/-- Negating a coordinate negates its sign. -/
@[simp] theorem cubeVal_not (b : Bool) : cubeVal (!b) = -cubeVal b := by
  cases b <;> simp

/-- Coordinate signs are nonzero. -/
@[simp] theorem cubeVal_ne_zero (b : Bool) : cubeVal b ≠ 0 := by
  cases b <;> simp

/-- Every coordinate sign has absolute value one. -/
@[simp] theorem abs_cubeVal (b : Bool) : |cubeVal b| = 1 := by
  cases b <;> simp

/-- Flipping coordinate `i` negates the characters `χ_S` with `i ∈ S` and fixes the others. -/
theorem cubeChi_flipCoord (S : Finset (Fin n)) (x : BoolCube n) (i : Fin n) :
    cubeChi n S (flipCoord x i) = if i ∈ S then -cubeChi n S x else cubeChi n S x := by
  unfold cubeChi
  split_ifs with hi
  · rw [← Finset.mul_prod_erase S _ hi, ← Finset.mul_prod_erase S _ hi,
      Finset.prod_congr rfl fun j hj => by
        rw [flipCoord_apply_of_ne x (Finset.ne_of_mem_erase hj)]]
    simp
  · exact Finset.prod_congr rfl fun j hj => by
      rw [flipCoord_apply_of_ne x (ne_of_mem_of_not_mem hj hi)]

/-- Summing over the flipped points is summing over all points. -/
theorem sum_comp_flipCoord {M : Type*} [AddCommMonoid M] (f : BoolCube n → M) (i : Fin n) :
    ∑ x, f (flipCoord x i) = ∑ x, f x :=
  Fintype.sum_bijective _ (flipCoord_involutive i).bijective _ _ fun _ => rfl

/-- Averaging over the flipped points is averaging over all points. -/
theorem expect_comp_flipCoord {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (f : BoolCube n → M) (i : Fin n) : 𝔼 x, f (flipCoord x i) = 𝔼 x, f x :=
  Fintype.expect_bijective _ (flipCoord_involutive i).bijective _ _ fun _ => rfl

/-! ### Fourier expansion -/

/-- An average over the cube is the sum divided by `2 ^ n`. -/
theorem expect_eq_sum_div_two_pow (f : BoolCube n → ℝ) : 𝔼 x, f x = (∑ x, f x) / 2 ^ n := by
  rw [Fintype.expect_eq_sum_div_card, card_boolCube]
  norm_num

/-- A Fourier coefficient is the average of `f` against the character. -/
theorem boolFourierCoeff_eq_expect (f : BoolCube n → ℝ) (S : Finset (Fin n)) :
    boolFourierCoeff n f S = 𝔼 x, f x * cubeChi n S x :=
  (Fintype.expect_eq_sum_div_card _).symm

/-- A Fourier coefficient is a sum divided by `2 ^ n`. -/
theorem boolFourierCoeff_eq_sum_div_two_pow (f : BoolCube n → ℝ) (S : Finset (Fin n)) :
    boolFourierCoeff n f S = (∑ x, f x * cubeChi n S x) / 2 ^ n := by
  rw [boolFourierCoeff_eq_expect, expect_eq_sum_div_two_pow]

/-- The mean of `f` is its Fourier coefficient at `∅`. -/
theorem expect_eq_boolFourierCoeff_empty (f : BoolCube n → ℝ) :
    𝔼 x, f x = boolFourierCoeff n f ∅ := by
  simp [boolFourierCoeff_eq_expect]

/-- A sum over the cube of a coordinatewise product factors coordinate by coordinate. -/
private theorem sum_prod_eq_prod_add (g : Fin n → Bool → ℝ) :
    ∑ x : BoolCube n, ∏ i, g i (x i) = ∏ i, (g i true + g i false) := by
  calc ∑ x : BoolCube n, ∏ i, g i (x i) = ∏ i, ∑ b, g i b := (Fintype.prod_sum g).symm
    _ = ∏ i, (g i true + g i false) := by simp

/-- A character as a product over all coordinates. -/
private theorem cubeChi_eq_prod_ite (S : Finset (Fin n)) (x : BoolCube n) :
    cubeChi n S x = ∏ i, if i ∈ S then cubeVal (x i) else 1 := by
  simp [cubeChi, Finset.prod_ite_mem]

/-- Orthogonality of the Fourier characters. -/
theorem sum_cubeChi_mul_cubeChi_eq_ite (S T : Finset (Fin n)) :
    ∑ x : BoolCube n, cubeChi n S x * cubeChi n T x = if S = T then 2 ^ n else 0 := by
  have hfac := sum_prod_eq_prod_add (n := n) fun i b =>
    (if i ∈ S then cubeVal b else 1) * (if i ∈ T then cubeVal b else 1)
  beta_reduce at hfac
  simp_rw [cubeChi_eq_prod_ite, ← Finset.prod_mul_distrib]
  rw [hfac]
  split_ifs with h
  · subst h
    calc ∏ i : Fin n, ((if i ∈ S then cubeVal true else 1) * (if i ∈ S then cubeVal true else 1) +
          (if i ∈ S then cubeVal false else 1) * (if i ∈ S then cubeVal false else 1))
        = ∏ _i : Fin n, (2 : ℝ) := Finset.prod_congr rfl fun i _ => by split_ifs <;> norm_num
      _ = 2 ^ n := by simp
  · obtain ⟨i, hi⟩ : ∃ i, ¬(i ∈ S ↔ i ∈ T) := by
      by_contra! h'
      exact h (Finset.ext h')
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all

/-- The sum of a character over the cube vanishes unless the character is trivial. -/
theorem sum_cubeChi_eq_ite (S : Finset (Fin n)) :
    ∑ x : BoolCube n, cubeChi n S x = if S = ∅ then 2 ^ n else 0 := by
  simpa using sum_cubeChi_mul_cubeChi_eq_ite S ∅

/-- Dual orthogonality: summing `χ_S(x) χ_S(y)` over all `S` detects whether `x = y`. -/
theorem sum_cubeChi_apply_mul_cubeChi_apply_eq_ite (x y : BoolCube n) :
    ∑ S : Finset (Fin n), cubeChi n S x * cubeChi n S y = if x = y then 2 ^ n else 0 := by
  have h (S : Finset (Fin n)) :
      cubeChi n S x * cubeChi n S y = ∏ i ∈ S, cubeVal (x i) * cubeVal (y i) := by
    simp [cubeChi, Finset.prod_mul_distrib]
  simp_rw [h]
  rw [← Finset.powerset_univ, ← Finset.prod_one_add]
  split_ifs with hxy
  · subst hxy
    calc ∏ i : Fin n, (1 + cubeVal (x i) * cubeVal (x i)) = ∏ _i : Fin n, (2 : ℝ) :=
          Finset.prod_congr rfl fun i _ => by norm_num
      _ = 2 ^ n := by simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    cases hx : x i <;> cases hy : y i <;> simp_all

/-- Fourier inversion: a function is the sum of its Fourier expansion. -/
theorem sum_boolFourierCoeff_mul_cubeChi (f : BoolCube n → ℝ) (x : BoolCube n) :
    ∑ S, boolFourierCoeff n f S * cubeChi n S x = f x := by
  have h2 : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  calc ∑ S, boolFourierCoeff n f S * cubeChi n S x
      = (∑ y, f y * ∑ S, cubeChi n S y * cubeChi n S x) / 2 ^ n := by
        simp_rw [boolFourierCoeff_eq_sum_div_two_pow, div_mul_eq_mul_div, ← Finset.sum_div,
          Finset.sum_mul, Finset.mul_sum, mul_assoc]
        rw [Finset.sum_comm]
    _ = f x := by
        simp_rw [sum_cubeChi_apply_mul_cubeChi_apply_eq_ite, mul_ite, mul_zero]
        simp [h2]

/-- Plancherel's identity: `𝔼[f g] = ∑_S f̂(S) ĝ(S)`. -/
theorem expect_mul_eq_sum_boolFourierCoeff_mul (f g : BoolCube n → ℝ) :
    𝔼 x, f x * g x = ∑ S, boolFourierCoeff n f S * boolFourierCoeff n g S := by
  calc 𝔼 x, f x * g x = 𝔼 x, (∑ S, boolFourierCoeff n f S * cubeChi n S x) * g x := by
        simp_rw [sum_boolFourierCoeff_mul_cubeChi]
    _ = ∑ S, boolFourierCoeff n f S * 𝔼 x, g x * cubeChi n S x := by
        simp_rw [Finset.sum_mul, Finset.expect_sum_comm, Finset.mul_expect]
        refine Finset.sum_congr rfl fun S _ => Finset.expect_congr rfl fun x _ => ?_
        ring
    _ = ∑ S, boolFourierCoeff n f S * boolFourierCoeff n g S := by
        simp_rw [boolFourierCoeff_eq_expect]

/-- Parseval's identity: `𝔼[f²] = ∑_S f̂(S)²`. -/
theorem expect_sq_eq_sum_boolFourierCoeff_sq (f : BoolCube n → ℝ) :
    𝔼 x, f x ^ 2 = ∑ S, boolFourierCoeff n f S ^ 2 := by
  simpa [sq] using expect_mul_eq_sum_boolFourierCoeff_mul f f

/-- A function is determined by its Fourier coefficients. -/
theorem boolFourierCoeff_injective : Function.Injective (boolFourierCoeff n) := by
  intro f g h
  funext x
  rw [← sum_boolFourierCoeff_mul_cubeChi f x, ← sum_boolFourierCoeff_mul_cubeChi g x, h]

/-- Fourier coefficients are additive. -/
theorem boolFourierCoeff_add (f g : BoolCube n → ℝ) (S : Finset (Fin n)) :
    boolFourierCoeff n (fun x => f x + g x) S =
      boolFourierCoeff n f S + boolFourierCoeff n g S := by
  simp only [boolFourierCoeff_eq_expect, add_mul, Finset.expect_add_distrib]

/-- Fourier coefficients commute with subtraction. -/
theorem boolFourierCoeff_sub (f g : BoolCube n → ℝ) (S : Finset (Fin n)) :
    boolFourierCoeff n (fun x => f x - g x) S =
      boolFourierCoeff n f S - boolFourierCoeff n g S := by
  simp only [boolFourierCoeff_eq_expect, sub_mul, Finset.expect_sub_distrib]

/-- Fourier coefficients are homogeneous. -/
theorem boolFourierCoeff_const_mul (c : ℝ) (f : BoolCube n → ℝ) (S : Finset (Fin n)) :
    boolFourierCoeff n (fun x => c * f x) S = c * boolFourierCoeff n f S := by
  simp only [boolFourierCoeff_eq_expect, mul_assoc, Finset.mul_expect]

/-- A constant function has only the empty Fourier coefficient. -/
theorem boolFourierCoeff_const (c : ℝ) (S : Finset (Fin n)) :
    boolFourierCoeff n (fun _ => c) S = if S = ∅ then c else 0 := by
  rw [boolFourierCoeff_eq_sum_div_two_pow, ← Finset.mul_sum, sum_cubeChi_eq_ite]
  split_ifs <;> simp

/-- The Fourier coefficients of a character. -/
theorem boolFourierCoeff_cubeChi (T S : Finset (Fin n)) :
    boolFourierCoeff n (cubeChi n T) S = if T = S then 1 else 0 := by
  rw [boolFourierCoeff_eq_sum_div_two_pow, sum_cubeChi_mul_cubeChi_eq_ite]
  split_ifs <;> simp

/-- Uniqueness of the Fourier expansion: the coefficients of `∑_T a_T χ_T` are the `a_T`. -/
theorem boolFourierCoeff_sum_mul_cubeChi (a : Finset (Fin n) → ℝ) (S : Finset (Fin n)) :
    boolFourierCoeff n (fun x => ∑ T, a T * cubeChi n T x) S = a S := by
  rw [boolFourierCoeff_eq_sum_div_two_pow]
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_cubeChi_mul_cubeChi_eq_ite, mul_ite, mul_zero]
  simp

/-- Precomposing with a flip of coordinate `i` negates the coefficients at the sets
containing `i`. -/
theorem boolFourierCoeff_comp_flipCoord (f : BoolCube n → ℝ) (i : Fin n) (S : Finset (Fin n)) :
    boolFourierCoeff n (fun x => f (flipCoord x i)) S =
      if i ∈ S then -boolFourierCoeff n f S else boolFourierCoeff n f S := by
  rw [boolFourierCoeff_eq_expect, boolFourierCoeff_eq_expect,
    ← expect_comp_flipCoord (fun x => f (flipCoord x i) * cubeChi n S x) i]
  simp only [flipCoord_flipCoord, cubeChi_flipCoord]
  split_ifs
  · simp [Finset.expect_neg_distrib]
  · rfl

/-! ### Influence, total influence and variance -/

/-- The influence of coordinate `i` on `f`: `Inf_i[f] = 𝔼ₓ[((f x - f x^{⊕i}) / 2)²]`. -/
noncomputable def boolInfluence (f : BoolCube n → ℝ) (i : Fin n) : ℝ :=
  𝔼 x, ((f x - f (flipCoord x i)) / 2) ^ 2

/-- The total influence `I[f] = ∑ᵢ Inf_i[f]`. -/
noncomputable def boolTotalInfluence (f : BoolCube n → ℝ) : ℝ :=
  ∑ i, boolInfluence f i

/-- The variance `Var[f] = 𝔼ₓ[(f x - 𝔼 f)²]` under the uniform distribution. -/
noncomputable def boolVariance (f : BoolCube n → ℝ) : ℝ :=
  𝔼 x, (f x - 𝔼 y, f y) ^ 2

/-- Influences are nonnegative. -/
theorem boolInfluence_nonneg (f : BoolCube n → ℝ) (i : Fin n) : 0 ≤ boolInfluence f i :=
  Finset.expect_nonneg fun _ _ => sq_nonneg _

/-- The total influence is nonnegative. -/
theorem boolTotalInfluence_nonneg (f : BoolCube n → ℝ) : 0 ≤ boolTotalInfluence f :=
  Finset.sum_nonneg fun i _ => boolInfluence_nonneg f i

/-- The variance is nonnegative. -/
theorem boolVariance_nonneg (f : BoolCube n → ℝ) : 0 ≤ boolVariance f :=
  Finset.expect_nonneg fun _ _ => sq_nonneg _

/-- A constant function has zero influences. -/
@[simp] theorem boolInfluence_const (c : ℝ) (i : Fin n) : boolInfluence (fun _ => c) i = 0 := by
  simp [boolInfluence]

/-- A constant function has zero total influence. -/
@[simp] theorem boolTotalInfluence_const (c : ℝ) :
    boolTotalInfluence (fun _ : BoolCube n => c) = 0 := by
  simp [boolTotalInfluence]

/-- A constant function has zero variance. -/
@[simp] theorem boolVariance_const (c : ℝ) : boolVariance (fun _ : BoolCube n => c) = 0 := by
  simp [boolVariance]

/-- For a `±1`-valued function, the influence of `i` is the probability that flipping `i`
changes the value. -/
theorem boolInfluence_eq_expect_ite_ne {f : BoolCube n → ℝ} (hf : ∀ x, f x = 1 ∨ f x = -1)
    (i : Fin n) :
    boolInfluence f i = 𝔼 x, if f (flipCoord x i) ≠ f x then (1 : ℝ) else 0 := by
  refine Finset.expect_congr rfl fun x _ => ?_
  rcases hf x with h1 | h1 <;> rcases hf (flipCoord x i) with h2 | h2 <;> norm_num [h1, h2]

/-- The Fourier coefficients of the discrete derivative `(f x - f x^{⊕i}) / 2`. -/
private theorem boolFourierCoeff_derivative (f : BoolCube n → ℝ) (i : Fin n)
    (S : Finset (Fin n)) :
    boolFourierCoeff n (fun x => (f x - f (flipCoord x i)) / 2) S =
      if i ∈ S then boolFourierCoeff n f S else 0 := by
  have h : (fun x => (f x - f (flipCoord x i)) / 2) =
      fun x => (1 / 2 : ℝ) * (f x - f (flipCoord x i)) := by
    funext x
    ring
  rw [h, boolFourierCoeff_const_mul, boolFourierCoeff_sub f (fun x => f (flipCoord x i)),
    boolFourierCoeff_comp_flipCoord]
  split_ifs <;> ring

/-- `Inf_i[f] = ∑_{S ∋ i} f̂(S)²`. -/
theorem boolInfluence_eq_sum_sq (f : BoolCube n → ℝ) (i : Fin n) :
    boolInfluence f i = ∑ S with i ∈ S, boolFourierCoeff n f S ^ 2 := by
  rw [boolInfluence, expect_sq_eq_sum_boolFourierCoeff_sq (fun x => (f x - f (flipCoord x i)) / 2),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [boolFourierCoeff_derivative]
  split_ifs <;> simp

/-- `Var[f] = ∑_{S ≠ ∅} f̂(S)²`. -/
theorem boolVariance_eq_sum_sq (f : BoolCube n → ℝ) :
    boolVariance f = ∑ S with S.Nonempty, boolFourierCoeff n f S ^ 2 := by
  rw [boolVariance, expect_sq_eq_sum_boolFourierCoeff_sq (fun x => f x - 𝔼 y, f y),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [boolFourierCoeff_sub f (fun _ => 𝔼 y, f y), boolFourierCoeff_const,
    expect_eq_boolFourierCoeff_empty]
  rcases S.eq_empty_or_nonempty with hS | hS
  · simp [hS]
  · simp [hS, hS.ne_empty]

/-- `Var[f] = 𝔼[f²] - (𝔼 f)²`. -/
theorem boolVariance_eq_expect_sq_sub_sq (f : BoolCube n → ℝ) :
    boolVariance f = 𝔼 x, f x ^ 2 - (𝔼 x, f x) ^ 2 := by
  have h (x : BoolCube n) : (f x - 𝔼 y, f y) ^ 2 =
      f x ^ 2 - 2 * (𝔼 y, f y) * f x + (𝔼 y, f y) ^ 2 := by
    ring
  rw [boolVariance]
  simp_rw [h, Finset.expect_add_distrib, Finset.expect_sub_distrib, ← Finset.mul_expect,
    Fintype.expect_const]
  ring

/-- `I[f] = ∑_S |S| f̂(S)²`. -/
theorem boolTotalInfluence_eq_sum_card_mul_sq (f : BoolCube n → ℝ) :
    boolTotalInfluence f = ∑ S, (S.card : ℝ) * boolFourierCoeff n f S ^ 2 := by
  simp_rw [boolTotalInfluence, boolInfluence_eq_sum_sq, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

/-- The Poincaré inequality on the Boolean cube: `Var[f] ≤ I[f]`. -/
theorem boolVariance_le_boolTotalInfluence (f : BoolCube n → ℝ) :
    boolVariance f ≤ boolTotalInfluence f := by
  rw [boolVariance_eq_sum_sq, boolTotalInfluence_eq_sum_card_mul_sq, Finset.sum_filter]
  refine Finset.sum_le_sum fun S _ => ?_
  split_ifs with hS
  · have h1 : (1 : ℝ) ≤ S.card := by exact_mod_cast hS.card_pos
    nlinarith [sq_nonneg (boolFourierCoeff n f S)]
  · positivity

/-! ### The noise operator -/

/-- The noise operator `T_ρ`: `T_ρ f x` is the expectation of `f y` for `y` `ρ`-correlated with
`x`, i.e. each coordinate of `y` independently equals that of `x` with probability `(1 + ρ) / 2`
(for `ρ ∈ [-1, 1]`). The formula is used for every real `ρ`; `boolFourierCoeff_boolNoiseOp`
holds for all of them. -/
noncomputable def boolNoiseOp (ρ : ℝ) (f : BoolCube n → ℝ) (x : BoolCube n) : ℝ :=
  ∑ y, (∏ i, (1 + ρ * cubeVal (x i) * cubeVal (y i)) / 2) * f y

/-- The noise kernel in Fourier form. -/
private theorem prod_noiseKernel (ρ : ℝ) (x y : BoolCube n) :
    ∏ i, (1 + ρ * cubeVal (x i) * cubeVal (y i)) / 2 =
      (∑ S : Finset (Fin n), ρ ^ S.card * (cubeChi n S x * cubeChi n S y)) / 2 ^ n := by
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Finset.prod_one_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp [cubeChi, mul_assoc, Finset.prod_mul_distrib, Finset.prod_const]

/-- The Fourier expansion of `T_ρ f`. -/
theorem boolNoiseOp_eq_sum (ρ : ℝ) (f : BoolCube n → ℝ) (x : BoolCube n) :
    boolNoiseOp ρ f x = ∑ S, ρ ^ S.card * boolFourierCoeff n f S * cubeChi n S x := by
  simp only [boolNoiseOp, prod_noiseKernel, boolFourierCoeff_eq_sum_div_two_pow,
    Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun y _ => ?_
  ring

/-- The noise operator multiplies the coefficient at `S` by `ρ ^ |S|`. -/
theorem boolFourierCoeff_boolNoiseOp (ρ : ℝ) (f : BoolCube n → ℝ) (S : Finset (Fin n)) :
    boolFourierCoeff n (boolNoiseOp ρ f) S = ρ ^ S.card * boolFourierCoeff n f S := by
  have h : boolNoiseOp ρ f =
      fun x => ∑ T, (ρ ^ T.card * boolFourierCoeff n f T) * cubeChi n T x :=
    funext (boolNoiseOp_eq_sum ρ f)
  rw [h, boolFourierCoeff_sum_mul_cubeChi]

/-- `T_1` is the identity. -/
@[simp] theorem boolNoiseOp_one (f : BoolCube n → ℝ) : boolNoiseOp 1 f = f := by
  funext x
  simp [boolNoiseOp_eq_sum, sum_boolFourierCoeff_mul_cubeChi]

/-- `T_0 f` is the constant function `𝔼 f`. -/
@[simp] theorem boolNoiseOp_zero (f : BoolCube n → ℝ) : boolNoiseOp 0 f = fun _ => 𝔼 x, f x := by
  funext x
  rw [boolNoiseOp_eq_sum, Finset.sum_eq_single ∅, expect_eq_boolFourierCoeff_empty]
  · simp
  · intro S _ hS
    simp [Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS)]
  · simp

/-- The noise operators form a multiplicative semigroup: `T_ρ ∘ T_σ = T_{ρσ}`. -/
theorem boolNoiseOp_boolNoiseOp (ρ σ : ℝ) (f : BoolCube n → ℝ) :
    boolNoiseOp ρ (boolNoiseOp σ f) = boolNoiseOp (ρ * σ) f :=
  boolFourierCoeff_injective <| funext fun S => by
    simp only [boolFourierCoeff_boolNoiseOp, mul_pow]
    ring

/-- The noise operator preserves the mean. -/
theorem expect_boolNoiseOp (ρ : ℝ) (f : BoolCube n → ℝ) :
    𝔼 x, boolNoiseOp ρ f x = 𝔼 x, f x := by
  rw [expect_eq_boolFourierCoeff_empty, expect_eq_boolFourierCoeff_empty,
    boolFourierCoeff_boolNoiseOp]
  simp

/-- The characters are eigenfunctions of the noise operator. -/
theorem boolNoiseOp_cubeChi (ρ : ℝ) (S : Finset (Fin n)) :
    boolNoiseOp ρ (cubeChi n S) = fun x => ρ ^ S.card * cubeChi n S x := by
  funext x
  simp [boolNoiseOp_eq_sum, boolFourierCoeff_cubeChi]

/-- The noise operator fixes constant functions. -/
@[simp] theorem boolNoiseOp_const (ρ c : ℝ) :
    boolNoiseOp ρ (fun _ : BoolCube n => c) = fun _ => c := by
  funext x
  simp [boolNoiseOp_eq_sum, boolFourierCoeff_const]

/-- For `|ρ| ≤ 1`, the noise operator is positive: it maps nonnegative functions to nonnegative
functions. -/
theorem boolNoiseOp_nonneg {ρ : ℝ} (hρ : |ρ| ≤ 1) {f : BoolCube n → ℝ} (hf : ∀ x, 0 ≤ f x)
    (x : BoolCube n) : 0 ≤ boolNoiseOp ρ f x := by
  refine Finset.sum_nonneg fun y _ => mul_nonneg (Finset.prod_nonneg fun i _ => ?_) (hf y)
  have h : |ρ * cubeVal (x i) * cubeVal (y i)| ≤ 1 := by
    simpa [abs_mul] using hρ
  have := neg_abs_le (ρ * cubeVal (x i) * cubeVal (y i))
  linarith

end BooleanCube
