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

/-- **Coordinate flip on the Boolean cube.** For a point $x$ of the Boolean cube of dimension $n$
and a coordinate $i \in \{0, \dots, n-1\}$, the point $x^{\oplus i}$ is obtained from $x$ by
negating its $i$-th coordinate (exchanging true and false) and leaving every other coordinate
unchanged. -/
def flipCoord (x : BoolCube n) (i : Fin n) : BoolCube n :=
  Function.update x i (!x i)

/-- **A coordinate flip negates the flipped coordinate.** For every point $x$ of the Boolean cube
of dimension $n$ and every coordinate $i \in \{0, \dots, n-1\}$, the $i$-th coordinate of
$x^{\oplus i}$, the point $x$ with its $i$-th coordinate flipped, is the negation $\lnot x_i$ of
$x_i$ (true and false exchanged). -/
@[simp] theorem flipCoord_apply_self (x : BoolCube n) (i : Fin n) : flipCoord x i i = !x i :=
  Function.update_self ..

/-- **A coordinate flip fixes the other coordinates.** For every point $x$ of the Boolean cube of
dimension $n$ and all coordinates $i, j \in \{0, \dots, n-1\}$ with $j \ne i$, the $j$-th
coordinate of $x^{\oplus i}$, the point $x$ with its $i$-th coordinate flipped, is $x_j$. -/
@[simp] theorem flipCoord_apply_of_ne (x : BoolCube n) {i j : Fin n} (h : j ≠ i) :
    flipCoord x i j = x j :=
  Function.update_of_ne h ..

/-- **Flipping a coordinate twice.** For every point $x$ of the Boolean cube of dimension $n$ and
every coordinate $i \in \{0, \dots, n-1\}$, writing $x^{\oplus i}$ for $x$ with its $i$-th
coordinate flipped, we have $(x^{\oplus i})^{\oplus i} = x$. -/
@[simp] theorem flipCoord_flipCoord (x : BoolCube n) (i : Fin n) :
    flipCoord (flipCoord x i) i = x := by
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

/-- **Flipping a coordinate is an involution.** For every $n \in \mathbb{N}$ and every coordinate
$i \in \{0, \dots, n-1\}$, the map $x \mapsto x^{\oplus i}$ on the Boolean cube of dimension $n$,
which flips the $i$-th coordinate, is an involution: applying it twice gives the identity. -/
theorem flipCoord_involutive (i : Fin n) : Function.Involutive (flipCoord · i) :=
  fun x => flipCoord_flipCoord x i

/-- **A coordinate flip moves every point.** For every point $x$ of the Boolean cube of dimension
$n$ and every coordinate $i \in \{0, \dots, n-1\}$, the point $x^{\oplus i}$ obtained from $x$ by
flipping its $i$-th coordinate is different from $x$. -/
theorem flipCoord_ne_self (x : BoolCube n) (i : Fin n) : flipCoord x i ≠ x := fun h => by
  simpa using congrFun h i

/-- **Sign of a negated Boolean value.** For every Boolean value $b$, the sign of its negation
is the negative of its sign: $\sigma(\lnot b) = -\sigma(b)$, where $\sigma(\text{true}) = 1$
and $\sigma(\text{false}) = -1$. -/
@[simp] theorem cubeVal_not (b : Bool) : cubeVal (!b) = -cubeVal b := by
  cases b <;> simp

/-- **Coordinate signs are nonzero.** For every Boolean value $b$, its sign $\sigma(b)$ (equal
to $1$ for true and $-1$ for false) is nonzero. -/
@[simp] theorem cubeVal_ne_zero (b : Bool) : cubeVal b ≠ 0 := by
  cases b <;> simp

/-- **Coordinate signs have absolute value one.** For every Boolean value $b$, its sign $\sigma(b)$,
which is $1$ for true and $-1$ for false, satisfies $|\sigma(b)| = 1$. -/
@[simp] theorem abs_cubeVal (b : Bool) : |cubeVal b| = 1 := by
  cases b <;> simp

/-- **Flipping a coordinate in a Fourier character.** Let $S \subseteq \{0, \dots, n-1\}$, let
$x$ be a point of the Boolean cube in $n$ coordinates, let $i < n$, and write $x^{\oplus i}$ for
$x$ with coordinate $i$ flipped. Then the Fourier character $\chi_S$ satisfies
$\chi_S(x^{\oplus i}) = -\chi_S(x)$ if $i \in S$, and $\chi_S(x^{\oplus i}) = \chi_S(x)$ if
$i \notin S$. -/
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

/-- **Flipping a coordinate preserves sums over the cube.** Let $M$ be an additive commutative
monoid, $n \in \mathbb{N}$, $f$ a function from the Boolean cube of dimension $n$ to $M$, and
$i \in \{0, \dots, n-1\}$. For a point $x$ of the cube write $x^{\oplus i}$ for the point $x$ with
its $i$-th coordinate flipped. Then $\sum_x f(x^{\oplus i}) = \sum_x f(x)$, both sums ranging over
all points $x$ of the cube. -/
theorem sum_comp_flipCoord {M : Type*} [AddCommMonoid M] (f : BoolCube n → M) (i : Fin n) :
    ∑ x, f (flipCoord x i) = ∑ x, f x :=
  Fintype.sum_bijective _ (flipCoord_involutive i).bijective _ _ fun _ => rfl

/-- **Averages are invariant under flipping a coordinate.** Let $M$ be an additive commutative
monoid that is a module over the nonnegative rationals, let $f$ be a function from the Boolean
cube in $n$ coordinates to $M$, and let $i < n$. Writing $x^{\oplus i}$ for $x$ with coordinate
$i$ flipped, the uniform average of $f(x^{\oplus i})$ over all points $x$ of the cube equals the
uniform average of $f(x)$. -/
theorem expect_comp_flipCoord {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (f : BoolCube n → M) (i : Fin n) : 𝔼 x, f (flipCoord x i) = 𝔼 x, f x :=
  Fintype.expect_bijective _ (flipCoord_involutive i).bijective _ _ fun _ => rfl

/-! ### Fourier expansion -/

/-- **Uniform average over the Boolean cube as a sum.** For every $n \in \mathbb{N}$ and every
function $f : \{-1, 1\}^n \to \mathbb{R}$, the uniform average of $f$ over the Boolean cube
$\{-1, 1\}^n$ is $\mathbb{E}_x f(x) = \frac{1}{2^n} \sum_{x \in \{-1, 1\}^n} f(x)$. -/
theorem expect_eq_sum_div_two_pow (f : BoolCube n → ℝ) : 𝔼 x, f x = (∑ x, f x) / 2 ^ n := by
  rw [Fintype.expect_eq_sum_div_card, card_boolCube]
  norm_num

/-- **Fourier coefficients as averages.** For every real-valued function $f$ on the Boolean cube
in $n$ coordinates and every set $S$ of the $n$ coordinates, the Fourier coefficient $\hat f(S)$
is the average of $f(x) \chi_S(x)$ over all points $x$ of the cube,
$\hat f(S) = \mathbb{E}_x [f(x) \chi_S(x)]$, where $\chi_S$ is the Fourier character of $S$. -/
theorem boolFourierCoeff_eq_expect (f : BoolCube n → ℝ) (S : Finset (Fin n)) :
    boolFourierCoeff n f S = 𝔼 x, f x * cubeChi n S x :=
  (Fintype.expect_eq_sum_div_card _).symm

/-- **Fourier coefficients as sums over the cube.** For every real-valued function $f$ on the
Boolean cube in $n$ coordinates and every set $S$ of the $n$ coordinates, the Fourier coefficient
of $f$ at $S$ is $\hat f(S) = \frac{1}{2^n} \sum_x f(x) \chi_S(x)$, where the sum runs over all
points $x$ of the cube and $\chi_S$ is the Fourier character of $S$. -/
theorem boolFourierCoeff_eq_sum_div_two_pow (f : BoolCube n → ℝ) (S : Finset (Fin n)) :
    boolFourierCoeff n f S = (∑ x, f x * cubeChi n S x) / 2 ^ n := by
  rw [boolFourierCoeff_eq_expect, expect_eq_sum_div_two_pow]

/-- **Average over the Boolean cube as the empty Fourier coefficient.** For every $n \in \mathbb{N}$
and every function $f : \{-1, 1\}^n \to \mathbb{R}$, the uniform average $\mathbb{E}_x f(x)$ of $f$
over the Boolean cube $\{-1, 1\}^n$ equals the Fourier coefficient $\hat f(\emptyset)$ of $f$ at
the empty set. -/
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

/-- **Orthogonality of the Boolean cube characters.** Let $n \in \mathbb{N}$, let $S$ and $T$ be
subsets of $\{0, \dots, n-1\}$, and let $\chi_S$ and $\chi_T$ be their Fourier characters. Then
$\sum_x \chi_S(x) \chi_T(x)$, the sum ranging over all points $x$ of the Boolean cube of dimension
$n$, equals $2^n$ if $S = T$ and $0$ otherwise. -/
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

/-- **Sum of a Boolean cube character.** For every $n \in \mathbb{N}$ and every subset $S$ of
$\{0, \dots, n-1\}$, the sum of the Fourier character $\chi_S$ over all points of the Boolean cube
of dimension $n$ equals $2^n$ if $S$ is empty and $0$ otherwise. -/
theorem sum_cubeChi_eq_ite (S : Finset (Fin n)) :
    ∑ x : BoolCube n, cubeChi n S x = if S = ∅ then 2 ^ n else 0 := by
  simpa using sum_cubeChi_mul_cubeChi_eq_ite S ∅

/-- **Dual orthogonality of the Boolean cube characters.** Let $n \in \mathbb{N}$ and let $x, y$ be
points of the Boolean cube of dimension $n$. For each subset $S$ of $\{0, \dots, n-1\}$ let
$\chi_S$ be the Fourier character of $S$. Then $\sum_S \chi_S(x) \chi_S(y)$, the sum ranging over
all subsets $S$ of $\{0, \dots, n-1\}$, equals $2^n$ if $x = y$ and $0$ otherwise. -/
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

/-- **Fourier inversion on the Boolean cube.** Let $n \in \mathbb{N}$, let $f$ be a real-valued
function on the Boolean cube of dimension $n$, and let $x$ be a point of the cube. For each subset
$S$ of $\{0, \dots, n-1\}$ let $\hat f(S)$ be the Fourier coefficient of $f$ at $S$ and $\chi_S$
the Fourier character of $S$. Then $\sum_S \hat f(S) \chi_S(x) = f(x)$, the sum ranging over all
subsets $S$ of $\{0, \dots, n-1\}$. -/
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

/-- **Plancherel's identity on the Boolean cube.** For every $n \in \mathbb{N}$ and all functions
$f, g : \{-1, 1\}^n \to \mathbb{R}$, the uniform average of $f g$ over the Boolean cube
$\{-1, 1\}^n$ is the sum, over all sets $S \subseteq \{0, \dots, n-1\}$, of the products of the
Fourier coefficients of $f$ and $g$ at $S$:
$\mathbb{E}_x f(x) g(x) = \sum_S \hat f(S) \hat g(S)$. -/
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

/-- **Parseval's identity on the Boolean cube.** For every $n \in \mathbb{N}$ and every function
$f : \{-1, 1\}^n \to \mathbb{R}$, the uniform average of $f^2$ over the Boolean cube $\{-1, 1\}^n$
is the sum, over all sets $S \subseteq \{0, \dots, n-1\}$, of the squares of the Fourier
coefficients of $f$ at $S$: $\mathbb{E}_x f(x)^2 = \sum_S \hat f(S)^2$. -/
theorem expect_sq_eq_sum_boolFourierCoeff_sq (f : BoolCube n → ℝ) :
    𝔼 x, f x ^ 2 = ∑ S, boolFourierCoeff n f S ^ 2 := by
  simpa [sq] using expect_mul_eq_sum_boolFourierCoeff_mul f f

/-- **Fourier coefficients determine the function.** If two real-valued functions $f$ and $g$ on
the Boolean cube in $n$ coordinates have the same Fourier coefficient $\hat f(S) = \hat g(S)$ at
every set $S$ of the $n$ coordinates, then $f = g$. -/
theorem boolFourierCoeff_injective : Function.Injective (boolFourierCoeff n) := by
  intro f g h
  funext x
  rw [← sum_boolFourierCoeff_mul_cubeChi f x, ← sum_boolFourierCoeff_mul_cubeChi g x, h]

/-- **Additivity of Fourier coefficients.** For all real-valued functions $f$ and $g$ on the
Boolean cube in $n$ coordinates and every set $S$ of the $n$ coordinates, the Fourier coefficient
of $f + g$ at $S$ is the sum of the Fourier coefficients of $f$ and $g$ at $S$:
$\widehat{f + g}(S) = \hat f(S) + \hat g(S)$. -/
theorem boolFourierCoeff_add (f g : BoolCube n → ℝ) (S : Finset (Fin n)) :
    boolFourierCoeff n (fun x => f x + g x) S =
      boolFourierCoeff n f S + boolFourierCoeff n g S := by
  simp only [boolFourierCoeff_eq_expect, add_mul, Finset.expect_add_distrib]

/-- **Fourier coefficients of a difference.** For real-valued functions $f$ and $g$ on the
Boolean cube $\{-1, 1\}^n$ and every set $S \subseteq \{0, \dots, n-1\}$, the Fourier coefficient
of $f - g$ at $S$ is $\widehat{f - g}(S) = \hat f(S) - \hat g(S)$. -/
theorem boolFourierCoeff_sub (f g : BoolCube n → ℝ) (S : Finset (Fin n)) :
    boolFourierCoeff n (fun x => f x - g x) S =
      boolFourierCoeff n f S - boolFourierCoeff n g S := by
  simp only [boolFourierCoeff_eq_expect, sub_mul, Finset.expect_sub_distrib]

/-- **Homogeneity of Fourier coefficients.** For every real $c$, every real-valued function $f$
on the Boolean cube in $n$ coordinates and every set $S$ of the $n$ coordinates, the Fourier
coefficient of $c f$ at $S$ is $c$ times the Fourier coefficient of $f$ at $S$:
$\widehat{c f}(S) = c \hat f(S)$. -/
theorem boolFourierCoeff_const_mul (c : ℝ) (f : BoolCube n → ℝ) (S : Finset (Fin n)) :
    boolFourierCoeff n (fun x => c * f x) S = c * boolFourierCoeff n f S := by
  simp only [boolFourierCoeff_eq_expect, mul_assoc, Finset.mul_expect]

/-- **Fourier coefficients of a constant function.** For every real $c$ and every set $S$ of the
$n$ coordinates, the Fourier coefficient at $S$ of the constant function $x \mapsto c$ on the
Boolean cube in $n$ coordinates is $c$ if $S = \emptyset$ and $0$ otherwise. -/
theorem boolFourierCoeff_const (c : ℝ) (S : Finset (Fin n)) :
    boolFourierCoeff n (fun _ => c) S = if S = ∅ then c else 0 := by
  rw [boolFourierCoeff_eq_sum_div_two_pow, ← Finset.mul_sum, sum_cubeChi_eq_ite]
  split_ifs <;> simp

/-- **Fourier coefficients of a character.** For all sets $S$ and $T$ of the $n$ coordinates, the
Fourier coefficient at $S$ of the Fourier character $\chi_T$ on the Boolean cube in $n$
coordinates, $\chi_T(x) = \prod_{i \in T} \sigma(x_i)$ with $\sigma(\text{true}) = 1$ and
$\sigma(\text{false}) = -1$, is $1$ if $T = S$ and $0$ otherwise. -/
theorem boolFourierCoeff_cubeChi (T S : Finset (Fin n)) :
    boolFourierCoeff n (cubeChi n T) S = if T = S then 1 else 0 := by
  rw [boolFourierCoeff_eq_sum_div_two_pow, sum_cubeChi_mul_cubeChi_eq_ite]
  split_ifs <;> simp

/-- **Uniqueness of the Fourier expansion.** For real numbers $a_T$ indexed by the sets
$T \subseteq \{0, \dots, n-1\}$, let $g(x) = \sum_T a_T \chi_T(x)$ on the Boolean cube
$\{-1, 1\}^n$, where $\chi_T$ is the Fourier character of $T$. Then for every set
$S \subseteq \{0, \dots, n-1\}$ the Fourier coefficient of $g$ at $S$ is $\hat g(S) = a_S$. -/
theorem boolFourierCoeff_sum_mul_cubeChi (a : Finset (Fin n) → ℝ) (S : Finset (Fin n)) :
    boolFourierCoeff n (fun x => ∑ T, a T * cubeChi n T x) S = a S := by
  rw [boolFourierCoeff_eq_sum_div_two_pow]
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_cubeChi_mul_cubeChi_eq_ite, mul_ite, mul_zero]
  simp

/-- **Flipping a coordinate negates the Fourier coefficients of the sets containing it.** Let $f$
be a real-valued function on the Boolean cube in $n$ coordinates, let $i$ be a coordinate, and
let $g(x) = f(x^{\oplus i})$, where $x^{\oplus i}$ is the point $x$ with its $i$-th coordinate
flipped. Write $\hat f(S)$ and $\hat g(S)$ for the Fourier coefficients of $f$ and $g$ at a set
$S$ of the $n$ coordinates. Then for every such $S$, $\hat g(S) = -\hat f(S)$ if $i \in S$ and
$\hat g(S) = \hat f(S)$ if $i \notin S$. -/
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

/-- **Influence of a coordinate.** For a real-valued function $f$ on the Boolean cube
$\{-1, 1\}^n$ and a coordinate $i \in \{0, \dots, n-1\}$, the influence of $i$ on $f$ is
$\mathrm{Inf}_i[f] = \mathbb{E}_x\big[\big((f(x) - f(x^{\oplus i})) / 2\big)^2\big]$, where the
expectation is over $x$ uniform on the cube and $x^{\oplus i}$ is $x$ with its $i$-th coordinate
flipped. -/
noncomputable def boolInfluence (f : BoolCube n → ℝ) (i : Fin n) : ℝ :=
  𝔼 x, ((f x - f (flipCoord x i)) / 2) ^ 2

/-- **Total influence on the Boolean cube.** For a function $f$ from the Boolean cube
$\{-1, 1\}^n$ to $\mathbb{R}$, the total influence of $f$ is the sum of the influences of its $n$
coordinates, $\mathrm{I}[f] = \sum_{i=0}^{n-1} \mathrm{Inf}_i[f]$, where
$\mathrm{Inf}_i[f] = \mathbb{E}_x \left[\left(\frac{f(x) - f(x^{\oplus i})}{2}\right)^2\right]$,
$x^{\oplus i}$ is $x$ with its $i$-th coordinate flipped and $\mathbb{E}_x$ is the uniform average
over the points $x$ of the cube. -/
noncomputable def boolTotalInfluence (f : BoolCube n → ℝ) : ℝ :=
  ∑ i, boolInfluence f i

/-- **Variance on the Boolean cube.** For a function $f : \{-1, 1\}^n \to \mathbb{R}$ on the
Boolean cube, its variance under the uniform distribution is
$\mathrm{Var}[f] = \mathbb{E}_x\big[(f(x) - \mathbb{E}_y[f(y)])^2\big]$, where $\mathbb{E}_x$
denotes the uniform average over the $2^n$ points $x$ of the cube. -/
noncomputable def boolVariance (f : BoolCube n → ℝ) : ℝ :=
  𝔼 x, (f x - 𝔼 y, f y) ^ 2

/-- **Influences are nonnegative.** For every real-valued function $f$ on the Boolean cube
$\{-1, 1\}^n$ and every coordinate $i \in \{0, \dots, n-1\}$, the influence $\mathrm{Inf}_i[f]$ of
coordinate $i$ on $f$ satisfies $\mathrm{Inf}_i[f] \ge 0$. -/
theorem boolInfluence_nonneg (f : BoolCube n → ℝ) (i : Fin n) : 0 ≤ boolInfluence f i :=
  Finset.expect_nonneg fun _ _ => sq_nonneg _

/-- **Total influence is nonnegative.** For every function $f$ from the Boolean cube
$\{-1, 1\}^n$ to $\mathbb{R}$, the total influence of $f$ is nonnegative. -/
theorem boolTotalInfluence_nonneg (f : BoolCube n → ℝ) : 0 ≤ boolTotalInfluence f :=
  Finset.sum_nonneg fun i _ => boolInfluence_nonneg f i

/-- **Variance on the Boolean cube is nonnegative.** For every function
$f : \{-1, 1\}^n \to \mathbb{R}$ on the Boolean cube, the variance of $f$ under the uniform
distribution is at least $0$. -/
theorem boolVariance_nonneg (f : BoolCube n → ℝ) : 0 ≤ boolVariance f :=
  Finset.expect_nonneg fun _ _ => sq_nonneg _

/-- **Constant functions have zero influence.** For every real number $c$ and every coordinate
$i \in \{0, \dots, n-1\}$, the influence of coordinate $i$ on the constant function with value $c$
on the Boolean cube $\{-1, 1\}^n$ is $0$. -/
@[simp] theorem boolInfluence_const (c : ℝ) (i : Fin n) : boolInfluence (fun _ => c) i = 0 := by
  simp [boolInfluence]

/-- **Constant functions have zero total influence.** For every real number $c$, the constant
function with value $c$ on the Boolean cube $\{-1, 1\}^n$ has total influence $0$. -/
@[simp] theorem boolTotalInfluence_const (c : ℝ) :
    boolTotalInfluence (fun _ : BoolCube n => c) = 0 := by
  simp [boolTotalInfluence]

/-- **Constant functions have zero variance.** For every real number $c$, the constant function
with value $c$ on the Boolean cube $\{-1, 1\}^n$ has variance $0$ under the uniform
distribution. -/
@[simp] theorem boolVariance_const (c : ℝ) : boolVariance (fun _ : BoolCube n => c) = 0 := by
  simp [boolVariance]

/-- **Influence of a Boolean function as a flip probability.** Let $f$ be a real-valued function
on the Boolean cube $\{-1, 1\}^n$ that takes only the values $1$ and $-1$, and let
$i \in \{0, \dots, n-1\}$. Then the influence of coordinate $i$ on $f$ equals the probability,
for $x$ uniform on the cube, that $f(x^{\oplus i}) \ne f(x)$, where $x^{\oplus i}$ is $x$ with
its $i$-th coordinate flipped. -/
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

/-- **Fourier formula for influence.** For every real-valued function $f$ on the Boolean cube
$\{-1, 1\}^n$ and every coordinate $i \in \{0, \dots, n-1\}$, the influence of coordinate $i$ on
$f$ is $\mathrm{Inf}_i[f] = \sum_{S \ni i} \hat f(S)^2$, where $\hat f(S)$ is the Fourier
coefficient of $f$ at $S$ and the sum runs over the sets $S \subseteq \{0, \dots, n-1\}$ that
contain $i$. -/
theorem boolInfluence_eq_sum_sq (f : BoolCube n → ℝ) (i : Fin n) :
    boolInfluence f i = ∑ S with i ∈ S, boolFourierCoeff n f S ^ 2 := by
  rw [boolInfluence, expect_sq_eq_sum_boolFourierCoeff_sq (fun x => (f x - f (flipCoord x i)) / 2),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [boolFourierCoeff_derivative]
  split_ifs <;> simp

/-- **Variance in terms of Fourier coefficients.** For every function
$f : \{-1, 1\}^n \to \mathbb{R}$ on the Boolean cube, the variance of $f$ under the uniform
distribution equals $\sum_{S \neq \emptyset} \hat f(S)^2$, where the sum runs over the nonempty
sets $S \subseteq \{0, \dots, n-1\}$ and $\hat f(S)$ is the Fourier coefficient of $f$ at $S$. -/
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

/-- **Variance as mean square minus squared mean.** For every function
$f : \{-1, 1\}^n \to \mathbb{R}$ on the Boolean cube, the variance of $f$ under the uniform
distribution equals $\mathbb{E}_x[f(x)^2] - (\mathbb{E}_x[f(x)])^2$, where $\mathbb{E}_x$
denotes the uniform average over the $2^n$ points $x$ of the cube. -/
theorem boolVariance_eq_expect_sq_sub_sq (f : BoolCube n → ℝ) :
    boolVariance f = 𝔼 x, f x ^ 2 - (𝔼 x, f x) ^ 2 := by
  have h (x : BoolCube n) : (f x - 𝔼 y, f y) ^ 2 =
      f x ^ 2 - 2 * (𝔼 y, f y) * f x + (𝔼 y, f y) ^ 2 := by
    ring
  rw [boolVariance]
  simp_rw [h, Finset.expect_add_distrib, Finset.expect_sub_distrib, ← Finset.mul_expect,
    Fintype.expect_const]
  ring

/-- **Total influence in Fourier form.** For every function $f$ from the Boolean cube
$\{-1, 1\}^n$ to $\mathbb{R}$, the total influence of $f$ is
$$\mathrm{I}[f] = \sum_{S \subseteq \{0, \dots, n-1\}} |S| \, \hat f(S)^2,$$
where $\hat f(S)$ is the Fourier coefficient of $f$ at $S$. -/
theorem boolTotalInfluence_eq_sum_card_mul_sq (f : BoolCube n → ℝ) :
    boolTotalInfluence f = ∑ S, (S.card : ℝ) * boolFourierCoeff n f S ^ 2 := by
  simp_rw [boolTotalInfluence, boolInfluence_eq_sum_sq, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

/-- **Poincaré inequality on the Boolean cube.** For every function
$f : \{-1, 1\}^n \to \mathbb{R}$ on the Boolean cube, the variance of $f$ under the uniform
distribution is at most the total influence of $f$: $\mathrm{Var}[f] \le I[f]$. -/
theorem boolVariance_le_boolTotalInfluence (f : BoolCube n → ℝ) :
    boolVariance f ≤ boolTotalInfluence f := by
  rw [boolVariance_eq_sum_sq, boolTotalInfluence_eq_sum_card_mul_sq, Finset.sum_filter]
  refine Finset.sum_le_sum fun S _ => ?_
  split_ifs with hS
  · have h1 : (1 : ℝ) ≤ S.card := by exact_mod_cast hS.card_pos
    nlinarith [sq_nonneg (boolFourierCoeff n f S)]
  · positivity

/-! ### The noise operator -/

/-- **Noise operator on the Boolean cube.** For a real number $\rho$ and a function $f$ from the
Boolean cube $\{-1, 1\}^n$ to $\mathbb{R}$, the noise operator $T_\rho$ sends $f$ to the function
$$T_\rho f(x) = \sum_y \Bigl(\prod_{i < n} \frac{1 + \rho \sigma(x_i) \sigma(y_i)}{2}\Bigr) f(y),$$
where $y$ runs over all points of the cube and $\sigma$ is the sign of a coordinate:
$\sigma(\mathrm{true}) = 1$ and $\sigma(\mathrm{false}) = -1$.

For $-1 \le \rho \le 1$, $T_\rho f(x)$ is the expectation of $f(y)$ when each coordinate of $y$
independently equals the corresponding coordinate of $x$ with probability $(1 + \rho) / 2$; the
formula is used for every real $\rho$. -/
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

/-- **Fourier expansion of the noise operator.** For every real number $\rho$, every function $f$
from the Boolean cube $\{-1, 1\}^n$ to $\mathbb{R}$ and every point $x$ of the cube,
$$T_\rho f(x) = \sum_{S \subseteq \{0, \dots, n-1\}} \rho^{|S|} \, \hat f(S) \, \chi_S(x),$$
where $T_\rho$ is the noise operator, $\hat f(S)$ is the Fourier coefficient of $f$ at $S$,
$\chi_S$ is the Fourier character of $S$, and $\rho^0 = 1$ also when $\rho = 0$. -/
theorem boolNoiseOp_eq_sum (ρ : ℝ) (f : BoolCube n → ℝ) (x : BoolCube n) :
    boolNoiseOp ρ f x = ∑ S, ρ ^ S.card * boolFourierCoeff n f S * cubeChi n S x := by
  simp only [boolNoiseOp, prod_noiseKernel, boolFourierCoeff_eq_sum_div_two_pow,
    Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun y _ => ?_
  ring

/-- **Fourier coefficients of the noise operator.** For every real $\rho$, every real-valued
function $f$ on the Boolean cube in $n$ coordinates and every set $S$ of the $n$ coordinates, the
Fourier coefficient at $S$ of $T_\rho f$, the noise operator with parameter $\rho$ applied to $f$,
is $\widehat{T_\rho f}(S) = \rho^{|S|} \hat f(S)$. -/
theorem boolFourierCoeff_boolNoiseOp (ρ : ℝ) (f : BoolCube n → ℝ) (S : Finset (Fin n)) :
    boolFourierCoeff n (boolNoiseOp ρ f) S = ρ ^ S.card * boolFourierCoeff n f S := by
  have h : boolNoiseOp ρ f =
      fun x => ∑ T, (ρ ^ T.card * boolFourierCoeff n f T) * cubeChi n T x :=
    funext (boolNoiseOp_eq_sum ρ f)
  rw [h, boolFourierCoeff_sum_mul_cubeChi]

/-- **The noise operator $T_1$ is the identity.** For every function $f$ from the Boolean cube
$\{-1, 1\}^n$ to $\mathbb{R}$, the noise operator with $\rho = 1$ fixes $f$: $T_1 f = f$. -/
@[simp] theorem boolNoiseOp_one (f : BoolCube n → ℝ) : boolNoiseOp 1 f = f := by
  funext x
  simp [boolNoiseOp_eq_sum, sum_boolFourierCoeff_mul_cubeChi]

/-- **The noise operator $T_0$ takes the mean.** For every function $f$ from the Boolean cube
$\{-1, 1\}^n$ to $\mathbb{R}$, the noise operator with $\rho = 0$ sends $f$ to the constant
function whose value is the mean $\mathbb{E}_x f(x) = 2^{-n} \sum_x f(x)$ of $f$ under the
uniform distribution. -/
@[simp] theorem boolNoiseOp_zero (f : BoolCube n → ℝ) : boolNoiseOp 0 f = fun _ => 𝔼 x, f x := by
  funext x
  rw [boolNoiseOp_eq_sum, Finset.sum_eq_single ∅, expect_eq_boolFourierCoeff_empty]
  · simp
  · intro S _ hS
    simp [Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS)]
  · simp

/-- **Semigroup property of the noise operator.** For all real numbers $\rho$ and $\sigma$ and every
real-valued function $f$ on the Boolean cube $\{-1, 1\}^n$, applying the noise operator $T_\sigma$
and then $T_\rho$ to $f$ gives $T_{\rho\sigma} f$: $T_\rho(T_\sigma f) = T_{\rho\sigma} f$. -/
theorem boolNoiseOp_boolNoiseOp (ρ σ : ℝ) (f : BoolCube n → ℝ) :
    boolNoiseOp ρ (boolNoiseOp σ f) = boolNoiseOp (ρ * σ) f :=
  boolFourierCoeff_injective <| funext fun S => by
    simp only [boolFourierCoeff_boolNoiseOp, mul_pow]
    ring

/-- **The noise operator preserves the mean.** For every real $\rho$ and every function
$f : \{-1, 1\}^n \to \mathbb{R}$ on the Boolean cube, the uniform average over the cube of
$T_\rho f$, the image of $f$ under the noise operator with parameter $\rho$, equals the uniform
average of $f$. -/
theorem expect_boolNoiseOp (ρ : ℝ) (f : BoolCube n → ℝ) :
    𝔼 x, boolNoiseOp ρ f x = 𝔼 x, f x := by
  rw [expect_eq_boolFourierCoeff_empty, expect_eq_boolFourierCoeff_empty,
    boolFourierCoeff_boolNoiseOp]
  simp

/-- **Characters are eigenfunctions of the noise operator.** For every real number $\rho$ and every
set $S \subseteq \{0, \dots, n-1\}$, the noise operator $T_\rho$ maps the Fourier character $\chi_S$
on the Boolean cube $\{-1, 1\}^n$ to the function $x \mapsto \rho^{|S|} \chi_S(x)$, so $\chi_S$ is
an eigenfunction of $T_\rho$ with eigenvalue $\rho^{|S|}$. -/
theorem boolNoiseOp_cubeChi (ρ : ℝ) (S : Finset (Fin n)) :
    boolNoiseOp ρ (cubeChi n S) = fun x => ρ ^ S.card * cubeChi n S x := by
  funext x
  simp [boolNoiseOp_eq_sum, boolFourierCoeff_cubeChi]

/-- **The noise operator fixes constants.** For every real number $\rho$ and every real number $c$,
the noise operator $T_\rho$ maps the constant function with value $c$ on the Boolean cube
$\{-1, 1\}^n$ to itself. -/
@[simp] theorem boolNoiseOp_const (ρ c : ℝ) :
    boolNoiseOp ρ (fun _ : BoolCube n => c) = fun _ => c := by
  funext x
  simp [boolNoiseOp_eq_sum, boolFourierCoeff_const]

/-- **Positivity of the noise operator.** For every real number $\rho$ with $|\rho| \le 1$, the
noise operator $T_\rho$ on the Boolean cube maps nonnegative functions to nonnegative functions:
if $f$ is a real function on the cube with $f(y) \ge 0$ for every point $y$, then
$T_\rho f(x) \ge 0$ for every point $x$ of the cube. -/
theorem boolNoiseOp_nonneg {ρ : ℝ} (hρ : |ρ| ≤ 1) {f : BoolCube n → ℝ} (hf : ∀ x, 0 ≤ f x)
    (x : BoolCube n) : 0 ≤ boolNoiseOp ρ f x := by
  refine Finset.sum_nonneg fun y _ => mul_nonneg (Finset.prod_nonneg fun i _ => ?_) (hf y)
  have h : |ρ * cubeVal (x i) * cubeVal (y i)| ≤ 1 := by
    simpa [abs_mul] using hρ
  have := neg_abs_le (ρ * cubeVal (x i) * cubeVal (y i))
  linarith

end BooleanCube
