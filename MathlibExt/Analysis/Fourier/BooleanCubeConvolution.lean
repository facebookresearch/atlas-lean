/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.BooleanCubeInfluence
import Mathlib.Tactic.Ring

/-!
# Convolution on the Boolean cube

The cube `{-1, 1}ⁿ` is a group under coordinatewise multiplication; it is the group `𝔽₂ⁿ`
written multiplicatively. With `true` read as `+1` and `false` as `-1` (`cubeVal`), the product
of two coordinates is `a == b` (`cubeMul`). The characters `χ_S` are the group homomorphisms to
`{-1, 1}`, and convolution `(f ∗ g)(x) = 𝔼_y[f(y) g(x y)]` turns into multiplication of Fourier
coefficients (O'Donnell's Theorem 1.27).

## Main definitions

* `BooleanCube.cubeMul x y`: the coordinatewise product of `x, y ∈ {-1, 1}ⁿ`.
* `BooleanCube.boolConv f g`: the convolution `(f ∗ g)(x) = 𝔼_y[f(y) g(x y)]`.

## Main statements

* `BooleanCube.cubeChi_cubeMul`: `χ_S(x y) = χ_S(x) χ_S(y)`.
* `BooleanCube.boolFourierCoeff_boolConv`: the convolution theorem,
  `(f ∗ g)^(S) = f̂(S) ĝ(S)`.

## References

* R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014
  (arXiv:2105.10386), Section 1.5 (Definition 1.24, Theorem 1.27).
-/

@[expose] public section

namespace BooleanCube

open scoped BigOperators

variable {n : ℕ}

/-- **Product on the Boolean cube.** The coordinatewise product of `x, y ∈ {-1, 1}ⁿ`: with
`true` as `+1` and `false` as `-1`, the product of two coordinates is `x i == y i`. This is
addition in `𝔽₂ⁿ` written multiplicatively (R. O'Donnell, *Analysis of Boolean Functions*, 2014,
Section 1.2 and Section 1.5). -/
def cubeMul (x y : BoolCube n) : BoolCube n :=
  fun i => x i == y i

/-- **Signs multiply under the cube product.** `σ(a == b) = σ(a) σ(b)` for the sign
`σ = cubeVal` of a Boolean coordinate. -/
@[simp] theorem cubeVal_beq (a b : Bool) : cubeVal (a == b) = cubeVal a * cubeVal b := by
  cases a <;> cases b <;> simp [cubeVal]

/-- **Characters are multiplicative.** For every `S` and `x, y ∈ {-1, 1}ⁿ`,
`χ_S(x y) = χ_S(x) χ_S(y)` (R. O'Donnell, *Analysis of Boolean Functions*, 2014, equation (1.5),
written there additively as `χ_S(x + y) = χ_S(x) χ_S(y)` on `𝔽₂ⁿ`). -/
theorem cubeChi_cubeMul (S : Finset (Fin n)) (x y : BoolCube n) :
    cubeChi n S (cubeMul x y) = cubeChi n S x * cubeChi n S y := by
  simp [cubeChi, cubeMul, Finset.prod_mul_distrib]

/-- **Every point is its own inverse.** `(x y) y = x` on the Boolean cube. -/
@[simp] theorem cubeMul_cubeMul_self (x y : BoolCube n) : cubeMul (cubeMul x y) y = x := by
  funext i
  simp only [cubeMul]
  cases x i <;> cases y i <;> rfl

/-- **The cube product is commutative.** `x y = y x`. -/
theorem cubeMul_comm (x y : BoolCube n) : cubeMul x y = cubeMul y x := by
  funext i
  simp only [cubeMul]
  cases x i <;> cases y i <;> rfl

/-- **Translation-invariance of averages.** For every `y` and `F : BoolCube n → ℝ`,
`𝔼_x F(x y) = 𝔼_x F(x)`: multiplication by `y` is a bijection of the cube. -/
theorem expect_comp_cubeMul (F : BoolCube n → ℝ) (y : BoolCube n) :
    𝔼 x, F (cubeMul x y) = 𝔼 x, F x := by
  let e : BoolCube n ≃ BoolCube n :=
    ⟨fun x => cubeMul x y, fun x => cubeMul x y, fun x => by simp, fun x => by simp⟩
  exact Fintype.expect_equiv e _ _ fun _ => rfl

/-- **Convolution on the Boolean cube.** For `f, g : BoolCube n → ℝ`,
`(f ∗ g)(x) = 𝔼_y[f(y) g(x y)]`, the cube form of `𝔼_y[f(y) g(x - y)]` on `𝔽₂ⁿ`
(R. O'Donnell, *Analysis of Boolean Functions*, 2014, Definition 1.24). -/
noncomputable def boolConv (f g : BoolCube n → ℝ) (x : BoolCube n) : ℝ :=
  𝔼 y, f y * g (cubeMul x y)

/-- **Convolution theorem on the Boolean cube.** For all `f, g : BoolCube n → ℝ` and every
`S`, `(f ∗ g)^(S) = f̂(S) ĝ(S)` (R. O'Donnell, *Analysis of Boolean Functions*, 2014,
Theorem 1.27). -/
theorem boolFourierCoeff_boolConv (f g : BoolCube n → ℝ) (S : Finset (Fin n)) :
    boolFourierCoeff n (boolConv f g) S = boolFourierCoeff n f S * boolFourierCoeff n g S := by
  simp_rw [boolFourierCoeff_eq_expect, boolConv, Finset.expect_mul, Finset.mul_expect]
  rw [Finset.expect_comm]
  refine Finset.expect_congr rfl fun y _ => ?_
  have h := expect_comp_cubeMul
    (fun z => f y * g z * cubeChi n S (cubeMul z y)) y
  simp only [cubeMul_cubeMul_self] at h
  rw [h]
  refine Finset.expect_congr rfl fun x _ => ?_
  rw [cubeChi_cubeMul]
  ring

/-- **Convolution is commutative.** `f ∗ g = g ∗ f` on the Boolean cube. -/
theorem boolConv_comm (f g : BoolCube n → ℝ) : boolConv f g = boolConv g f :=
  boolFourierCoeff_injective <| funext fun S => by
    rw [boolFourierCoeff_boolConv, boolFourierCoeff_boolConv, mul_comm]

end BooleanCube
