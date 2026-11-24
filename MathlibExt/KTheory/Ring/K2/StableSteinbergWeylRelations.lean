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

/-! # Weyl relations

Basic inversion and root-conjugation identities for stable Steinberg Weyl words,
including torus transport.
-/

@[expose] public section

namespace AlgebraicKTheory

namespace StableSteinberg

universe u

variable {R : Type u} [Ring R]

open scoped commutatorElement

private theorem coe_neg_units (u : Rˣ) : (↑(-u) : R) = -(↑u : R) :=
  rfl

private theorem coe_inv_neg_units (u : Rˣ) : (↑((-u)⁻¹) : R) = -(↑u⁻¹ : R) :=
  rfl

private theorem neg_coe_inv_neg_units (u : Rˣ) :
    (-(↑((-u)⁻¹) : R)) = (↑u⁻¹ : R) := by
  rw [coe_inv_neg_units, neg_neg]

private theorem conj_eq_commutator_mul {G : Type*} [Group G] (a b : G) :
    a * b * a⁻¹ = ⁅a, b⁆ * b := by
  simpa only [MulAut.conj_apply, mul_assoc] using
    (conj_eq_commutatorElement_mul (g₁ := a) (g₂ := b))

public theorem weyl_neg_eq_inv (i j : ℕ) (hij : i ≠ j) (u : Rˣ) :
    weyl (R := R) i j hij (-u) = (weyl i j hij u)⁻¹ := by
  unfold weyl
  rw [coe_neg_units (R := R) (u := u), neg_coe_inv_neg_units (R := R) (u := u)]
  have hx1 : x (R := R) i j hij (-(↑u : R)) = (x i j hij (↑u : R))⁻¹ := by
    rw [← x_neg]
  have hx2 :
      x (R := R) j i hij.symm (↑u⁻¹ : R) =
        (x (R := R) j i hij.symm (-(↑u⁻¹ : R)))⁻¹ := by
    rw [← x_neg]
    simp [neg_neg]
  rw [hx1, hx2]
  simp [mul_inv_rev, mul_assoc]

/-- Weyl conjugation of `x j k` by `weyl i j`. -/
public theorem weyl_conj_x_jk (i j k : ℕ) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (u : Rˣ) (a : R) :
    weyl (R := R) i j hij u * x j k hjk a * (weyl i j hij u)⁻¹ =
      x i k hik ((↑u : R) * a) := by
  let A := x i j hij (u : R)
  let B := x j i hij.symm (-(↑u⁻¹ : R))
  let X := x j k hjk a
  let Y := x i k hik ((↑u : R) * a)
  have hWeyl : weyl (R := R) i j hij u = A * B * A := rfl
  rw [hWeyl]
  change (A * B * A) * X * (A * B * A)⁻¹ = Y
  have hAX : A * X * A⁻¹ = Y * X := by
    have hChev : ⁅A, X⁆ = Y := by
      simp only [A, X, Y]
      exact x_chev (R := R) i j k hij hjk hik (↑u : R) a
    have hConj : A * X * A⁻¹ = ⁅A, X⁆ * X :=
      conj_eq_commutator_mul A X
    rw [hConj, hChev]
  have hCoeff : (-(↑u⁻¹ : R)) * ((↑u : R) * a) = -a := by
    calc (-(↑u⁻¹ : R)) * ((↑u : R) * a)
        = -((↑u⁻¹ : R) * ((↑u : R) * a)) := by rw [neg_mul]
      _ = -(((↑u⁻¹ : R) * (↑u : R)) * a) := by rw [← mul_assoc]
      _ = -((1 : R) * a) := by rw [Units.inv_mul]
      _ = -a := by rw [one_mul]
  have hBY : B * Y * B⁻¹ = X⁻¹ * Y := by
    have hChevBY : ⁅B, Y⁆ = x j k hjk ((-(↑u⁻¹ : R)) * ((↑u : R) * a)) := by
      simp only [B, Y]
      exact x_chev (R := R) j i k hij.symm hik hjk (-(↑u⁻¹ : R))
        ((↑u : R) * a)
    have hChevBY2 : ⁅B, Y⁆ = x j k hjk (-a) := by
      rw [hChevBY, hCoeff]
    have hChevBY3 : ⁅B, Y⁆ = X⁻¹ := by
      rw [hChevBY2]
      have hXneg : x j k hjk (-a) = X⁻¹ := by
        simp only [X]
        exact x_neg (R := R) j k hjk a
      rw [hXneg]
    have hConjBY : B * Y * B⁻¹ = ⁅B, Y⁆ * Y :=
      conj_eq_commutator_mul B Y
    rw [hConjBY, hChevBY3]
  have hBX : B * X * B⁻¹ = X := by
    have hCommBX : ⁅B, X⁆ = (1 : StableSteinberg R) := by
      simp only [B, X]
      exact x_comm (R := R) j i j k hij.symm hjk hjk hij
        (-(↑u⁻¹ : R)) a
    have hConjBX : B * X * B⁻¹ = ⁅B, X⁆ * X :=
      conj_eq_commutator_mul B X
    rw [hConjBX, hCommBX, one_mul]
  have hYX : Y * X = X * Y := by
    have hCommYX : ⁅Y, X⁆ = (1 : StableSteinberg R) := by
      simp only [Y, X]
      exact x_comm (R := R) i k j k hik hjk hik hjk.symm
        ((↑u : R) * a) a
    exact (commutatorElement_eq_one_iff_mul_comm.mp hCommYX)
  have hcancel : (X⁻¹ * Y) * X = Y := by
    calc (X⁻¹ * Y) * X = X⁻¹ * (Y * X) := by rw [mul_assoc]
      _ = X⁻¹ * (X * Y) := by rw [hYX]
      _ = X⁻¹ * X * Y := by rw [← mul_assoc]
      _ = Y := by rw [inv_mul_cancel, one_mul]
  have hAY : A * Y * A⁻¹ = Y := by
    have hCommAY : ⁅A, Y⁆ = (1 : StableSteinberg R) := by
      simp only [A, Y]
      exact x_comm (R := R) i j i k hij hik hik hij.symm
        (↑u : R) ((↑u : R) * a)
    have hConjAY : A * Y * A⁻¹ = ⁅A, Y⁆ * Y :=
      conj_eq_commutator_mul A Y
    rw [hConjAY, hCommAY, one_mul]
  calc
    (A * B * A) * X * (A * B * A)⁻¹ =
        A * (B * (A * X * A⁻¹) * B⁻¹) * A⁻¹ := by
          simp only [mul_inv_rev, mul_assoc]
    _ = A * (B * (Y * X) * B⁻¹) * A⁻¹ := by rw [hAX]
    _ = A * ((B * Y * B⁻¹) * (B * X * B⁻¹)) * A⁻¹ := by
        rw [← conj_mul (b := B) (a := Y) (c := X)]
    _ = A * ((X⁻¹ * Y) * X) * A⁻¹ := by rw [hBY, hBX]
    _ = A * Y * A⁻¹ := by rw [hcancel]
    _ = Y := hAY

/-- Conjugation by `weyl i j` sends `x i k` to the corresponding negative root coefficient. -/
public theorem weyl_conj_x_ik (i j k : ℕ) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (u : Rˣ) (a : R) :
    weyl (R := R) i j hij u * x i k hik a * (weyl i j hij u)⁻¹ =
      x j k hjk (-((↑u⁻¹ : R) * a)) := by
  have hCoeff :
      (↑(-u) : R) * (-((↑u⁻¹ : R) * a)) = a := by
    rw [coe_neg_units, neg_mul_neg, ← mul_assoc, Units.mul_inv, one_mul]
  have hConj :=
    weyl_conj_x_jk (R := R) i j k hij hjk hik (-u)
      (-((↑u⁻¹ : R) * a))
  rw [hCoeff, weyl_neg_eq_inv] at hConj
  rw [← hConj]
  simp [mul_assoc]

/-- Weyl conjugation of `x k j` by `weyl i j`. -/
public theorem weyl_conj_x_kj (i j k : ℕ) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (u : Rˣ) (a : R) :
    weyl (R := R) i j hij u * x k j hjk.symm a * (weyl i j hij u)⁻¹ =
      x k i hik.symm (a * (↑u⁻¹ : R)) := by
  let A := x i j hij (u : R)
  let B := x j i hij.symm (-(↑u⁻¹ : R))
  let X := x k j hjk.symm a
  let Y := x k i hik.symm (a * (↑u⁻¹ : R))
  have hWeyl : weyl (R := R) i j hij u = A * B * A := rfl
  rw [hWeyl]
  change (A * B * A) * X * (A * B * A)⁻¹ = Y
  have hAX : A * X * A⁻¹ = X := by
    have hComm : ⁅A, X⁆ = (1 : StableSteinberg R) := by
      simp only [A, X]
      exact x_comm i j k j hij hjk.symm hij hjk (↑u : R) a
    have hConj : A * X * A⁻¹ = ⁅A, X⁆ * X :=
      conj_eq_commutator_mul A X
    rw [hConj, hComm, one_mul]
  have hCoeff : (a * (↑u⁻¹ : R)) * (↑u : R) = a := by
    calc (a * (↑u⁻¹ : R)) * (↑u : R)
        = a * ((↑u⁻¹ : R) * (↑u : R)) := by rw [mul_assoc]
      _ = a * 1 := by rw [Units.inv_mul]
      _ = a := by rw [mul_one]
  have hBX : B * X * B⁻¹ = Y * X := by
    have hChevXB : ⁅X, B⁆ = x k i hik.symm (a * (-(↑u⁻¹ : R))) := by
      simp only [X, B]
      exact x_chev k j i hjk.symm hij.symm hik.symm a (-(↑u⁻¹ : R))
    have hChevNeg : ⁅X, B⁆ = x k i hik.symm (-(a * (↑u⁻¹ : R))) := by
      rw [hChevXB, mul_neg]
    have hXB_eq_Yinv : ⁅X, B⁆ = Y⁻¹ := by
      calc ⁅X, B⁆ = x k i hik.symm (-(a * (↑u⁻¹ : R))) := hChevNeg
        _ = Y⁻¹ := by
          simp only [Y]
          rw [x_neg]
    have hCommBX : ⁅B, X⁆ = Y := by
      have hInv : ⁅B, X⁆ = ⁅X, B⁆⁻¹ := (commutatorElement_inv X B).symm
      rw [hInv, hXB_eq_Yinv, inv_inv]
    have hConjBX : B * X * B⁻¹ = ⁅B, X⁆ * X :=
      conj_eq_commutator_mul B X
    rw [hConjBX, hCommBX]
  have hAY : A * Y * A⁻¹ = X⁻¹ * Y := by
    have hChevYA : ⁅Y, A⁆ =
        x k j hjk.symm ((a * (↑u⁻¹ : R)) * (↑u : R)) := by
      simp only [Y, A]
      exact x_chev k i j hik.symm hij hjk.symm (a * (↑u⁻¹ : R)) (↑u : R)
    have hChevYA2 : ⁅Y, A⁆ = X := by
      calc ⁅Y, A⁆ = x k j hjk.symm ((a * (↑u⁻¹ : R)) * (↑u : R)) := hChevYA
        _ = x k j hjk.symm a := by rw [hCoeff]
        _ = X := rfl
    have hInvYA : ⁅A, Y⁆ = X⁻¹ := by
      have hInv : ⁅A, Y⁆ = ⁅Y, A⁆⁻¹ := (commutatorElement_inv Y A).symm
      rw [hInv, hChevYA2]
    have hConjAY : A * Y * A⁻¹ = ⁅A, Y⁆ * Y :=
      conj_eq_commutator_mul A Y
    rw [hConjAY, hInvYA]
  have hYX : Y * X = X * Y := by
    have hComm : ⁅Y, X⁆ = (1 : StableSteinberg R) := by
      simp only [Y, X]
      exact x_comm k i k j hik.symm hjk.symm hjk.symm hik
        (a * (↑u⁻¹ : R)) a
    exact (commutatorElement_eq_one_iff_mul_comm.mp hComm)
  have hCancel : (X⁻¹ * Y) * X = Y := by
    calc (X⁻¹ * Y) * X = X⁻¹ * (Y * X) := by rw [mul_assoc]
      _ = X⁻¹ * (X * Y) := by rw [hYX]
      _ = X⁻¹ * X * Y := by rw [← mul_assoc]
      _ = Y := by rw [inv_mul_cancel, one_mul]
  calc
    (A * B * A) * X * (A * B * A)⁻¹ =
        A * (B * (A * X * A⁻¹) * B⁻¹) * A⁻¹ := by
          simp only [mul_inv_rev, mul_assoc]
    _ = A * (B * X * B⁻¹) * A⁻¹ := by rw [hAX]
    _ = A * (Y * X) * A⁻¹ := by rw [hBX]
    _ = (A * Y * A⁻¹) * (A * X * A⁻¹) :=
      (conj_mul (b := A) (a := Y) (c := X)).symm
    _ = (X⁻¹ * Y) * X := by rw [hAY, hAX]
    _ = Y := hCancel

/-- Conjugation by `weyl i j` sends `x k i` to the corresponding negative root coefficient. -/
public theorem weyl_conj_x_ki (i j k : ℕ) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (u : Rˣ) (a : R) :
    weyl (R := R) i j hij u * x k i hik.symm a * (weyl i j hij u)⁻¹ =
      x k j hjk.symm (-(a * (↑u : R))) := by
  have hCoeff :
      (-(a * (↑u : R))) * (↑(-u)⁻¹ : R) = a := by
    rw [coe_inv_neg_units, neg_mul_neg, mul_assoc, Units.mul_inv, mul_one]
  have hConj :=
    weyl_conj_x_kj (R := R) i j k hij hjk hik (-u)
      (-(a * (↑u : R)))
  rw [hCoeff, weyl_neg_eq_inv] at hConj
  rw [← hConj]
  simp [mul_assoc]

/-- Weyl conjugation of the opposite root subgroup. -/
public theorem weyl_conj_x_ji (i j : ℕ) (hij : i ≠ j)
    (u : Rˣ) (a : R) :
    weyl (R := R) i j hij u * x j i hij.symm a *
        (weyl i j hij u)⁻¹ =
      x i j hij (-((u : R) * a * (u : R))) := by
  let k := max i j + 1
  have hk_gt_i : i < k := by
    have : i ≤ max i j := Nat.le_max_left i j
    omega
  have hk_gt_j : j < k := by
    have : j ≤ max i j := Nat.le_max_right i j
    omega
  have hjk : j ≠ k := Nat.ne_of_lt hk_gt_j
  have hik : i ≠ k := Nat.ne_of_lt hk_gt_i
  have hkj : k ≠ j := Ne.symm hjk
  have hki : k ≠ i := Ne.symm hik
  have hx_eq : x (R := R) j i hij.symm a = ⁅x j k hjk a, x k i hki (1 : R)⁆ := by
    have hchev : ⁅x (R := R) j k hjk a, x k i hki (1 : R)⁆ = x j i hij.symm (a * 1) :=
      x_chev (R := R) j k i hjk hki hij.symm a (1 : R)
    simp only [mul_one] at hchev
    exact hchev.symm
  let w := weyl (R := R) i j hij u
  have h_conj_jk : w * x j k hjk a * w⁻¹ = x i k hik ((↑u : R) * a) :=
    weyl_conj_x_jk (R := R) i j k hij hjk hik u a
  have h_conj_ki : w * x k i hki (1 : R) * w⁻¹ = x k j hkj (-((1 : R) * (↑u : R))) :=
    weyl_conj_x_ki (R := R) i j k hij hjk hik u (1 : R)
  have h_coeff : ((↑u : R) * a) * (-((1 : R) * (↑u : R))) = -((↑u : R) * a * (↑u : R)) := by
    calc ((↑u : R) * a) * (-((1 : R) * (↑u : R)))
        = -(((↑u : R) * a) * ((1 : R) * (↑u : R))) := by rw [mul_neg]
      _ = -(((↑u : R) * a) * (↑u : R)) := by rw [one_mul]
  calc w * x (R := R) j i hij.symm a * w⁻¹
      = w * ⁅x j k hjk a, x k i hki (1 : R)⁆ * w⁻¹ := by rw [hx_eq]
    _ = ⁅w * x j k hjk a * w⁻¹, w * x k i hki (1 : R) * w⁻¹⁆ := by
        rw [conjugate_commutatorElement]
    _ = ⁅x i k hik ((↑u : R) * a), x k j hkj (-((1 : R) * (↑u : R)))⁆ := by
        rw [h_conj_jk, h_conj_ki]
    _ = x i j hij (((↑u : R) * a) * (-((1 : R) * (↑u : R)))) := by
        exact x_chev (R := R) i k j hik hkj hij ((↑u : R) * a) (-((1 : R) * (↑u : R)))
    _ = x i j hij (-((↑u : R) * a * (↑u : R))) := by rw [h_coeff]

/-- Weyl conjugation of the same ordered root `x i j` by `weyl i j` :
`w_{ij}(u) x_{ij}(a) w_{ij}(u)⁻¹ = x_{ji}(-u⁻¹ a u⁻¹)`.
Coefficient and sign are obtained from the checked-in
`weyl_conj_x_ji` and `weyl_neg_eq_inv`; no guess.
`w_{ij}(-u)=w_{ij}(u)⁻¹`, `w_{ij}(-u) x_{ji}(b) w_{ij}(-u)⁻¹ = x_{ij}(-(-u) b (-u))`,
and with `b = -u⁻¹ a u⁻¹` we have `-(-u) b (-u) = -u b u = a`,
so `x_{ij}(a)=w_{ij}(-u) x_{ji}(b) w_{ij}(-u)⁻¹` and conjugating by
`w_{ij}(u)` gives `x_{ji}(b)`. -/
public theorem weyl_conj_x_ij (i j : ℕ) (hij : i ≠ j) (u : Rˣ) (a : R) :
    weyl (R := R) i j hij u * x i j hij a * (weyl i j hij u)⁻¹ =
      x j i hij.symm (-((↑u⁻¹ : R) * a * (↑u⁻¹ : R))) := by
  let b : R := -((↑u⁻¹ : R) * a * (↑u⁻¹ : R))
  have hU : (↑u : R) * (↑u⁻¹ : R) = 1 := Units.mul_inv u
  have hUi : (↑u⁻¹ : R) * (↑u : R) = 1 := Units.inv_mul u
  have hCoeNeg : (↑(-u) : R) = -(↑u : R) := coe_neg_units (R := R) u
  have hMulNeg : ∀ (x y : R), (-x) * y = -(x * y) := fun x y => neg_mul x y
  have hNegMul : ∀ (x y : R), x * (-y) = -(x * y) := fun x y => mul_neg x y
  have hNegNegMul : ∀ (x y : R), (-x) * (-y) = x * y := fun x y => by
    calc (-x) * (-y) = - (x * (-y)) := by rw [neg_mul]
      _ = - (-(x * y)) := by rw [mul_neg]
      _ = x * y := by rw [neg_neg]
  have hCoeNegProd :
      (↑(-u) : R) * b * (↑(-u) : R) = (↑u : R) * b * (↑u : R) := by
    calc (↑(-u) : R) * b * (↑(-u) : R)
        = (-(↑u : R)) * b * (-(↑u : R)) := by rw [hCoeNeg]
      _ = (-((↑u : R) * b)) * (-(↑u : R)) := by rw [neg_mul]
      _ = ((↑u : R) * b) * (↑u : R) := by rw [hNegNegMul]
  have hU_b_U_eq_neg_a : (↑u : R) * b * (↑u : R) = -a := by
    calc (↑u : R) * b * (↑u : R)
        = (↑u : R) * (-((↑u⁻¹ : R) * a * (↑u⁻¹ : R))) * (↑u : R) := rfl
      _ = -((↑u : R) * ((↑u⁻¹ : R) * a * (↑u⁻¹ : R)) * (↑u : R)) := by
          calc (↑u : R) * (-((↑u⁻¹ : R) * a * (↑u⁻¹ : R))) * (↑u : R)
              = (-((↑u : R) * ((↑u⁻¹ : R) * a * (↑u⁻¹ : R)))) * (↑u : R) := by
                rw [mul_neg]
            _ = -((↑u : R) * ((↑u⁻¹ : R) * a * (↑u⁻¹ : R)) * (↑u : R)) := by
                rw [neg_mul]
      _ = -a := by
          have hInner : (↑u : R) * ((↑u⁻¹ : R) * a * (↑u⁻¹ : R)) * (↑u : R) = a := by
            calc (↑u : R) * ((↑u⁻¹ : R) * a * (↑u⁻¹ : R)) * (↑u : R)
                = (↑u : R) * ((↑u⁻¹ : R) * a) * (↑u⁻¹ : R) * (↑u : R) := by
                  rw [← mul_assoc (a := (↑u : R))]
                _ = (↑u : R) * (↑u⁻¹ : R) * a * (↑u⁻¹ : R) * (↑u : R) := by
                  rw [← mul_assoc (a := (↑u : R))]
                _ = (1 : R) * a * (↑u⁻¹ : R) * (↑u : R) := by rw [hU]
                _ = a * (↑u⁻¹ : R) * (↑u : R) := by rw [one_mul]
                _ = a * ((↑u⁻¹ : R) * (↑u : R)) := by rw [mul_assoc]
                _ = a * 1 := by rw [hUi]
                _ = a := by rw [mul_one]
          rw [hInner]
  have hNeg_UbU : -((↑u : R) * b * (↑u : R)) = a := by
    calc -((↑u : R) * b * (↑u : R)) = -(-a) := by rw [hU_b_U_eq_neg_a]
      _ = a := by rw [neg_neg]
  have hNegU_b_U : (↑(-u) : R) * b * (↑(-u) : R) = -a := by
    calc (↑(-u) : R) * b * (↑(-u) : R) = (↑u : R) * b * (↑u : R) := hCoeNegProd
      _ = -a := hU_b_U_eq_neg_a
  have hConjNeg :
      weyl (R := R) i j hij (-u) * x j i hij.symm b *
        (weyl (R := R) i j hij (-u))⁻¹ =
        x i j hij (-((↑(-u) : R) * b * (↑(-u) : R))) := by
    exact weyl_conj_x_ji (R := R) i j hij (-u) b
  have hConjNegEq :
      weyl (R := R) i j hij (-u) * x j i hij.symm b *
        (weyl (R := R) i j hij (-u))⁻¹ = x i j hij a := by
    calc weyl (R := R) i j hij (-u) * x j i hij.symm b *
        (weyl (R := R) i j hij (-u))⁻¹
        = x i j hij (-((↑(-u) : R) * b * (↑(-u) : R))) := hConjNeg
      _ = x i j hij (-((↑u : R) * b * (↑u : R))) := by rw [hCoeNegProd]
      _ = x i j hij a := by rw [hNeg_UbU]
  have hWneg : weyl (R := R) i j hij (-u) = (weyl i j hij u)⁻¹ :=
    weyl_neg_eq_inv (R := R) i j hij u
  have hWmul : weyl (R := R) i j hij u * weyl (R := R) i j hij (-u) = 1 := by
    rw [hWneg, mul_inv_cancel]
  have hWmulInv :
      (weyl (R := R) i j hij (-u))⁻¹ * (weyl (R := R) i j hij u)⁻¹ = 1 := by
    calc (weyl (R := R) i j hij (-u))⁻¹ * (weyl (R := R) i j hij u)⁻¹
        = (weyl (R := R) i j hij u * weyl (R := R) i j hij (-u))⁻¹ := by
          rw [mul_inv_rev]
      _ = (1 : StableSteinberg R)⁻¹ := by rw [hWmul]
      _ = 1 := by rw [inv_one]
  calc weyl (R := R) i j hij u * x i j hij a * (weyl (R := R) i j hij u)⁻¹
      = weyl (R := R) i j hij u *
          (weyl (R := R) i j hij (-u) * x j i hij.symm b *
            (weyl (R := R) i j hij (-u))⁻¹) *
          (weyl (R := R) i j hij u)⁻¹ := by rw [hConjNegEq]
    _ = weyl (R := R) i j hij u * weyl (R := R) i j hij (-u) * x j i hij.symm b *
          (weyl (R := R) i j hij (-u))⁻¹ * (weyl (R := R) i j hij u)⁻¹ := by
        rw [← mul_assoc, ← mul_assoc]
    _ = weyl (R := R) i j hij u * weyl (R := R) i j hij (-u) * x j i hij.symm b *
          ((weyl (R := R) i j hij (-u))⁻¹ * (weyl (R := R) i j hij u)⁻¹) := by
        rw [mul_assoc]
    _ = (1 : StableSteinberg R) * x j i hij.symm b * (1 : StableSteinberg R) := by
        rw [hWmul, hWmulInv]
    _ = x j i hij.symm b := by rw [one_mul, mul_one]

/-- Weyl index swap: `w_{ij}(u) = w_{ji}(-u⁻¹)`. Exact equality in `St(R)`,
preserving coefficient, sign, inverse, and multiplication orientation, including
characteristic two. The proof reuses the existing
`weyl_conj_x_ij` / `weyl_conj_x_ji` identities (which already use the private
auxiliary `k := max i j + 1` and Chevalley commutator expansions for opposite
roots) and finishes by the elementary swapping calculation
`w_{ij}(u) x_{ij}(u) w_{ij}(u)⁻¹ = x_{ji}(-u⁻¹)`,
`w_{ij}(u) x_{ji}(-u⁻¹) w_{ij}(u)⁻¹ = x_{ij}(u)`,
hence `w_{ij}(u)² = w_{ji}(-u⁻¹) w_{ij}(u)` and `w_{ij}(u)=w_{ji}(-u⁻¹)`.
No exact torus index-swap, `weyl(u)^2 = torus(-1)`, or cocycle-subgroup
claim is made here; those may carry a central defect and belong downstream. -/
public theorem weyl_swap (i j : ℕ) (hij : i ≠ j) (u : Rˣ) :
    weyl (R := R) i j hij u = weyl j i hij.symm (-u⁻¹) := by
  let A : StableSteinberg R := x i j hij (↑u : R)
  let B : StableSteinberg R := x j i hij.symm (-(↑u⁻¹ : R))
  have hWdef : weyl (R := R) i j hij u = A * B * A := rfl
  set w := weyl (R := R) i j hij u with hw_def
  have hw_eq : w = A * B * A := hWdef
  have h_inner1 : (↑u⁻¹ : R) * (↑u : R) * (↑u⁻¹ : R) = (↑u⁻¹ : R) := by
    calc (↑u⁻¹ : R) * (↑u : R) * (↑u⁻¹ : R)
        = ((↑u⁻¹ : R) * (↑u : R)) * (↑u⁻¹ : R) := by rw [mul_assoc]
      _ = (1 : R) * (↑u⁻¹ : R) := by rw [Units.inv_mul]
      _ = (↑u⁻¹ : R) := by rw [one_mul]
  have hcoeff1 : -((↑u⁻¹ : R) * (↑u : R) * (↑u⁻¹ : R)) = -(↑u⁻¹ : R) := by
    rw [h_inner1]
  have h_inner2 : (↑u : R) * (-(↑u⁻¹ : R)) * (↑u : R) = -(↑u : R) := by
    calc (↑u : R) * (-(↑u⁻¹ : R)) * (↑u : R)
        = (-((↑u : R) * (↑u⁻¹ : R))) * (↑u : R) := by rw [mul_neg]
      _ = (-(1 : R)) * (↑u : R) := by rw [Units.mul_inv]
      _ = -(1 * (↑u : R)) := by rw [neg_mul]
      _ = -(↑u : R) := by rw [one_mul]
  have hcoeff2 : -((↑u : R) * (-(↑u⁻¹ : R)) * (↑u : R)) = (↑u : R) := by
    calc -((↑u : R) * (-(↑u⁻¹ : R)) * (↑u : R))
        = -(-(↑u : R)) := by rw [h_inner2]
      _ = (↑u : R) := by rw [neg_neg]
  have h_conj_A : w * A * w⁻¹ = B := by
    calc w * A * w⁻¹
        = w * x i j hij (↑u : R) * w⁻¹ := rfl
      _ = x j i hij.symm (-((↑u⁻¹ : R) * (↑u : R) * (↑u⁻¹ : R))) :=
          weyl_conj_x_ij (R := R) i j hij u (↑u : R)
      _ = x j i hij.symm (-(↑u⁻¹ : R)) := by rw [hcoeff1]
      _ = B := rfl
  have h_conj_B : w * B * w⁻¹ = A := by
    calc w * B * w⁻¹
        = w * x j i hij.symm (-(↑u⁻¹ : R)) * w⁻¹ := rfl
      _ = x i j hij (-((↑u : R) * (-(↑u⁻¹ : R)) * (↑u : R))) :=
          weyl_conj_x_ji (R := R) i j hij u (-(↑u⁻¹ : R))
      _ = x i j hij (↑u : R) := by rw [hcoeff2]
      _ = A := rfl
  have h_wA : w * A = B * w := by
    calc w * A
        = (w * A * w⁻¹) * w := by rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = B * w := by rw [h_conj_A]
  have h_wB : w * B = A * w := by
    calc w * B
        = (w * B * w⁻¹) * w := by rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = A * w := by rw [h_conj_B]
  have h_sq : w * w = B * A * B * w := by
    calc w * w
        = w * (A * B * A) := by rw [hw_eq]
      _ = w * A * B * A := by simp only [mul_assoc]
      _ = B * w * B * A := by rw [h_wA]
      _ = B * (w * B) * A := by simp only [mul_assoc]
      _ = B * (A * w) * A := by rw [h_wB]
      _ = B * A * w * A := by simp only [mul_assoc]
      _ = B * A * (w * A) := by rw [mul_assoc (a := B * A) (b := w) (c := A)]
      _ = B * A * (B * w) := by rw [h_wA]
      _ = B * A * B * w := by simp only [mul_assoc]
  have h_w_eq_BAB : w = B * A * B := by
    calc w
        = w * w * w⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
      _ = (B * A * B * w) * w⁻¹ := by rw [h_sq]
      _ = B * A * B * w * w⁻¹ := by simp only [mul_assoc]
      _ = B * A * B * (w * w⁻¹) :=
          by rw [mul_assoc (a := B * A * B) (b := w) (c := w⁻¹)]
      _ = B * A * B * 1 := by rw [mul_inv_cancel]
      _ = B * A * B := by rw [mul_one]
  have h_coe_neg : (↑(-u⁻¹ : Rˣ) : R) = -(↑u⁻¹ : R) :=
    coe_neg_units (R := R) (u := u⁻¹)
  have h_inv_neg_val : (↑((-u⁻¹ : Rˣ)⁻¹) : R) = -(↑((u⁻¹ : Rˣ)⁻¹) : R) :=
    coe_inv_neg_units (R := R) (u := u⁻¹)
  have h_inv_inv_val : (↑((u⁻¹ : Rˣ)⁻¹) : R) = (↑u : R) := by
    have hu : ((u⁻¹ : Rˣ)⁻¹ : Rˣ) = u := inv_inv u
    rw [hu]
  have h_mid : -(↑((-u⁻¹ : Rˣ)⁻¹) : R) = (↑u : R) := by
    calc -(↑((-u⁻¹ : Rˣ)⁻¹) : R)
        = -(-(↑((u⁻¹ : Rˣ)⁻¹) : R)) := by rw [h_inv_neg_val]
      _ = (↑((u⁻¹ : Rˣ)⁻¹) : R) := by rw [neg_neg]
      _ = (↑u : R) := by rw [h_inv_inv_val]
  have h_wji_eq_BAB : weyl (R := R) j i hij.symm (-u⁻¹) = B * A * B := by
    calc weyl (R := R) j i hij.symm (-u⁻¹)
        = x j i hij.symm (↑(-u⁻¹ : Rˣ) : R) *
            x i j hij (-(↑((-u⁻¹ : Rˣ)⁻¹) : R)) *
            x j i hij.symm (↑(-u⁻¹ : Rˣ) : R) := rfl
      _ = x j i hij.symm (-(↑u⁻¹ : R)) *
            x i j hij (-(↑((-u⁻¹ : Rˣ)⁻¹) : R)) *
            x j i hij.symm (-(↑u⁻¹ : R)) := by rw [h_coe_neg]
      _ = x j i hij.symm (-(↑u⁻¹ : R)) *
            x i j hij (↑u : R) *
            x j i hij.symm (-(↑u⁻¹ : R)) := by rw [h_mid]
      _ = B * A * B := rfl
  calc weyl (R := R) i j hij u
      = w := rfl
    _ = B * A * B := h_w_eq_BAB
    _ = weyl (R := R) j i hij.symm (-u⁻¹) := h_wji_eq_BAB.symm

private theorem weyl_conj_weyl_kj
    (i j k : ℕ) (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j)
    (u v : Rˣ) :
    weyl (R := R) i k hik u * weyl k j hkj v *
        (weyl i k hik u)⁻¹ =
      weyl i j hij (u * v) := by
  let W := weyl (R := R) i k hik u
  have hLeft (a : R) :
      MulAut.conj W (x k j hkj a) = x i j hij ((↑u : R) * a) := by
    change W * x k j hkj a * W⁻¹ = x i j hij ((↑u : R) * a)
    exact weyl_conj_x_jk (R := R) i k j hik hkj hij u a
  have hRight (a : R) :
      MulAut.conj W (x j k hkj.symm a) =
        x j i hij.symm (a * (↑u⁻¹ : R)) := by
    change W * x j k hkj.symm a * W⁻¹ =
      x j i hij.symm (a * (↑u⁻¹ : R))
    exact weyl_conj_x_kj (R := R) i k j hik hkj hij u a
  have hMul : (↑u : R) * (↑v : R) = (↑(u * v) : R) := by
    rw [Units.val_mul]
  have hInvCoeff :
      (-(↑v⁻¹ : R)) * (↑u⁻¹ : R) =
        -(↑(u * v)⁻¹ : R) := by
    rw [neg_mul, mul_inv_rev, Units.val_mul]
  change MulAut.conj W (weyl k j hkj v) = weyl i j hij (u * v)
  simp only [weyl, map_mul, hLeft, hRight]
  rw [hMul, hInvCoeff]

/-- Shared-middle-index Weyl conjugation: conjugating `weyl k j v` by
`weyl i k u` (sharing the middle index `k`) gives `weyl i j (u * v)`.
This holds over any `[Ring R]`; no field hypothesis is used.
No torus or cocycle identity is claimed. -/
public theorem weyl_conj_weyl_mixed (i j k : ℕ) (hij : i ≠ j) (hik : i ≠ k)
    (hkj : k ≠ j) (u v : Rˣ) :
    weyl (R := R) i k hik u * weyl k j hkj v * (weyl i k hik u)⁻¹ =
      weyl (R := R) i j hij (u * v) :=
  weyl_conj_weyl_kj (R := R) i j k hij hik hkj u v

private theorem weyl_neg_one_conj_weyl
    (i j k : ℕ) (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j)
    (u : Rˣ) :
    weyl (R := R) i k hik (-1 : Rˣ) * weyl i j hij u *
        (weyl i k hik (-1 : Rˣ))⁻¹ =
      weyl k j hkj u := by
  let W := weyl (R := R) i k hik (-1 : Rˣ)
  have hLeftCoeff (a : R) :
      -((↑((-1 : Rˣ)⁻¹) : R) * a) = a := by
    rw [← neg_mul,
      neg_coe_inv_neg_units (R := R) (u := (1 : Rˣ)),
      inv_one, Units.val_one, one_mul]
  have hRightCoeff (a : R) :
      -(a * (↑(-1 : Rˣ) : R)) = a := by
    rw [coe_neg_units (R := R) (u := (1 : Rˣ)),
      Units.val_one, mul_neg, mul_one, neg_neg]
  have hLeft (a : R) :
      (MulAut.conj W) (x i j hij a) = x k j hkj a := by
    change W * x i j hij a * W⁻¹ = x k j hkj a
    simpa only [W, hLeftCoeff] using
      (weyl_conj_x_ik (R := R) i k j hik hkj hij (-1 : Rˣ) a)
  have hRight (a : R) :
      (MulAut.conj W) (x j i hij.symm a) = x j k hkj.symm a := by
    change W * x j i hij.symm a * W⁻¹ = x j k hkj.symm a
    simpa only [W, hRightCoeff] using
      (weyl_conj_x_ki (R := R) i k j hik hkj hij (-1 : Rˣ) a)
  change MulAut.conj W (weyl i j hij u) = weyl k j hkj u
  simp only [weyl, map_mul, hLeft, hRight]

/-- Conjugation by `weyl i k (-1)` transports the first index of `torus i j u` to `k`. -/
public theorem torus_conj_w_ik
    (i j k : ℕ) (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j)
    (u : Rˣ) :
    weyl (R := R) i k hik (-1 : Rˣ) * torus i j hij u *
        (weyl i k hik (-1 : Rˣ))⁻¹ =
      torus k j hkj u := by
  change MulAut.conj (weyl (R := R) i k hik (-1 : Rˣ)) (torus i j hij u) =
    torus k j hkj u
  simp only [torus, map_mul]
  calc MulAut.conj (weyl (R := R) i k hik (-1 : Rˣ)) (weyl i j hij u) *
        MulAut.conj (weyl (R := R) i k hik (-1 : Rˣ))
          (weyl i j hij (-1 : Rˣ))
      = weyl k j hkj u * weyl k j hkj (-1 : Rˣ) := by
        rw [MulAut.conj_apply, MulAut.conj_apply,
          weyl_neg_one_conj_weyl (R := R) i j k hij hik hkj u,
          weyl_neg_one_conj_weyl (R := R) i j k hij hik hkj (-1 : Rˣ)]
    _ = torus k j hkj u := by
        simp only [torus]

private theorem weyl_neg_one_conj_weyl_second
    (i j k : ℕ) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (u : Rˣ) :
    weyl (R := R) j k hjk (-1 : Rˣ) * weyl i j hij u *
        (weyl j k hjk (-1 : Rˣ))⁻¹ =
      weyl i k hik u := by
  let W := weyl (R := R) j k hjk (-1 : Rˣ)
  have hLeftCoeff (a : R) :
      -((↑((-1 : Rˣ)⁻¹) : R) * a) = a := by
    rw [← neg_mul,
      neg_coe_inv_neg_units (R := R) (u := (1 : Rˣ)),
      inv_one, Units.val_one, one_mul]
  have hRightCoeff (a : R) :
      -(a * (↑(-1 : Rˣ) : R)) = a := by
    rw [coe_neg_units (R := R) (u := (1 : Rˣ)),
      Units.val_one, mul_neg, mul_one, neg_neg]
  have hLeft (a : R) :
      (MulAut.conj W) (x i j hij a) = x i k hik a := by
    change W * x i j hij a * W⁻¹ = x i k hik a
    simpa only [W, hRightCoeff] using
      (weyl_conj_x_ki (R := R) j k i hjk hik.symm hij.symm
        (-1 : Rˣ) a)
  have hRight (a : R) :
      (MulAut.conj W) (x j i hij.symm a) = x k i hik.symm a := by
    change W * x j i hij.symm a * W⁻¹ = x k i hik.symm a
    simpa only [W, hLeftCoeff] using
      (weyl_conj_x_ik (R := R) j k i hjk hik.symm hij.symm
        (-1 : Rˣ) a)
  change MulAut.conj W (weyl i j hij u) = weyl i k hik u
  simp only [weyl, map_mul, hLeft, hRight]

/-- Conjugation by `weyl j k (-1)` transports the second index of `torus i j u` to `k`. -/
public theorem torus_conj_w_jk
    (i j k : ℕ) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (u : Rˣ) :
    weyl (R := R) j k hjk (-1 : Rˣ) * torus i j hij u *
        (weyl j k hjk (-1 : Rˣ))⁻¹ =
      torus i k hik u := by
  change MulAut.conj (weyl (R := R) j k hjk (-1 : Rˣ)) (torus i j hij u) =
    torus i k hik u
  simp only [torus, map_mul]
  calc MulAut.conj (weyl (R := R) j k hjk (-1 : Rˣ)) (weyl i j hij u) *
        MulAut.conj (weyl (R := R) j k hjk (-1 : Rˣ))
          (weyl i j hij (-1 : Rˣ))
      = weyl i k hik u * weyl i k hik (-1 : Rˣ) := by
        rw [MulAut.conj_apply, MulAut.conj_apply,
          weyl_neg_one_conj_weyl_second (R := R) i j k hij hjk hik u,
          weyl_neg_one_conj_weyl_second (R := R) i j k hij hjk hik
            (-1 : Rˣ)]
    _ = torus i k hik u := by
        simp only [torus]

/-- Conjugating one torus word by another sharing its first index. -/
public theorem torus_conj_torus
    (i j k : ℕ) (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j)
    (u v : Rˣ) :
    torus (R := R) i k hik u * torus i j hij v *
        (torus i k hik u)⁻¹ =
      torus i j hij (u * v) * (torus i j hij u)⁻¹ := by
  let Wu := weyl (R := R) i k hik u
  let Wm := weyl (R := R) i k hik (-1 : Rˣ)
  have hConjTorus :
      Wu * torus k j hkj v * Wu⁻¹ =
        weyl (R := R) i j hij (u * v) *
          weyl (R := R) i j hij (-u) := by
    change MulAut.conj Wu (torus k j hkj v) =
      weyl (R := R) i j hij (u * v) * weyl (R := R) i j hij (-u)
    simp only [torus, map_mul, MulAut.conj_apply]
    rw [weyl_conj_weyl_kj (R := R) i j k hij hik hkj u v,
      weyl_conj_weyl_kj (R := R) i j k hij hik hkj u (-1 : Rˣ)]
    simp
  have hTorusDecomp : torus (R := R) i k hik u = Wu * Wm := rfl
  calc torus (R := R) i k hik u * torus i j hij v *
        (torus (R := R) i k hik u)⁻¹
      = (Wu * Wm) * torus i j hij v * (Wu * Wm)⁻¹ := by
        rw [hTorusDecomp]
    _ = Wu * (Wm * torus i j hij v * Wm⁻¹) * Wu⁻¹ := by
        simp only [mul_assoc, mul_inv_rev]
    _ = Wu * torus k j hkj v * Wu⁻¹ := by
        rw [torus_conj_w_ik (R := R) i j k hij hik hkj v]
    _ = weyl (R := R) i j hij (u * v) *
          weyl (R := R) i j hij (-u) := hConjTorus
    _ = weyl (R := R) i j hij (u * v) *
          (weyl (R := R) i j hij u)⁻¹ := by
        rw [← weyl_neg_eq_inv (R := R) i j hij u]
    _ = torus (R := R) i j hij (u * v) *
          (torus (R := R) i j hij u)⁻¹ := by
        simp only [torus, mul_inv_rev, mul_assoc, mul_inv_cancel_left]

/-- Conjugation of `x i k` by `torus i j` scales the coefficient by `u` on the left. -/
public theorem torus_conj_x_ik (i j k : ℕ) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (u : Rˣ) (a : R) :
    torus (R := R) i j hij u * x i k hik a * (torus i j hij u)⁻¹ =
      x i k hik ((↑u : R) * a) := by
  let Wu := weyl (R := R) i j hij u
  let Wm := weyl (R := R) i j hij (-1 : Rˣ)
  have hTorusDecomp : torus (R := R) i j hij u = Wu * Wm := rfl
  have hCoeff : -((↑((-1 : Rˣ)⁻¹) : R) * a) = a := by
    rw [← neg_mul, neg_coe_inv_neg_units (R := R) (u := (1 : Rˣ)),
      inv_one, Units.val_one, one_mul]
  have hInner : Wm * x i k hik a * Wm⁻¹ = x j k hjk a := by
    have h := weyl_conj_x_ik (R := R) i j k hij hjk hik (-1 : Rˣ) a
    rw [hCoeff] at h
    exact h
  calc torus (R := R) i j hij u * x i k hik a * (torus i j hij u)⁻¹
      = (Wu * Wm) * x i k hik a * (Wu * Wm)⁻¹ := by rw [hTorusDecomp]
    _ = Wu * (Wm * x i k hik a * Wm⁻¹) * Wu⁻¹ := by
        simp only [mul_assoc, mul_inv_rev]
    _ = Wu * x j k hjk a * Wu⁻¹ := by rw [hInner]
    _ = x i k hik ((↑u : R) * a) :=
        weyl_conj_x_jk (R := R) i j k hij hjk hik u a

/-- Conjugation of `x j k` by `torus i j` scales the coefficient by `u⁻¹` on the left. -/
public theorem torus_conj_x_jk (i j k : ℕ) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (u : Rˣ) (a : R) :
    torus (R := R) i j hij u * x j k hjk a * (torus i j hij u)⁻¹ =
      x j k hjk ((↑u⁻¹ : R) * a) := by
  let Wu := weyl (R := R) i j hij u
  let Wm := weyl (R := R) i j hij (-1 : Rˣ)
  have hTorusDecomp : torus (R := R) i j hij u = Wu * Wm := rfl
  have hCoeff1 : (↑(-1 : Rˣ) : R) * a = -a := by
    rw [coe_neg_units (R := R) (u := (1 : Rˣ)), Units.val_one, neg_one_mul]
  have hInner : Wm * x j k hjk a * Wm⁻¹ = x i k hik (-a) := by
    have h := weyl_conj_x_jk (R := R) i j k hij hjk hik (-1 : Rˣ) a
    rw [hCoeff1] at h
    exact h
  have hCoeff2 : -((↑u⁻¹ : R) * (-a)) = (↑u⁻¹ : R) * a := by
    rw [mul_neg, neg_neg]
  have hOuter :
      Wu * x i k hik (-a) * Wu⁻¹ = x j k hjk ((↑u⁻¹ : R) * a) := by
    have h := weyl_conj_x_ik (R := R) i j k hij hjk hik u (-a)
    rw [hCoeff2] at h
    exact h
  calc torus (R := R) i j hij u * x j k hjk a * (torus i j hij u)⁻¹
      = (Wu * Wm) * x j k hjk a * (Wu * Wm)⁻¹ := by rw [hTorusDecomp]
    _ = Wu * (Wm * x j k hjk a * Wm⁻¹) * Wu⁻¹ := by
      simp only [mul_assoc, mul_inv_rev]
    _ = Wu * x i k hik (-a) * Wu⁻¹ := by rw [hInner]
    _ = x j k hjk ((↑u⁻¹ : R) * a) := hOuter

/-- Conjugation of `x k i` by `torus i j` scales the coefficient by `u⁻¹` on the right. -/
public theorem torus_conj_x_ki (i j k : ℕ) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (u : Rˣ) (a : R) :
    torus (R := R) i j hij u * x k i hik.symm a * (torus i j hij u)⁻¹ =
      x k i hik.symm (a * (↑u⁻¹ : R)) := by
  let Wu := weyl (R := R) i j hij u
  let Wm := weyl (R := R) i j hij (-1 : Rˣ)
  have hTorusDecomp : torus (R := R) i j hij u = Wu * Wm := rfl
  have hCoeNeg : (↑(-1 : Rˣ) : R) = (-1 : R) := by
    rw [coe_neg_units (R := R) (u := (1 : Rˣ)), Units.val_one]
  have hInnerCoeff : -(a * (↑(-1 : Rˣ) : R)) = a := by
    rw [hCoeNeg, mul_neg, mul_one, neg_neg]
  have hInner : Wm * x k i hik.symm a * Wm⁻¹ = x k j hjk.symm a := by
    have h := weyl_conj_x_ki (R := R) i j k hij hjk hik (-1 : Rˣ) a
    rw [hInnerCoeff] at h
    exact h
  calc torus (R := R) i j hij u * x k i hik.symm a * (torus i j hij u)⁻¹
      = (Wu * Wm) * x k i hik.symm a * (Wu * Wm)⁻¹ := by rw [hTorusDecomp]
    _ = Wu * (Wm * x k i hik.symm a * Wm⁻¹) * Wu⁻¹ := by
        simp only [mul_assoc, mul_inv_rev]
    _ = Wu * x k j hjk.symm a * Wu⁻¹ := by rw [hInner]
    _ = x k i hik.symm (a * (↑u⁻¹ : R)) :=
        weyl_conj_x_kj (R := R) i j k hij hjk hik u a

/-- Conjugation of `x k j` by `torus i j` scales the coefficient by `u` on the right. -/
public theorem torus_conj_x_kj (i j k : ℕ) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (u : Rˣ) (a : R) :
    torus (R := R) i j hij u * x k j hjk.symm a * (torus i j hij u)⁻¹ =
      x k j hjk.symm (a * (↑u : R)) := by
  let Wu := weyl (R := R) i j hij u
  let Wm := weyl (R := R) i j hij (-1 : Rˣ)
  have hTorusDecomp : torus (R := R) i j hij u = Wu * Wm := rfl
  have hCoeInvNeg : (↑(-1 : Rˣ)⁻¹ : R) = (-1 : R) := by
    simp only [coe_inv_neg_units, inv_one, Units.val_one]
  have hInnerCoeff : a * (↑(-1 : Rˣ)⁻¹ : R) = -a := by
    rw [hCoeInvNeg, mul_neg, mul_one]
  have hInner : Wm * x k j hjk.symm a * Wm⁻¹ = x k i hik.symm (-a) := by
    have h := weyl_conj_x_kj (R := R) i j k hij hjk hik (-1 : Rˣ) a
    rw [hInnerCoeff] at h
    exact h
  have hOuterCoeff : -((-a) * (↑u : R)) = a * (↑u : R) := by
    rw [neg_mul, neg_neg]
  have hOuter : Wu * x k i hik.symm (-a) * Wu⁻¹ = x k j hjk.symm (a * (↑u : R)) := by
    have h := weyl_conj_x_ki (R := R) i j k hij hjk hik u (-a)
    rw [hOuterCoeff] at h
    exact h
  calc torus (R := R) i j hij u * x k j hjk.symm a * (torus i j hij u)⁻¹
      = (Wu * Wm) * x k j hjk.symm a * (Wu * Wm)⁻¹ := by rw [hTorusDecomp]
    _ = Wu * (Wm * x k j hjk.symm a * Wm⁻¹) * Wu⁻¹ := by
        simp only [mul_assoc, mul_inv_rev]
    _ = Wu * x k i hik.symm (-a) * Wu⁻¹ := by rw [hInner]
    _ = x k j hjk.symm (a * (↑u : R)) := hOuter

/-- `torus` at `1` is trivial. -/
public theorem torus_one (i j : ℕ) (hij : i ≠ j) :
    torus (R := R) i j hij (1 : Rˣ) = 1 := by
  unfold torus
  have h : weyl (R := R) i j hij (-1 : Rˣ) = (weyl i j hij (1 : Rˣ))⁻¹ := by
    simpa using weyl_neg_eq_inv (R := R) i j hij (1 : Rˣ)
  rw [h, mul_inv_cancel]

/-- Inverse Weyl word for `torus`. -/
public theorem torus_inv (i j : ℕ) (hij : i ≠ j) (u : Rˣ) :
    (torus (R := R) i j hij u)⁻¹ = weyl i j hij (1 : Rˣ) * weyl i j hij (-u) := by
  unfold torus
  rw [mul_inv_rev]
  have h1 : (weyl (R := R) i j hij (-1 : Rˣ))⁻¹ = weyl i j hij (1 : Rˣ) := by
    have h := weyl_neg_eq_inv (R := R) i j hij (1 : Rˣ)
    rw [h, inv_inv]
  have h2 : (weyl (R := R) i j hij u)⁻¹ = weyl i j hij (-u) :=
    (weyl_neg_eq_inv (R := R) i j hij u).symm
  rw [h1, h2]

/-- Same-root torus conjugation `i=j` for fields: `torus i j u`
conjugates `x i j a` to `x i j (u*a*u)`. Derived from `x_chev`
commutator `[x i k a, x k j 1] = x i j a` with private auxiliary
`k = max i j + 1` and accepted distinct-index `torus_conj_x_ik`
and `torus_conj_x_kj`. Char2 safe. -/
public theorem torus_conj_x_ij {F : Type u} [Field F] (i j : ℕ)
    (hij : i ≠ j) (u : Fˣ) (a : F) :
    torus (R := F) i j hij u * x i j hij a * (torus i j hij u)⁻¹ =
      x i j hij ((↑u : F) * a * (↑u : F)) := by
  let k := max i j + 1
  have hk_gt_i : i < k := by
    have : i ≤ max i j := Nat.le_max_left i j
    omega
  have hk_gt_j : j < k := by
    have : j ≤ max i j := Nat.le_max_right i j
    omega
  have hjk : j ≠ k := Nat.ne_of_lt hk_gt_j
  have hik : i ≠ k := Nat.ne_of_lt hk_gt_i
  have hkj : k ≠ j := Ne.symm hjk
  have hx_eq : x (R := F) i j hij a =
      ⁅x i k hik a, x k j hkj (1 : F)⁆ := by
    have hchev : ⁅x (R := F) i k hik a, x k j hkj (1 : F)⁆ =
        x i j hij (a * 1) :=
      x_chev (R := F) i k j hik hkj hij a (1 : F)
    simp only [mul_one] at hchev
    exact hchev.symm
  let w := torus (R := F) i j hij u
  have h_conj_ik : w * x i k hik a * w⁻¹ =
      x i k hik ((↑u : F) * a) :=
    torus_conj_x_ik (R := F) i j k hij hjk hik u a
  have h_conj_kj : w * x k j hkj (1 : F) * w⁻¹ =
      x k j hkj ((1 : F) * (↑u : F)) :=
    torus_conj_x_kj (R := F) i j k hij hjk hik u (1 : F)
  have h_one_mul : (1 : F) * (↑u : F) = (↑u : F) := one_mul _
  calc w * x (R := F) i j hij a * w⁻¹
      = w * ⁅x i k hik a, x k j hkj (1 : F)⁆ * w⁻¹ := by
        rw [hx_eq]
    _ = ⁅w * x i k hik a * w⁻¹, w * x k j hkj (1 : F) * w⁻¹⁆ := by
        rw [conjugate_commutatorElement]
    _ = ⁅x i k hik ((↑u : F) * a), x k j hkj ((1 : F) * (↑u : F))⁆ := by
        rw [h_conj_ik, h_conj_kj]
    _ = ⁅x i k hik ((↑u : F) * a), x k j hkj (↑u : F)⁆ := by
        rw [h_one_mul]
    _ = x i j hij (((↑u : F) * a) * (↑u : F)) := by
        exact x_chev (R := F) i k j hik hkj hij ((↑u : F) * a) (↑u : F)
    _ = x i j hij ((↑u : F) * a * (↑u : F)) := by
        rw [mul_assoc]

/-- Same-root opposite-root torus conjugation `j,i` for fields:
`torus i j u` conjugates `x j i a` to `x j i ((u⁻¹)*a*(u⁻¹))`.
Derived from `x_chev` commutator `[x j k a, x k i 1] = x j i a`
with private auxiliary `k = max i j + 1` and accepted
distinct-index `torus_conj_x_jk` and `torus_conj_x_ki`.
Char2 safe. No exact torus multiplicativity used. -/
public theorem torus_conj_x_ji {F : Type u} [Field F] (i j : ℕ)
    (hij : i ≠ j) (u : Fˣ) (a : F) :
    torus (R := F) i j hij u * x j i hij.symm a *
        (torus i j hij u)⁻¹ =
      x j i hij.symm ((↑u⁻¹ : F) * a * (↑u⁻¹ : F)) := by
  let k := max i j + 1
  have hk_gt_i : i < k := by
    have : i ≤ max i j := Nat.le_max_left i j
    omega
  have hk_gt_j : j < k := by
    have : j ≤ max i j := Nat.le_max_right i j
    omega
  have hjk : j ≠ k := Nat.ne_of_lt hk_gt_j
  have hik : i ≠ k := Nat.ne_of_lt hk_gt_i
  have hki : k ≠ i := Ne.symm hik
  have hx_eq : x (R := F) j i hij.symm a =
      ⁅x j k hjk a, x k i hki (1 : F)⁆ := by
    have hchev : ⁅x (R := F) j k hjk a, x k i hki (1 : F)⁆ =
        x j i hij.symm (a * 1) :=
      x_chev (R := F) j k i hjk hki hij.symm a (1 : F)
    simp only [mul_one] at hchev
    exact hchev.symm
  let w := torus (R := F) i j hij u
  have h_conj_jk : w * x j k hjk a * w⁻¹ =
      x j k hjk ((↑u⁻¹ : F) * a) :=
    torus_conj_x_jk (R := F) i j k hij hjk hik u a
  have h_conj_ki : w * x k i hki (1 : F) * w⁻¹ =
      x k i hki ((1 : F) * (↑u⁻¹ : F)) :=
    torus_conj_x_ki (R := F) i j k hij hjk hik u (1 : F)
  have h_one_mul : (1 : F) * (↑u⁻¹ : F) = (↑u⁻¹ : F) := one_mul _
  calc w * x (R := F) j i hij.symm a * w⁻¹
      = w * ⁅x j k hjk a, x k i hki (1 : F)⁆ * w⁻¹ := by
        rw [hx_eq]
    _ = ⁅w * x j k hjk a * w⁻¹,
          w * x k i hki (1 : F) * w⁻¹⁆ := by
        rw [conjugate_commutatorElement]
    _ = ⁅x j k hjk ((↑u⁻¹ : F) * a),
          x k i hki ((1 : F) * (↑u⁻¹ : F))⁆ := by
        rw [h_conj_jk, h_conj_ki]
    _ = ⁅x j k hjk ((↑u⁻¹ : F) * a),
          x k i hki (↑u⁻¹ : F)⁆ := by
        rw [h_one_mul]
    _ = x j i hij.symm (((↑u⁻¹ : F) * a) * (↑u⁻¹ : F)) := by
        exact x_chev (R := F) j k i hjk hki hij.symm
          ((↑u⁻¹ : F) * a) (↑u⁻¹ : F)
    _ = x j i hij.symm ((↑u⁻¹ : F) * a * (↑u⁻¹ : F)) := by
        rw [mul_assoc]


/-- `x_{ij}(a)` as commutator `[x_{ik}(a), x_{kj}(1)]` when `i,j,k` distinct.
Uses only `x_chev` with `a*1 = a`; no opposite pair. -/
public theorem x_ij_eq_chev_ik_kj {F : Type u} [Field F]
    (i j k : ℕ) (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) (a : F) :
    x (R := F) i j hij a = ⁅x i k hik a, x k j hkj (1 : F)⁆ := by
  have h := x_chev (R := F) i k j hik hkj hij a (1 : F)
  simpa [mul_one] using h.symm

/-- `x_{ji}(b)` as commutator `[x_{jl}(b), x_{li}(1)]` when `j,l,i` distinct.
Uses only `x_chev` with `b*1 = b`; no opposite pair. -/
public theorem x_ji_eq_chev_jl_li {F : Type u} [Field F]
    (i j l : ℕ) (hij : i ≠ j) (hjl : j ≠ l) (hli : l ≠ i) (b : F) :
    x (R := F) j i hij.symm b = ⁅x j l hjl b, x l i hli (1 : F)⁆ := by
  have h := x_chev (R := F) j l i hjl hli hij.symm b (1 : F)
  simpa [mul_one] using h.symm

/-- Field identity `u⁻¹ + a * u⁻¹ * b = 1` with `u = 1 + a*b`.
Preserves order `a*b`; uses only field axioms.
This gives `u⁻¹ + a' * b = 1` for `a' = a * u⁻¹`. -/
public theorem field_inv_add_mul_eq_one_of_one_add_mul_ne_zero {F : Type u} [Field F]
    (a b : F) (hu : 1 + a * b ≠ 0) :
    (1 + a * b)⁻¹ + a * (1 + a * b)⁻¹ * b = 1 := by
  have h : (1 + a * b)⁻¹ * (1 + a * b) = 1 := inv_mul_cancel₀ hu
  calc (1 + a * b)⁻¹ + a * (1 + a * b)⁻¹ * b
      = (1 + a * b)⁻¹ * 1 + (1 + a * b)⁻¹ * (a * b) := by
        rw [mul_one, mul_comm a ((1 + a * b)⁻¹), mul_assoc]
    _ = (1 + a * b)⁻¹ * (1 + a * b) := by rw [← mul_add]
    _ = 1 := h

/-- Valid commuting pair `(j,l)` vs `(i,k)` when `j≠k` and `l≠i`.
Both inequalities follow from `<` via `Nat.ne_of_lt` and `Ne.symm`;
order `i≠l` (`j≠k`) then `j≠k` (`l≠i`) as required by `x_comm`. -/
public theorem x_comm_jl_ik_of_distinct {F : Type u} [Field F]
    (i j k l : ℕ) (hjl : j ≠ l) (hik : i ≠ k) (hjk : j ≠ k) (hli : l ≠ i)
    (b a : F) :
    ⁅x (R := F) j l hjl b, x i k hik a⁆ = 1 :=
  x_comm (R := F) j l i k hjl hik hjk hli b a

/-- Valid commuting pair `(l,i)` vs `(k,j)` when `l≠j` and `i≠k`.
Both inequalities follow from `<` via `Nat.ne_of_lt` and `Ne.symm`;
order `i≠l` (`l≠j`) then `j≠k` (`i≠k`) as required by `x_comm`. -/
public theorem x_comm_li_kj_of_distinct {F : Type u} [Field F]
    (i j k l : ℕ) (hli : l ≠ i) (hkj : k ≠ j) (hlj : l ≠ j) (hki : k ≠ i)
    (a b : F) :
    ⁅x (R := F) l i hli a, x k j hkj b⁆ = 1 :=
  x_comm (R := F) l i k j hli hkj hlj hki.symm a b

section EqualIndexMiddle

/-- Splitting `x_{kj}(1)` via field identity `u⁻¹ + a*u⁻¹*b = 1`.
Uses `field_inv_add_mul_eq_one_of_one_add_mul_ne_zero` and `x_add`.
Exposes `u⁻¹` for torus middle word. -/
public theorem x_kj_one_split_of_one_add_mul {F : Type u} [Field F]
    (k j : ℕ) (hkj : k ≠ j) (a b : F) (hu : 1 + a * b ≠ 0) :
    x (R := F) k j hkj (1 : F) =
      x k j hkj ((1 + a * b)⁻¹) * x k j hkj (a * (1 + a * b)⁻¹ * b) := by
  have hfield : (1 + a * b)⁻¹ + a * (1 + a * b)⁻¹ * b = (1 : F) :=
    field_inv_add_mul_eq_one_of_one_add_mul_ne_zero a b hu
  calc x (R := F) k j hkj (1 : F)
      = x k j hkj ((1 + a * b)⁻¹ + a * (1 + a * b)⁻¹ * b) := by
        rw [hfield]
    _ = x k j hkj ((1 + a * b)⁻¹) * x k j hkj (a * (1 + a * b)⁻¹ * b) := by
        rw [← x_add]

/-- Swap `x_{jl}(b) * x_{kj}(c)` exposing auxiliary `x_{kl}(-(c*b))`.
Only `x_chev` with `k≠j, j≠l, k≠l`; no opposite pair.
Useful middle word connector for two-aux factorization. -/
public theorem x_jl_mul_x_kj_swap {R : Type u} [Ring R]
    (j l k : ℕ) (hjl : j ≠ l) (hkj : k ≠ j) (hkl : k ≠ l) (b c : R) :
    x (R := R) j l hjl b * x k j hkj c =
      x k l hkl (-(c * b)) * x k j hkj c * x j l hjl b := by
  let A := x (R := R) j l hjl b
  let D := x (R := R) k j hkj c
  have hChev : ⁅D, A⁆ = x (R := R) k l hkl (c * b) := by
    simp only [A, D]
    exact x_chev (R := R) k j l hkj hjl hkl c b
  have hChevInv : ⁅A, D⁆ = x (R := R) k l hkl (-(c * b)) := by
    have hInv : ⁅A, D⁆ = ⁅D, A⁆⁻¹ := (commutatorElement_inv D A).symm
    rw [hInv, hChev]
    exact (x_neg (R := R) k l hkl (c * b)).symm
  have hConj : A * D * A⁻¹ = ⁅A, D⁆ * D :=
    conj_eq_commutator_mul A D
  calc x (R := R) j l hjl b * x k j hkj c
      = (A * D * A⁻¹) * A := by
        simp only [A, D, mul_assoc, inv_mul_cancel, mul_one]
    _ = (⁅A, D⁆ * D) * A := by rw [hConj]
    _ = x k l hkl (-(c * b)) * x k j hkj c * x j l hjl b := by
        rw [hChevInv, mul_assoc]

/-- Swap `x_{li}(b) * x_{ik}(a)` exposing auxiliary `x_{lk}(b*a)`.
Only `x_chev` with `l≠i, i≠k, l≠k`; no opposite pair. -/
public theorem x_li_mul_x_ik_swap {R : Type u} [Ring R]
    (l i k : ℕ) (hli : l ≠ i) (hik : i ≠ k) (hlk : l ≠ k) (b a : R) :
    x (R := R) l i hli b * x i k hik a =
      x l k hlk (b * a) * x i k hik a * x l i hli b := by
  let B := x (R := R) l i hli b
  let C := x (R := R) i k hik a
  have hChev : ⁅B, C⁆ = x (R := R) l k hlk (b * a) := by
    simp only [B, C]
    exact x_chev (R := R) l i k hli hik hlk b a
  have hConj : B * C * B⁻¹ = ⁅B, C⁆ * C :=
    conj_eq_commutator_mul B C
  calc x (R := R) l i hli b * x i k hik a
      = (B * C * B⁻¹) * B := by
        simp only [B, C, mul_assoc, inv_mul_cancel, mul_one]
    _ = (⁅B, C⁆ * C) * B := by rw [hConj]
    _ = x l k hlk (b * a) * x i k hik a * x l i hli b := by
        rw [hChev, mul_assoc]

/-- Product `x_{ik}(a) * x_{kj}(b)` equals `x_{ij}(a*b)` followed by swapped factors.
This is the Chevalley reordering `[x_{ik}(a), x_{kj}(b)] = x_{ij}(a*b)` written as
`C*D = x_{ij}(a*b) * D * C`. Only `x_chev`; no opposite. -/
public theorem x_ik_mul_x_kj_eq {R : Type u} [Ring R]
    (i k j : ℕ) (hik : i ≠ k) (hkj : k ≠ j) (hij : i ≠ j) (a b : R) :
    x (R := R) i k hik a * x k j hkj b =
      x i j hij (a * b) * x k j hkj b * x i k hik a := by
  let C := x (R := R) i k hik a
  let D := x (R := R) k j hkj b
  have hChev : ⁅C, D⁆ = x (R := R) i j hij (a * b) := by
    simp only [C, D]
    exact x_chev (R := R) i k j hik hkj hij a b
  have hConj : C * D * C⁻¹ = ⁅C, D⁆ * D :=
    conj_eq_commutator_mul C D
  calc x (R := R) i k hik a * x k j hkj b
      = (C * D * C⁻¹) * C := by
        simp only [C, D, mul_assoc, inv_mul_cancel, mul_one]
    _ = (⁅C, D⁆ * D) * C := by rw [hConj]
    _ = x i j hij (a * b) * x k j hkj b * x i k hik a := by
        rw [hChev, mul_assoc]

/-- Opposite order `x_{kj}(b) * x_{ik}(a)` with auxiliary middle `x_{ij}(-(a*b))`.
Derived from previous via inverse commutator. -/
public theorem x_kj_mul_x_ik_eq {R : Type u} [Ring R]
    (i k j : ℕ) (hik : i ≠ k) (hkj : k ≠ j) (hij : i ≠ j) (a b : R) :
    x (R := R) k j hkj b * x i k hik a =
      x i j hij (-(a * b)) * x i k hik a * x k j hkj b := by
  let C := x (R := R) i k hik a
  let D := x (R := R) k j hkj b
  have hChev : ⁅C, D⁆ = x (R := R) i j hij (a * b) := by
    simp only [C, D]
    exact x_chev (R := R) i k j hik hkj hij a b
  have hChevInv : ⁅D, C⁆ = x (R := R) i j hij (-(a * b)) := by
    have hInv : ⁅D, C⁆ = ⁅C, D⁆⁻¹ := (commutatorElement_inv C D).symm
    rw [hInv, hChev, x_neg]
  have hConj : D * C * D⁻¹ = ⁅D, C⁆ * C :=
    conj_eq_commutator_mul D C
  calc x (R := R) k j hkj b * x i k hik a
      = (D * C * D⁻¹) * D := by
        simp only [C, D, mul_assoc, inv_mul_cancel, mul_one]
    _ = (⁅D, C⁆ * C) * D := by rw [hConj]
    _ = x i j hij (-(a * b)) * x i k hik a * x k j hkj b := by
        rw [hChevInv, mul_assoc]

/-- Disjoint Weyl commutation over any `[Ring R]`: if `{i, j}` and `{k, l}`
are disjoint, witnessed by the four cross hypotheses `i ≠ k`, `i ≠ l`,
`j ≠ k`, `j ≠ l` (together with `i ≠ j` and `k ≠ l`), then `weyl i j u`
commutes with `weyl k l v` for all units `u v`. The proof unfolds `weyl` and
derives the four distinct `x`-factor `Commute` facts from `x_comm` via
`commutatorElement_eq_one_iff_commute.mp`, then composes them with
`Commute.mul_left`/`Commute.mul_right` to cover the repeated `3 × 3` factors.
This is the isolated disjoint-word prerequisite for the even-length boundary
descent. It claims no torus/cocycle identity, no finite containment, no
termination/TWT, no kernel generation, and no Matsumoto theorem. -/
public theorem weyl_comm_of_disjoint {R : Type u} [Ring R]
    (i j k l : ℕ) (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (u v : Rˣ) :
    Commute (weyl (R := R) i j hij u) (weyl (R := R) k l hkl v) := by
  have h11 : Commute (x (R := R) i j hij (↑u : R)) (x k l hkl (↑v : R)) :=
    commutatorElement_eq_one_iff_commute.mp
      (x_comm (R := R) i j k l hij hkl hil hjk (↑u : R) (↑v : R))
  have h12 : Commute (x (R := R) i j hij (↑u : R))
      (x l k hkl.symm (-(↑v⁻¹ : R))) :=
    commutatorElement_eq_one_iff_commute.mp
      (x_comm (R := R) i j l k hij hkl.symm hik hjl (↑u : R) (-(↑v⁻¹ : R)))
  have h21 : Commute (x (R := R) j i hij.symm (-(↑u⁻¹ : R)))
      (x k l hkl (↑v : R)) :=
    commutatorElement_eq_one_iff_commute.mp
      (x_comm (R := R) j i k l hij.symm hkl hjl hik (-(↑u⁻¹ : R)) (↑v : R))
  have h22 : Commute (x (R := R) j i hij.symm (-(↑u⁻¹ : R)))
      (x l k hkl.symm (-(↑v⁻¹ : R))) :=
    commutatorElement_eq_one_iff_commute.mp
      (x_comm (R := R) j i l k hij.symm hkl.symm hjk hil (-(↑u⁻¹ : R))
        (-(↑v⁻¹ : R)))
  have hA : Commute (x (R := R) i j hij (↑u : R))
      (x (R := R) k l hkl (↑v : R) * x l k hkl.symm (-(↑v⁻¹ : R)) *
        x (R := R) k l hkl (↑v : R)) :=
    Commute.mul_right (Commute.mul_right h11 h12) h11
  have hB : Commute (x (R := R) j i hij.symm (-(↑u⁻¹ : R)))
      (x (R := R) k l hkl (↑v : R) * x l k hkl.symm (-(↑v⁻¹ : R)) *
        x (R := R) k l hkl (↑v : R)) :=
    Commute.mul_right (Commute.mul_right h21 h22) h21
  unfold weyl
  exact Commute.mul_left (Commute.mul_left hA hB) hA

end EqualIndexMiddle

end StableSteinberg

end AlgebraicKTheory

end
