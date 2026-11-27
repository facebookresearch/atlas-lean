/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Projection.Algebraic
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-!
# Correcting an approximate projection intertwiner

An actual element in the target-source projection corner gives equivalence
when both of its adjoint products are within one of the original projections.
Neumann inverses in the original nonunital algebra's unitization construct
opposite factorization witnesses. Their zero scalar part descends to the
original coefficient algebra. The existing algebraic projection equivalence
construction then supplies the actual partial isometry.
-/

@[expose] public section

noncomputable section

namespace StarProjection

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- **Source support of a partial isometry.** Let `A` be a nonunital complex C*-algebra. If `p` is a
self-adjoint idempotent and `v ∈ A` satisfies `v* v = p`, then `v p = v`. -/
theorem mul_source_projection_eq (p : StarProjection A) (v : A)
    (hp : (p : A) = star v * v) : v * (p : A) = v := by
  let w := v - v * (p : A)
  have hpstar : star (p : A) = (p : A) := p.property.isSelfAdjoint.star_eq
  have hpid : (p : A) * (p : A) = (p : A) := p.property.isIdempotentElem.eq
  have hw : star w * w = 0 := by
    dsimp only [w]
    rw [star_sub, star_mul, hpstar]
    calc
      (star v - (p : A) * star v) * (v - v * (p : A)) =
          star v * v - (star v * v) * (p : A) -
            (p : A) * (star v * v) + (p : A) * ((star v * v) * (p : A)) := by
        noncomm_ring
      _ = 0 := by simp only [← hp, hpid]; abel
  have hnorm : ‖w‖ * ‖w‖ = 0 := by
    rw [← CStarRing.norm_star_mul_self, hw, norm_zero]
  have hwzero : w = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg w])
  exact (sub_eq_zero.mp hwzero).symm

/-- **Target support of a partial isometry.** Let `A` be a nonunital complex C*-algebra. If `q` is a
self-adjoint idempotent and `v ∈ A` satisfies `v v* = q`, then `q v = v`. -/
theorem target_projection_mul_eq (q : StarProjection A) (v : A)
    (hq : (q : A) = v * star v) : (q : A) * v = v := by
  have h := mul_source_projection_eq q (star v) (by simpa only [star_star] using hq)
  simpa only [star_mul, star_star, q.property.isSelfAdjoint.star_eq] using congrArg star h

/-- **Norm bound from the source projection.** Let `A` be a nonunital complex C*-algebra. If `p` is a
self-adjoint idempotent and `v* v = p`, then `‖v‖ ≤ 1`. -/
theorem norm_intertwiner_le_one (p : StarProjection A) (v : A)
    (hp : (p : A) = star v * v) : ‖v‖ ≤ 1 := by
  have hnorm : ‖v‖ * ‖v‖ ≤ 1 := by
    rw [← CStarRing.norm_star_mul_self, ← hp]
    exact IsStarProjection.norm_le (p : A) p.property
  nlinarith [norm_nonneg v]

/-- **Difference bound for adjoint products.** Let `A` be a nonunital complex C*-algebra. For `x,y ∈ A`,
`‖x* x - y* y‖ ≤ ‖x-y‖ (‖x‖ + ‖y‖)`. -/
theorem norm_star_mul_self_sub_le (x y : A) :
    ‖star x * x - star y * y‖ ≤ ‖x - y‖ * (‖x‖ + ‖y‖) := by
  have heq : star x * x - star y * y =
      star x * (x - y) + star (x - y) * y := by
    rw [star_sub]
    noncomm_ring
  rw [heq]
  calc
    _ ≤ ‖star x * (x - y)‖ + ‖star (x - y) * y‖ := norm_add_le _ _
    _ ≤ ‖star x‖ * ‖x - y‖ + ‖star (x - y)‖ * ‖y‖ := by
      gcongr <;> exact norm_mul_le _ _
    _ = ‖x - y‖ * (‖x‖ + ‖y‖) := by simp only [norm_star]; ring

/-- **Projection equivalence from an approximate intertwiner.** Let `A` be a nonunital complex
C*-algebra. If self-adjoint idempotents `p,q` and `x ∈ A` satisfy `x p = x`, `q x = x`, `‖p - x* x‖
< 1`, and `‖q - x x*‖ < 1`, then `p` and `q` are Murray-von Neumann equivalent. -/
theorem murrayVonNeumannEquivalent_of_approximate_intertwiner
    (p q : StarProjection A) (x : A)
    (hxp : x * (p : A) = x) (hqx : (q : A) * x = x)
    (hp : ‖(p : A) - star x * x‖ < 1)
    (hq : ‖(q : A) - x * star x‖ < 1) :
    MurrayVonNeumannEquivalent p q := by
  let P : Unitization ℂ A := Unitization.inr (p : A)
  let Q : Unitization ℂ A := Unitization.inr (q : A)
  let X : Unitization ℂ A := Unitization.inr x
  have hQstar : star Q = Q := by
    simpa only [Q, Unitization.inr_star] using
      congrArg (Unitization.inr : A → Unitization ℂ A) q.property.isSelfAdjoint.star_eq
  have hPid : P * P = P := by
    simpa [P] using congrArg (Unitization.inr : A → Unitization ℂ A)
      p.property.isIdempotentElem.eq
  have hQid : Q * Q = Q := by
    simpa [Q] using congrArg (Unitization.inr : A → Unitization ℂ A)
      q.property.isIdempotentElem.eq
  have hXP : X * P = X := by
    simpa [X, P] using congrArg (Unitization.inr : A → Unitization ℂ A) hxp
  have hQX : Q * X = X := by
    simpa [Q, X] using congrArg (Unitization.inr : A → Unitization ℂ A) hqx
  have hstarXQ : star X * Q = star X := by
    simpa only [star_mul, hQstar] using congrArg star hQX
  have hleft : ‖P - star X * X‖ < 1 := by
    simpa only [P, X, ← Unitization.inr_star, ← Unitization.inr_mul,
      ← Unitization.inr_sub, Unitization.norm_inr] using hp
  have hright : ‖Q - X * star X‖ < 1 := by
    simpa only [Q, X, ← Unitization.inr_star, ← Unitization.inr_mul,
      ← Unitization.inr_sub, Unitization.norm_inr] using hq
  let S : (Unitization ℂ A)ˣ := Units.oneSub (P - star X * X) hleft
  let T : (Unitization ℂ A)ˣ := Units.oneSub (Q - X * star X) hright
  have hSval : S.val = 1 - (P - star X * X) := by simp only [S, Units.val_oneSub]
  have hTval : T.val = 1 - (Q - X * star X) := by simp only [T, Units.val_oneSub]
  have hSp : S.val * P = star X * X := by
    have hz : (star X * X) * P = star X * X := by rw [mul_assoc, hXP]
    rw [hSval]
    calc
      _ = P - P * P + (star X * X) * P := by noncomm_ring
      _ = star X * X := by rw [hPid, hz]; abel
  have hTq : T.val * Q = X * star X := by
    have hz : (X * star X) * Q = X * star X := by rw [mul_assoc, hstarXQ]
    rw [hTval]
    calc
      _ = Q - Q * Q + (X * star X) * Q := by noncomm_ring
      _ = X * star X := by rw [hQid, hz]; abel
  have hTX : T.val * X = X * S.val := by
    rw [hTval, hSval]
    calc
      _ = X - Q * X + (X * star X) * X := by noncomm_ring
      _ = (X * star X) * X := by rw [hQX]; abel
      _ = X * (star X * X) := mul_assoc _ _ _
      _ = X - X * P + X * (star X * X) := by rw [hXP]; abel
      _ = X * (1 - (P - star X * X)) := by noncomm_ring
  have hmove : X * S.inv = T.inv * X := by
    calc
      _ = (T.inv * T.val) * (X * S.inv) := by rw [T.inv_val, one_mul]
      _ = T.inv * ((T.val * X) * S.inv) := by simp only [mul_assoc]
      _ = T.inv * ((X * S.val) * S.inv) := by rw [hTX]
      _ = T.inv * X := by rw [mul_assoc X S.val S.inv, S.val_inv, mul_one]
  let Y : Unitization ℂ A := S.inv * star X
  have hYX : Y * X = P := by
    calc
      _ = S.inv * (star X * X) := by simp only [Y, mul_assoc]
      _ = S.inv * (S.val * P) := by rw [hSp]
      _ = (S.inv * S.val) * P := (mul_assoc _ _ _).symm
      _ = P := by rw [S.inv_val, one_mul]
  have hXY : X * Y = Q := by
    calc
      _ = (X * S.inv) * star X := by simp only [Y, mul_assoc]
      _ = (T.inv * X) * star X := by rw [hmove]
      _ = T.inv * (X * star X) := mul_assoc _ _ _
      _ = T.inv * (T.val * Q) := by rw [hTq]
      _ = Q := by rw [← mul_assoc, T.inv_val, one_mul]
  let y : A := Y.snd
  have hYinr : Unitization.inr y = Y := by
    apply Unitization.ext
    · simp [y, Y, X]
    · rfl
  have hpFactor : (p : A) = y * x := by
    apply Unitization.inr_injective (R := ℂ)
    calc
      Unitization.inr (p : A) = P := rfl
      _ = Y * X := hYX.symm
      _ = Unitization.inr (y * x) := by rw [Unitization.inr_mul, hYinr]
  have hqFactor : (q : A) = x * y := by
    apply Unitization.inr_injective (R := ℂ)
    calc
      Unitization.inr (q : A) = Q := rfl
      _ = X * Y := hXY.symm
      _ = Unitization.inr (x * y) := by rw [Unitization.inr_mul, hYinr]
  exact murrayVonNeumannEquivalent_of_mul_eq_mul p q hpFactor hqFactor

end StarProjection
