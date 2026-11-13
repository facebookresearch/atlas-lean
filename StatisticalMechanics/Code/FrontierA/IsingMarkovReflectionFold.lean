/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Inequalities.FKG

open Finset
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech

variable {E B : Type*} [Fintype E] [DecidableEq E]
  [Fintype B] [DecidableEq B]




theorem fkg_inequality_unnormalized
    (w : ConfigSpace E -> Real) (hwpos : forall omega, 0 < w omega)
    (hwFKG : FKGLatticeCondition w)
    (f g : ConfigSpace E -> Real) (hf : Monotone f) (hg : Monotone g) :
    (∑ omega, w omega * f omega) * (∑ omega, w omega * g omega) <=
      (∑ omega, w omega) * ∑ omega, w omega * (f omega * g omega) := by
  let Z : Real := ∑ omega, w omega
  have hZ : 0 < Z := Finset.sum_pos
    (fun omega _ => hwpos omega) Finset.univ_nonempty
  let pi : ConfigSpace E -> Real := fun omega => w omega / Z
  have hpi0 : 0 <= pi := fun omega =>
    div_nonneg (hwpos omega).le hZ.le
  have hpiSum : ∑ omega, pi omega = 1 := by
    dsimp [pi, Z]
    rw [<- Finset.sum_div]
    exact div_self hZ.ne'
  have hpiFKG : FKGLatticeCondition pi := by
    intro a b
    dsimp [pi]
    rw [div_mul_div_comm, div_mul_div_comm]
    exact (div_le_div_iff_of_pos_right (mul_pos hZ hZ)).2 (hwFKG a b)
  have h := fkg_inequality hpi0 hpiSum hpiFKG hf hg
  have hZ0 := hZ.ne'
  have hfZ : (∑ omega, pi omega * f omega) =
      (∑ omega, w omega * f omega) / Z := by
    dsimp [pi]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro omega _
    ring
  have hgZ : (∑ omega, pi omega * g omega) =
      (∑ omega, w omega * g omega) / Z := by
    dsimp [pi]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro omega _
    ring
  have hfgZ : (∑ omega, pi omega * (f omega * g omega)) =
      (∑ omega, w omega * (f omega * g omega)) / Z := by
    dsimp [pi]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro omega _
    ring
  rw [hfZ, hgZ, hfgZ] at h
  field_simp [hZ0] at h
  simpa [Z, mul_assoc, mul_comm, mul_left_comm] using h





theorem markovReflectionFold_sum_le
    (w : B -> ConfigSpace E -> Real)
    (hwpos : forall b omega, 0 < w b omega)
    (hwFKG : forall b, FKGLatticeCondition (w b))
    (f g : ConfigSpace E -> Real) (hf : Monotone f) (hg : Monotone g) :
    (∑ b : B, ∑ lower : ConfigSpace E, ∑ upper : ConfigSpace E,
        (w b lower * w b upper) * (f lower * g upper)) <=
      ∑ b : B, ∑ lower : ConfigSpace E, ∑ upper : ConfigSpace E,
        (w b lower * w b upper) * (f lower * g lower) := by
  apply Finset.sum_le_sum
  intro b _
  have hb := fkg_inequality_unnormalized
    (w b) (hwpos b) (hwFKG b) f g hf hg
  have hcross :
      (∑ lower : ConfigSpace E, ∑ upper : ConfigSpace E,
          (w b lower * w b upper) * (f lower * g upper)) =
        (∑ lower, w b lower * f lower) *
          ∑ upper, w b upper * g upper := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro lower _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro upper _
    ring
  have hsame :
      (∑ lower : ConfigSpace E, ∑ upper : ConfigSpace E,
          (w b lower * w b upper) * (f lower * g lower)) =
        (∑ upper, w b upper) *
          ∑ lower, w b lower * (f lower * g lower) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro upper _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro lower _
    ring
  rw [hcross, hsame]
  simpa only [mul_comm] using hb

end StatMech.FrontierA
