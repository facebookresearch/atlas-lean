/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module
public import CSLibExt.MachineLearning.Backpropagation
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Logic.Function.Iterate

open Cslib.MachineLearning.Backpropagation

/-! Iterated tent map as a feedforward ReLU network.

Counting convention: widths alternate `1, 2, 1, 2, ...` (width `1` at
even indices, `2` at odd indices). One tent block is two layers: `R^1`
to `R^2` computing the two shifted ReLUs, then `R^2` to `R^1` forming
their outer ReLU combination. So `forward (2 * k)` traverses `2 * k`
layers with `3 * k` ReLU nodes, counting the readout ReLU of each
block. -/
@[expose] public section
namespace Cslib.MachineLearning.DepthSeparation

/-- The rectified linear unit. -/
noncomputable def relu (x : ℝ) : ℝ := max x 0

/-- The tent map: `2 * x` on `[0, 1 / 2]`, `2 - 2 * x` on `[1 / 2, 1]`, else `0`. -/
noncomputable def tent (x : ℝ) : ℝ :=
  2 * relu x - 4 * relu (x - 1 / 2) + 2 * relu (x - 1)

/-- The `k`-fold iterate of the tent map; `tentIter 0` is the identity. -/
noncomputable def tentIter (k : ℕ) : ℝ → ℝ := tent^[k]

theorem tent_eq_two_mul (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    tent x = 2 * x := by
  have h1 : max x 0 = x := max_eq_left hx0
  have h2 : max (x - 1 / 2) 0 = 0 := max_eq_right (by linarith)
  have h3 : max (x - 1) 0 = 0 := max_eq_right (by linarith)
  unfold tent relu; rw [h1, h2, h3]; ring

theorem tent_eq_two_sub (x : ℝ) (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 1) :
    tent x = 2 - 2 * x := by
  have h1 : max x 0 = x := max_eq_left (by linarith)
  have h2 : max (x - 1 / 2) 0 = x - 1 / 2 := max_eq_left (by linarith)
  have h3 : max (x - 1) 0 = 0 := max_eq_right (by linarith)
  unfold tent relu; rw [h1, h2, h3]; ring

theorem tent_eq_zero_of_nonpos (x : ℝ) (hx : x ≤ 0) : tent x = 0 := by
  have h1 : max x 0 = 0 := max_eq_right hx
  have h2 : max (x - 1 / 2) 0 = 0 := max_eq_right (by linarith)
  have h3 : max (x - 1) 0 = 0 := max_eq_right (by linarith)
  unfold tent relu; rw [h1, h2, h3]; ring

theorem tent_eq_zero_of_ge_one (x : ℝ) (hx : 1 ≤ x) : tent x = 0 := by
  have h1 : max x 0 = x := max_eq_left (by linarith)
  have h2 : max (x - 1 / 2) 0 = x - 1 / 2 := max_eq_left (by linarith)
  have h3 : max (x - 1) 0 = x - 1 := max_eq_left (by linarith)
  unfold tent relu; rw [h1, h2, h3]; ring

theorem tent_nonneg (x : ℝ) : 0 ≤ tent x := by
  rcases le_total x 0 with hx | hx
  · simp only [tent_eq_zero_of_nonpos x hx, le_rfl]
  · rcases le_total x (1 / 2) with hx1 | hx1
    · rw [tent_eq_two_mul x hx hx1]; linarith
    · rcases le_total x 1 with hx2 | hx2
      · rw [tent_eq_two_sub x hx1 hx2]; linarith
      · simp only [tent_eq_zero_of_ge_one x hx2, le_rfl]

theorem tent_le_one (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : tent x ≤ 1 := by
  rcases le_total x (1 / 2) with h | h
  · rw [tent_eq_two_mul x hx0 h]; linarith
  · rw [tent_eq_two_sub x h hx1]; linarith

/-- The tent map as an outer ReLU of two inner ReLUs (Remark 5.3 of
Telgarsky's deep learning theory lecture notes, Section 5). -/
theorem tent_eq_relu (x : ℝ) :
    tent x = relu (2 * relu x - 4 * relu (x - 1 / 2)) := by
  rcases le_total x 1 with hx1 | hx1
  · have h3 : relu (x - 1) = 0 := by
      unfold relu
      exact max_eq_right (by linarith)
    have htent : tent x = 2 * relu x - 4 * relu (x - 1 / 2) := by
      unfold tent
      rw [h3]
      ring
    have hnn : 0 ≤ 2 * relu x - 4 * relu (x - 1 / 2) := by
      rw [← htent]
      exact tent_nonneg x
    rw [htent]
    exact (max_eq_left hnn).symm
  · have h1 : relu x = x := by
      unfold relu
      exact max_eq_left (by linarith)
    have h2 : relu (x - 1 / 2) = x - 1 / 2 := by
      unfold relu
      exact max_eq_left (by linarith)
    rw [tent_eq_zero_of_ge_one x hx1, h1, h2]
    have e : (2 : ℝ) * x - 4 * (x - 1 / 2) = 2 - 2 * x := by ring
    rw [e]
    exact (max_eq_right (by linarith : (2 : ℝ) - 2 * x ≤ 0)).symm

theorem tentIter_zero (x : ℝ) : tentIter 0 x = x :=
  Function.iterate_zero_apply tent x

theorem tentIter_succ (k : ℕ) (x : ℝ) :
    tentIter (k + 1) x = tentIter k (tent x) :=
  Function.iterate_succ_apply tent k x

private theorem tentIter_succ_left (k : ℕ) (x : ℝ) :
    tentIter (k + 1) x = tent (tentIter k x) :=
  Function.iterate_succ_apply' tent k x

theorem tentIter_mem (k : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ tentIter k x ∧ tentIter k x ≤ 1 := by
  induction k generalizing x with
  | zero => rw [tentIter_zero]; exact ⟨hx0, hx1⟩
  | succ k ih =>
    show 0 ≤ tentIter (k + 1) x ∧ tentIter (k + 1) x ≤ 1
    rw [tentIter_succ]
    exact ih (tent x) (tent_nonneg x) (tent_le_one x hx0 hx1)

theorem tent_one_sub (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    tent (1 - x) = tent x := by
  rcases le_total x (1 / 2) with h | h
  · rw [tent_eq_two_sub (1 - x) (by linarith) (by linarith),
      tent_eq_two_mul x hx0 h]; ring
  · rw [tent_eq_two_mul (1 - x) (by linarith) (by linarith),
      tent_eq_two_sub x h hx1]; ring

/-- Proposition 5.1: on `[0, 1]`, the `(k+1)`-fold tent iterate equals the
tent map applied to the fractional part of `2^k * x`. The restriction to
`[0, 1]` is essential: outside it the two sides already differ, as shown
by the boundary test in the test module. -/
theorem tentIter_succ_eq_tent_fract (k : ℕ) (x : ℝ) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) :
    tentIter (k + 1) x = tent (Int.fract ((2 : ℝ) ^ k * x)) := by
  induction k generalizing x with
  | zero =>
    rw [tentIter_succ, tentIter_zero]
    simp only [pow_zero, one_mul]
    rcases lt_or_eq_of_le hx1 with hxlt | hxeq
    · rw [Int.fract_eq_self.mpr ⟨hx0, hxlt⟩]
    · subst hxeq
      rw [tent_eq_zero_of_ge_one 1 le_rfl, Int.fract_one,
        tent_eq_zero_of_nonpos 0 le_rfl]
  | succ k ih =>
    show tentIter (k + 1 + 1) x = tent (Int.fract ((2 : ℝ) ^ (k + 1) * x))
    rw [tentIter_succ, ih (tent x) (tent_nonneg x) (tent_le_one x hx0 hx1)]
    rcases le_total x (1 / 2) with hle | hle
    · have halg : (2 : ℝ) ^ k * (2 * x) = (2 : ℝ) ^ (k + 1) * x := by
        rw [pow_succ]; ring
      rw [tent_eq_two_mul x hx0 hle, halg]
    · have halg : (2 : ℝ) ^ k * (2 - 2 * x)
          = (2 : ℝ) ^ (k + 1) * (1 - x) := by
        rw [pow_succ]; ring
      have hPM : (2 : ℝ) ^ (k + 1) = ((2 ^ (k + 1) : ℕ) : ℝ) := by norm_cast
      have hdecomp : (2 : ℝ) ^ (k + 1) * (1 - x)
          = -((2 : ℝ) ^ (k + 1) * x) + ((2 ^ (k + 1) : ℕ) : ℝ) := by
        rw [hPM]; ring
      rw [tent_eq_two_sub x hle hx1, halg, hdecomp, Int.fract_add_natCast]
      by_cases hf : Int.fract ((2 : ℝ) ^ (k + 1) * x) = 0
      · rw [hf, Int.fract_neg_eq_zero.mpr hf]
      · rw [Int.fract_neg hf]
        exact tent_one_sub _ (Int.fract_nonneg _) (le_of_lt (Int.fract_lt_one _))

/-- Layer widths: `1` at even indices, `2` at odd indices. -/
def tentWidths : ℕ → ℕ := fun n => if n % 2 = 0 then 1 else 2

private theorem tentWidths_of_even (k : ℕ) (hk : k % 2 = 0) : tentWidths k = 1 := by
  change (if k % 2 = 0 then (1 : ℕ) else 2) = 1
  rw [ite_eq_left hk]

theorem tentWidths_of_odd (k : ℕ) (hk : k % 2 ≠ 0) : tentWidths k = 2 := by
  change (if k % 2 = 0 then (1 : ℕ) else 2) = 2
  rw [ite_eq_right hk]

theorem tentWidths_succ_of_even (k : ℕ) (hk : k % 2 = 0) :
    tentWidths (k + 1) = 2 := by
  change (if (k + 1) % 2 = 0 then (1 : ℕ) else 2) = 2
  rw [ite_eq_right (show (k + 1) % 2 ≠ 0 by omega)]

theorem tentWidths_even (i : ℕ) : tentWidths (2 * i) = 1 :=
  tentWidths_of_even (2 * i) (by omega)

theorem tentWidths_odd (i : ℕ) : tentWidths (2 * i + 1) = 2 :=
  tentWidths_of_odd (2 * i + 1) (by omega)

instance tentWidths_neZero (n : ℕ) : NeZero (tentWidths n) := by
  constructor
  change tentWidths n ≠ 0
  change (if n % 2 = 0 then (1 : ℕ) else 2) ≠ 0
  by_cases h : n % 2 = 0
  · rw [ite_eq_left h]; norm_num
  · rw [ite_eq_right h]; norm_num

/-- The vector in `EuclideanSpace ℝ (Fin 1)` with coordinate `x`. -/
def single (x : ℝ) : EuclideanSpace ℝ (Fin 1) :=
  WithLp.toLp 2 fun _ : Fin 1 => x

private theorem single_zero (x : ℝ) : single x 0 = x := rfl

/-- ReLU network for iterated tent maps. Even layers map `R^1` to `R^2`
by the two shifted ReLUs; odd layers map `R^2` to `R^1` by the outer
ReLU readout `relu (2 * y0 - 4 * y1)`. -/
noncomputable def tentNet : Net tentWidths where
  layer := fun k v =>
    dite (k % 2 = 0)
      (fun hk =>
        have hk2 : tentWidths (k + 1) = 2 := tentWidths_succ_of_even k hk
        WithLp.toLp 2 fun j : Fin (tentWidths (k + 1)) =>
          ![relu (v 0), relu (v 0 - 1 / 2)]
            (Fin.cast hk2 j))
      (fun hk =>
        have hk1 : tentWidths k = 2 := tentWidths_of_odd k hk
        have h0 : 0 < tentWidths k := by omega
        have h1 : 1 < tentWidths k := by omega
        WithLp.toLp 2 fun _ : Fin (tentWidths (k + 1)) =>
          relu (2 * v ⟨0, h0⟩ - 4 * v ⟨1, h1⟩))

/-- Construction half of Theorem 5.1: the network computes the `k`-fold
tent iterate. The forward pass through `2 * k` layers uses `3 * k` ReLU
nodes, three per block counting the readout ReLU; at `k = L^2 + 2` this
is `3 * L^2 + 6` nodes and `2 * L^2 + 4` layers. No approximation or
learnability claim is made. -/
theorem tentNet_forward (k : ℕ) (x : ℝ) :
    (tentNet.forward (2 * k) (single x)) 0 = tentIter k x := by
  induction k with
  | zero =>
    simp only [Net.forward]
    change (single x) 0 = tentIter 0 x
    rw [single_zero, tentIter_zero]
  | succ k ih =>
    show (tentNet.forward (2 * (k + 1)) (single x)) 0 = tentIter (k + 1) x
    have hblock : ∀ v : EuclideanSpace ℝ (Fin (tentWidths (2 * k))),
        ((tentNet.layer (2 * k + 1) (tentNet.layer (2 * k) v)) 0)
          = tent (v 0) := by
      intro v
      simp only [tentNet, dite_eq_left (show (2 * k) % 2 = 0 by omega),
        dite_eq_right (show ¬ (2 * k + 1) % 2 = 0 by omega)]
      change relu (2 * ((![relu (v 0), relu (v 0 - 1 / 2)] : Fin 2 → ℝ) 0)
          - 4 * ((![relu (v 0), relu (v 0 - 1 / 2)] : Fin 2 → ℝ) 1))
          = tent (v 0)
      have c0 : ((![relu (v 0), relu (v 0 - 1 / 2)] : Fin 2 → ℝ) 0)
          = relu (v 0) := by simp
      have c1 : ((![relu (v 0), relu (v 0 - 1 / 2)] : Fin 2 → ℝ) 1)
          = relu (v 0 - 1 / 2) := by simp
      rw [c0, c1]
      exact (tent_eq_relu (v 0)).symm
    have h2k : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
    rw [h2k]
    simp only [Net.forward]
    rw [hblock, ih]
    exact (tentIter_succ_left k x).symm

end Cslib.MachineLearning.DepthSeparation
