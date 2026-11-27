/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import MathlibExt.Analysis.Numerical.OrderedDotProductError
public import MathlibExt.Analysis.Numerical.SaturatingRoundHalfUp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Fixed-point FIR filter

A finite impulse-response filter is computed on signed integer codes
at a fixed power-of-two scale, as a zero-initialized left fold. Each
product is rounded half up back to the working scale, each accumulation
saturates to the signed code range, and any saturation is recorded in
an explicit overflow flag.

The flag covers the computed values only: it is set when a rounded
product or a running sum leaves the code range, and it does not check
the coefficient and input codes themselves. The results below hold for
any integer codes, so callers that need signed `w`-bit coefficients and
inputs must check that each code lies between
`SaturatingRoundHalfUp.signedMinCode w` and
`SaturatingRoundHalfUp.signedMaxCode w`.

When no overflow occurs and the real inputs and coefficients are within
half a step of their codes, the decoded output obeys the ordered
dot-product error bound with the coefficient, input and product errors
instantiated at half a step and the accumulation error at zero, because
an in-range accumulation is exact. The bound keeps the coefficient and
input cross term and the exact zero initialization, and an overflowing
trace is excluded rather than silently wrapped.
-/

@[expose] public section

namespace CSLibExt.Algorithms.Numerical.FixedPointFIR


open MathlibExt.Analysis.Numerical

/-- Divide by a power of two, rounding half up (ties toward positive
infinity), on integer codes. -/
def roundHalfUpShift (s : ℕ) (n : ℤ) : ℤ :=
  (n + (2 : ℤ) ^ s / 2) / (2 : ℤ) ^ s

/-- Saturate an integer code into the signed range. -/
def saturate (kmin kmax n : ℤ) : ℤ :=
  max kmin (min kmax n)

/-- One fold step: rounded product, saturating accumulation, and an
overflow flag recording whether either value left the code range. The
codes `hk` and `xk` themselves are not checked. -/
def firStep (s : ℕ) (kmin kmax : ℤ) (acc : ℤ) (flag : Bool) (hk xk : ℤ) :
    ℤ × Bool :=
  let prod := roundHalfUpShift s (hk * xk)
  let raw := acc + prod
  (saturate kmin kmax raw,
    flag || (raw < kmin || kmax < raw) || (prod < kmin || kmax < prod))

/-- Zero-initialized left fold over the first `n` taps. -/
def firFold (s : ℕ) (kmin kmax : ℤ) (h x : ℕ → ℤ) : ℕ → ℤ × Bool
  | 0 => (0, false)
  | n + 1 =>
    let prev := firFold s kmin kmax h x n
    firStep s kmin kmax prev.1 prev.2 (h n) (x n)

/-- Output code of the `m`-tap filter. -/
def firCode {m : ℕ} (s : ℕ) (kmin kmax : ℤ) (h x : Fin m → ℤ) : ℤ :=
  (firFold s kmin kmax (fun i => if hlt : i < m then h ⟨i, hlt⟩ else 0)
    (fun i => if hlt : i < m then x ⟨i, hlt⟩ else 0) m).1

/-- Overflow flag of the `m`-tap filter: set when a rounded product or a
running sum leaves the code range. The coefficient and input codes `h`
and `x` themselves are not checked; callers that need them in range must
check them. -/
def firOverflow {m : ℕ} (s : ℕ) (kmin kmax : ℤ) (h x : Fin m → ℤ) : Bool :=
  (firFold s kmin kmax (fun i => if hlt : i < m then h ⟨i, hlt⟩ else 0)
    (fun i => if hlt : i < m then x ⟨i, hlt⟩ else 0) m).2

/-- Decode an integer code at scale `2 ^ s` to a real value. -/
noncomputable def decode (s : ℕ) (c : ℤ) : ℝ :=
  (c : ℝ) / (2 : ℝ) ^ s

/-- First projection of a fold step. Helper. -/
private theorem firStep_fst (s : ℕ) (kmin kmax acc : ℤ) (flag : Bool)
    (hk xk : ℤ) :
    (firStep s kmin kmax acc flag hk xk).1
      = saturate kmin kmax (acc + roundHalfUpShift s (hk * xk)) := rfl

/-- Second projection of a fold step. Helper. -/
private theorem firStep_snd (s : ℕ) (kmin kmax acc : ℤ) (flag : Bool)
    (hk xk : ℤ) :
    (firStep s kmin kmax acc flag hk xk).2
      = (flag || (decide (acc + roundHalfUpShift s (hk * xk) < kmin) ||
          decide (kmax < acc + roundHalfUpShift s (hk * xk))) ||
        (decide (roundHalfUpShift s (hk * xk) < kmin) ||
          decide (kmax < roundHalfUpShift s (hk * xk)))) := rfl

/-- Saturation is the identity on values already in range. Helper. -/
private theorem saturate_eq_of_mem (kmin kmax n : ℤ)
    (h1 : kmin ≤ n) (h2 : n ≤ kmax) : saturate kmin kmax n = n := by
  unfold saturate
  rw [min_eq_right h2, max_eq_right h1]

/-- Telescoping for the exact left fold. Helper. -/
private theorem accumulator_telescope (P D A : ℕ → ℝ) (m : ℕ)
    (hstep : ∀ j : ℕ, j < m → P j + D j = A (j + 1) - A j)
    (j : ℕ) (hj : j ≤ m) : OrderedDotProductError.accumulator P D j
      = A j - A 0 := by
  induction j with
  | zero => rw [show OrderedDotProductError.accumulator P D 0
      = (0 : ℝ) from rfl]; linarith
  | succ j ih =>
    have hj' : j ≤ m := by omega
    have hlt : j < m := by omega
    have hacc : OrderedDotProductError.accumulator P D (j + 1)
        = OrderedDotProductError.accumulator P D j + P j + D j := rfl
    rw [hacc, ih hj', add_assoc, hstep j hlt]
    linarith

/-- One-step unfolding of the fold, by definition. Helper. -/
private theorem firFold_succ_eq (s : ℕ) (kmin kmax : ℤ) (H X : ℕ → ℤ)
    (n : ℕ) :
    firFold s kmin kmax H X (n + 1) =
      firStep s kmin kmax (firFold s kmin kmax H X n).1
        (firFold s kmin kmax H X n).2 (H n) (X n) := rfl

/-- Fold flags stay false under per-step range bounds. Helper. -/
private theorem firFold_snd_eq_false_of_bounds (s : ℕ) (kmin kmax : ℤ)
    (H X : ℕ → ℤ) (n : ℕ)
    (hbound : ∀ j : ℕ, j < n →
      kmin ≤ roundHalfUpShift s (H j * X j) ∧
      roundHalfUpShift s (H j * X j) ≤ kmax ∧
      kmin ≤ (firFold s kmin kmax H X j).1 + roundHalfUpShift s (H j * X j) ∧
      (firFold s kmin kmax H X j).1 + roundHalfUpShift s (H j * X j) ≤ kmax) :
    (firFold s kmin kmax H X n).2 = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [firFold_succ_eq, firStep_snd, ih (fun j hj => hbound j (by omega))]
    obtain ⟨hp1, hp2, hs1, hs2⟩ := hbound n (Nat.lt_succ_self n)
    have n1 : ¬ ((firFold s kmin kmax H X n).1
        + roundHalfUpShift s (H n * X n) < kmin) := not_lt.mpr hs1
    have n2 : ¬ (kmax < (firFold s kmin kmax H X n).1
        + roundHalfUpShift s (H n * X n)) := not_lt.mpr hs2
    have n3 : ¬ (roundHalfUpShift s (H n * X n) < kmin) := not_lt.mpr hp1
    have n4 : ¬ (kmax < roundHalfUpShift s (H n * X n)) := not_lt.mpr hp2
    simp [n1, n2, n3, n4]

/-- Once set, the overflow flag never clears. Helper. -/
private theorem firFold_flag_mono (s : ℕ) (kmin kmax : ℤ) (H X : ℕ → ℤ)
    (a b : ℕ) (hab : a ≤ b)
    (hflag : (firFold s kmin kmax H X a).2 = true) :
    (firFold s kmin kmax H X b).2 = true := by
  induction b, hab using Nat.le_induction with
  | base => exact hflag
  | succ b _ ih => simp [firFold_succ_eq, firStep_snd, ih]

/-- No overflow at the end means no overflow at any earlier step. Helper. -/
private theorem firFold_all_false (s : ℕ) (kmin kmax : ℤ) (H X : ℕ → ℤ)
    (m : ℕ) (hno : (firFold s kmin kmax H X m).2 = false)
    (j : ℕ) (hj : j ≤ m) : (firFold s kmin kmax H X j).2 = false := by
  by_cases h : (firFold s kmin kmax H X j).2 = true
  · have hm := firFold_flag_mono s kmin kmax H X j m hj h
    rw [hno] at hm
    cases hm
  · exact Bool.eq_false_iff.mpr h

/-- Per-step range bounds from a clean final flag. Helper. -/
private theorem firFold_step_bounds (s : ℕ) (kmin kmax : ℤ) (H X : ℕ → ℤ)
    (m : ℕ) (hno : (firFold s kmin kmax H X m).2 = false)
    (j : ℕ) (hj : j < m) :
    kmin ≤ roundHalfUpShift s (H j * X j) ∧
    roundHalfUpShift s (H j * X j) ≤ kmax ∧
    kmin ≤ (firFold s kmin kmax H X j).1 + roundHalfUpShift s (H j * X j) ∧
    (firFold s kmin kmax H X j).1 + roundHalfUpShift s (H j * X j) ≤ kmax := by
  have h1 : (firFold s kmin kmax H X (j + 1)).2 = false :=
    firFold_all_false s kmin kmax H X m hno (j + 1) (Nat.succ_le_of_lt hj)
  have h0 : (firFold s kmin kmax H X j).2 = false :=
    firFold_all_false s kmin kmax H X m hno j (le_of_lt hj)
  rw [firFold_succ_eq, firStep_snd, h0, Bool.false_or, Bool.or_eq_false_iff] at h1
  obtain ⟨hA, hB⟩ := h1
  rw [Bool.or_eq_false_iff] at hA hB
  obtain ⟨d1, d2⟩ := hA
  obtain ⟨d3, d4⟩ := hB
  have g1 : kmin ≤ (firFold s kmin kmax H X j).1
      + roundHalfUpShift s (H j * X j) :=
    not_lt.mp (of_decide_eq_false d1)
  have g2 : (firFold s kmin kmax H X j).1
      + roundHalfUpShift s (H j * X j) ≤ kmax :=
    not_lt.mp (of_decide_eq_false d2)
  have g3 : kmin ≤ roundHalfUpShift s (H j * X j) :=
    not_lt.mp (of_decide_eq_false d3)
  have g4 : roundHalfUpShift s (H j * X j) ≤ kmax :=
    not_lt.mp (of_decide_eq_false d4)
  exact ⟨g3, g4, g1, g2⟩

/-- Decoding distributes over one clean fold step. Helper. -/
private theorem firFold_succ_decode (s : ℕ) (kmin kmax : ℤ) (H X : ℕ → ℤ)
    (m : ℕ) (hno : (firFold s kmin kmax H X m).2 = false)
    (j : ℕ) (hj : j < m) :
    decode s (firFold s kmin kmax H X (j + 1)).1
      = decode s (firFold s kmin kmax H X j).1
        + decode s (roundHalfUpShift s (H j * X j)) := by
  obtain ⟨_, _, hs1, hs2⟩ :=
    firFold_step_bounds s kmin kmax H X m hno j hj
  have hfst : (firFold s kmin kmax H X (j + 1)).1
      = (firFold s kmin kmax H X j).1 + roundHalfUpShift s (H j * X j) := by
    rw [firFold_succ_eq, firStep_fst, saturate_eq_of_mem _ _ _ hs1 hs2]
  rw [hfst]
  unfold decode
  push_cast
  rw [add_div]

/-- The decoded fold starts at zero. Helper. -/
private theorem decode_firFold_zero (s : ℕ) (kmin kmax : ℤ) (H X : ℕ → ℤ) :
    decode s (firFold s kmin kmax H X 0).1 = 0 := by
  have hfold0 : (firFold s kmin kmax H X 0).1 = 0 := rfl
  rw [hfold0]
  unfold decode
  simp

/-- Rounding half up after a product costs at most half a code unit. -/
theorem roundHalfUpShift_error_le (s : ℕ) (n : ℤ) :
    |(roundHalfUpShift s n : ℝ) - (n : ℝ) / (2 : ℝ) ^ s|
      ≤ (1 : ℝ) / 2 := by
  unfold roundHalfUpShift
  set D : ℤ := (2 : ℤ) ^ s with hD
  set h : ℤ := D / 2 with hh
  set q : ℤ := (n + h) / D with hq
  set r : ℤ := (n + h) % D with hr
  have hDpos : (0 : ℤ) < D := by rw [hD]; exact pow_pos (by norm_num) s
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hqr : D * q + r = n + h := Int.mul_ediv_add_emod _ _
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hDne
  have hr1 : r < D := Int.emod_lt_of_pos _ hDpos
  have hr1Z : r ≤ D - 1 := by omega
  have hh2 : 2 * h + D % 2 = D := Int.mul_ediv_add_emod _ _
  have hm0 : 0 ≤ D % 2 := Int.emod_nonneg _ (by norm_num)
  have hm1 : D % 2 < 2 := Int.emod_lt_of_pos _ (by norm_num)
  have h2lo : 2 * h ≤ D := by omega
  have h2hi : D ≤ 2 * h + 1 := by omega
  have hDposR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hcast : (D : ℝ) * (q : ℝ) + (r : ℝ) = (n : ℝ) + (h : ℝ) := by
    exact_mod_cast hqr
  have hcast'' : r + 1 ≤ D := by omega
  have hr1R' : (r : ℝ) + 1 ≤ (D : ℝ) := by exact_mod_cast hcast''
  have h2loR : (2 : ℝ) * (h : ℝ) ≤ (D : ℝ) := by exact_mod_cast h2lo
  have h2hiR : (D : ℝ) ≤ (2 : ℝ) * (h : ℝ) + 1 := by exact_mod_cast h2hi
  have hr0R : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0
  have hr1R : (r : ℝ) ≤ (D : ℝ) - 1 := by linarith
  have hDS : (D : ℝ) = (2 : ℝ) ^ s := by rw [hD]; norm_cast
  rw [← hDS]
  have key : (q : ℝ) - (n : ℝ) / (D : ℝ) = ((h : ℝ) - (r : ℝ)) / (D : ℝ) := by
    rw [eq_div_iff hDposR.ne']
    have e : ((q : ℝ) - (n : ℝ) / (D : ℝ)) * (D : ℝ)
        = (D : ℝ) * (q : ℝ) - (n : ℝ) := by
      rw [sub_mul, div_mul_cancel₀ _ hDposR.ne', mul_comm (q : ℝ)]
    rw [e]
    linarith [hcast]
  rw [key, abs_div, abs_of_pos hDposR, div_le_iff₀ hDposR, abs_le]
  constructor <;> linarith

/-- Saturation keeps every code inside the signed range. -/
theorem saturate_mem_Icc (kmin kmax n : ℤ) (hk : kmin ≤ kmax) :
    kmin ≤ saturate kmin kmax n ∧ saturate kmin kmax n ≤ kmax := by
  exact ⟨le_max_left _ _, max_le hk (min_le_left _ _)⟩

/-- The fold starts at exactly zero with no overflow. -/
theorem firFold_zero (s : ℕ) (kmin kmax : ℤ) (h x : ℕ → ℤ) :
    firFold s kmin kmax h x 0 = (0, false) := by
  rfl

/-- One-step unfolding of the fold. -/
theorem firFold_succ (s : ℕ) (kmin kmax : ℤ) (h x : ℕ → ℤ) (n : ℕ) :
    firFold s kmin kmax h x (n + 1) =
      firStep s kmin kmax (firFold s kmin kmax h x n).1
        (firFold s kmin kmax h x n).2 (h n) (x n) := by
  rfl

/-- Under representable-range bounds on every product and partial
sum, no overflow is flagged. -/
theorem firOverflow_eq_false_of_range_bounds {m : ℕ} (s : ℕ) (kmin kmax : ℤ)
    (h x : Fin m → ℤ) (hk : kmin ≤ kmax)
    (hbound : ∀ n : ℕ, n < m →
      kmin ≤ roundHalfUpShift s ((fun i => if hlt : i < m then h ⟨i, hlt⟩ else 0) n *
        (fun i => if hlt : i < m then x ⟨i, hlt⟩ else 0) n) ∧
      roundHalfUpShift s ((fun i => if hlt : i < m then h ⟨i, hlt⟩ else 0) n *
        (fun i => if hlt : i < m then x ⟨i, hlt⟩ else 0) n) ≤ kmax ∧
      kmin ≤ (firFold s kmin kmax
          (fun i => if hlt : i < m then h ⟨i, hlt⟩ else 0)
          (fun i => if hlt : i < m then x ⟨i, hlt⟩ else 0) n).1
        + roundHalfUpShift s ((fun i => if hlt : i < m then h ⟨i, hlt⟩ else 0) n *
          (fun i => if hlt : i < m then x ⟨i, hlt⟩ else 0) n) ∧
      (firFold s kmin kmax
          (fun i => if hlt : i < m then h ⟨i, hlt⟩ else 0)
          (fun i => if hlt : i < m then x ⟨i, hlt⟩ else 0) n).1
        + roundHalfUpShift s ((fun i => if hlt : i < m then h ⟨i, hlt⟩ else 0) n *
          (fun i => if hlt : i < m then x ⟨i, hlt⟩ else 0) n) ≤ kmax) :
    firOverflow s kmin kmax h x = false := by
  have _ := hk
  unfold firOverflow
  exact firFold_snd_eq_false_of_bounds s kmin kmax _ _ m hbound

/-- Refinement: with no overflow, the decoded output is exactly the
perturbed fold whose coefficient, input and product perturbations are
the actual decoding and rounding errors of the integer computation and
whose accumulation errors are zero. Overflow only removes this
guarantee: the equation fails on a trace whose running sum saturates at
exactly one step, and still holds on a trace where only a rounded
product leaves the code range. -/
theorem decode_fir_eq_outputPerturbed_of_no_overflow {m : ℕ} (s w : ℕ) (hw : 1 ≤ w)
    (h x : Fin m → ℝ) (hc xc : Fin m → ℤ)
    (hno : firOverflow s (SaturatingRoundHalfUp.signedMinCode w)
      (SaturatingRoundHalfUp.signedMaxCode w) hc xc = false) :
    decode s (firCode s (SaturatingRoundHalfUp.signedMinCode w)
        (SaturatingRoundHalfUp.signedMaxCode w) hc xc)
      = OrderedDotProductError.outputPerturbed m
          h (fun k => decode s (hc k) - h k)
          x (fun k => decode s (xc k) - x k)
          (fun k => decode s (roundHalfUpShift s (hc k * xc k))
            - decode s (hc k) * decode s (xc k))
          (fun _ => 0) := by
  have _ := hw
  set kmin : ℤ := SaturatingRoundHalfUp.signedMinCode w with hkmin
  set kmax : ℤ := SaturatingRoundHalfUp.signedMaxCode w with hkmax
  set H : ℕ → ℤ := (fun i => if hlt : i < m then hc ⟨i, hlt⟩ else 0) with hHdef
  set X : ℕ → ℤ := (fun i => if hlt : i < m then xc ⟨i, hlt⟩ else 0) with hXdef
  set A : ℕ → ℝ := (fun j => decode s (firFold s kmin kmax H X j).1) with hAdef
  have hno' : (firFold s kmin kmax H X m).2 = false := hno
  set dh0 : Fin m → ℝ := (fun k => decode s (hc k) - h k) with hdh0
  set dx0 : Fin m → ℝ := (fun k => decode s (xc k) - x k) with hdx0
  set dp0 : Fin m → ℝ := (fun k => decode s (roundHalfUpShift s (hc k * xc k))
    - decode s (hc k) * decode s (xc k)) with hdp0
  set da0 : Fin m → ℝ := (fun _ => 0) with hda0
  have hHj : ∀ (j : ℕ) (hj : j < m), H j = hc ⟨j, hj⟩ :=
    fun j hj => dite_eq_left hj
  have hXj : ∀ (j : ℕ) (hj : j < m), X j = xc ⟨j, hj⟩ :=
    fun j hj => dite_eq_left hj
  have hstep : ∀ j : ℕ, j < m →
      (OrderedDotProductError.extend m
        (OrderedDotProductError.productPerturbed m h dh0 x dx0 dp0)) j
        + (OrderedDotProductError.extend m da0) j
        = A (j + 1) - A j := by
    intro j hj
    have e1 : (OrderedDotProductError.extend m
          (OrderedDotProductError.productPerturbed m h dh0 x dx0 dp0)) j
        = OrderedDotProductError.productPerturbed m h dh0 x dx0 dp0 ⟨j, hj⟩ :=
      dite_eq_left hj
    have e2 : (OrderedDotProductError.extend m da0) j = da0 ⟨j, hj⟩ :=
      dite_eq_left hj
    rw [e1, e2]
    have hdec := firFold_succ_decode s kmin kmax H X m hno' j hj
    rw [hHj j hj, hXj j hj] at hdec
    have pda : da0 ⟨j, hj⟩ = 0 := rfl
    have pdh : dh0 ⟨j, hj⟩ = decode s (hc ⟨j, hj⟩) - h ⟨j, hj⟩ := rfl
    have pdx : dx0 ⟨j, hj⟩ = decode s (xc ⟨j, hj⟩) - x ⟨j, hj⟩ := rfl
    have pdp : dp0 ⟨j, hj⟩
        = decode s (roundHalfUpShift s (hc ⟨j, hj⟩ * xc ⟨j, hj⟩))
          - decode s (hc ⟨j, hj⟩) * decode s (xc ⟨j, hj⟩) := rfl
    have ppp : OrderedDotProductError.productPerturbed m h dh0 x dx0 dp0 ⟨j, hj⟩
        = (h ⟨j, hj⟩ + dh0 ⟨j, hj⟩) * (x ⟨j, hj⟩ + dx0 ⟨j, hj⟩)
          + dp0 ⟨j, hj⟩ := rfl
    rw [ppp, pdh, pdx, pdp, pda]
    have hA1 : A (j + 1)
        = decode s (firFold s kmin kmax H X (j + 1)).1 := rfl
    have hA2 : A j = decode s (firFold s kmin kmax H X j).1 := rfl
    rw [hA1, hA2, hdec]
    have c1 : h ⟨j, hj⟩ + (decode s (hc ⟨j, hj⟩) - h ⟨j, hj⟩)
        = decode s (hc ⟨j, hj⟩) := add_sub_cancel _ _
    have c2 : x ⟨j, hj⟩ + (decode s (xc ⟨j, hj⟩) - x ⟨j, hj⟩)
        = decode s (xc ⟨j, hj⟩) := add_sub_cancel _ _
    rw [c1, c2]
    linarith
  have htele := accumulator_telescope
    (OrderedDotProductError.extend m
      (OrderedDotProductError.productPerturbed m h dh0 x dx0 dp0))
    (OrderedDotProductError.extend m da0) A m hstep m le_rfl
  change decode s (firFold s kmin kmax H X m).1
    = OrderedDotProductError.accumulator _ _ m
  rw [htele]
  have hAm : A m = decode s (firFold s kmin kmax H X m).1 := rfl
  have hA0 : A 0 = 0 := decode_firFold_zero s kmin kmax H X
  rw [hAm, hA0, sub_zero]

/-- Headline bound: the decoded fixed-point output satisfies the
ordered dot-product bound with the coefficient, input and product errors
at half a step and no accumulation error, since a clean trace adds
exactly. The bound holds for any integer codes `hc` and `xc`: the
hypotheses do not ask them to be signed `w`-bit codes, so a caller
certifying a signed `w`-bit filter must check that each code lies
between `SaturatingRoundHalfUp.signedMinCode w` and
`SaturatingRoundHalfUp.signedMaxCode w`. -/
theorem fixed_point_fir_error_bound (s w m : ℕ) (hw : 1 ≤ w)
    (h x : Fin m → ℝ) (hc xc : Fin m → ℤ)
    (hdx : ∀ k : Fin m, |decode s (xc k) - x k| ≤ (1 : ℝ) / (2 * (2 : ℝ) ^ s))
    (hdh : ∀ k : Fin m, |decode s (hc k) - h k| ≤ (1 : ℝ) / (2 * (2 : ℝ) ^ s))
    (hno : firOverflow s (SaturatingRoundHalfUp.signedMinCode w)
      (SaturatingRoundHalfUp.signedMaxCode w) hc xc = false) :
    |decode s (firCode s (SaturatingRoundHalfUp.signedMinCode w)
        (SaturatingRoundHalfUp.signedMaxCode w) hc xc)
        - OrderedDotProductError.outputIdeal m h x|
      ≤ ((1 : ℝ) / (2 * (2 : ℝ) ^ s)) * (∑ k : Fin m, |h k|)
        + ((1 : ℝ) / (2 * (2 : ℝ) ^ s)) * (∑ k : Fin m, |x k|)
        + (m : ℝ) * ((1 : ℝ) / (2 * (2 : ℝ) ^ s)) * ((1 : ℝ) / (2 * (2 : ℝ) ^ s))
        + (m : ℝ) * ((1 : ℝ) / (2 * (2 : ℝ) ^ s)) := by
  set δ : ℝ := (1 : ℝ) / (2 * (2 : ℝ) ^ s) with hδdef
  set dh0 : Fin m → ℝ := (fun k => decode s (hc k) - h k) with hdh0
  set dx0 : Fin m → ℝ := (fun k => decode s (xc k) - x k) with hdx0
  set dp0 : Fin m → ℝ := (fun k => decode s (roundHalfUpShift s (hc k * xc k))
    - decode s (hc k) * decode s (xc k)) with hdp0
  set da0 : Fin m → ℝ := (fun _ => 0) with hda0
  have heq : decode s (firCode s (SaturatingRoundHalfUp.signedMinCode w)
        (SaturatingRoundHalfUp.signedMaxCode w) hc xc)
      = OrderedDotProductError.outputPerturbed m h dh0 x dx0 dp0 da0 :=
    decode_fir_eq_outputPerturbed_of_no_overflow s w hw h x hc xc hno
  have hpow : (0 : ℝ) < (2 : ℝ) ^ s := pow_pos (by norm_num) s
  have hδ : (0 : ℝ) ≤ δ := by
    change (0 : ℝ) ≤ (1 : ℝ) / (2 * (2 : ℝ) ^ s)
    exact div_nonneg zero_le_one (mul_nonneg (by norm_num) (le_of_lt hpow))
  have hdx' : ∀ k : Fin m, |dx0 k| ≤ δ := fun k => hdx k
  have hdh' : ∀ k : Fin m, |dh0 k| ≤ δ := fun k => hdh k
  have hda' : ∀ k : Fin m, |da0 k| ≤ 0 := by
    intro k
    have h0 : da0 k = 0 := rfl
    rw [h0, abs_zero]
  have hdp' : ∀ k : Fin m, |dp0 k| ≤ δ := by
    intro k
    have hround := roundHalfUpShift_error_le s (hc k * xc k)
    have hcast : ((hc k * xc k : ℤ) : ℝ) = (hc k : ℝ) * (xc k : ℝ) := by
      push_cast
      ring
    have h2 : |(roundHalfUpShift s (hc k * xc k) : ℝ)
        - (hc k : ℝ) * (xc k : ℝ) / (2 : ℝ) ^ s| ≤ 1 / 2 := by
      have h := hround
      rw [hcast] at h
      exact h
    have pdp : dp0 k = decode s (roundHalfUpShift s (hc k * xc k))
        - decode s (hc k) * decode s (xc k) := rfl
    rw [pdp]
    unfold decode
    have e : (roundHalfUpShift s (hc k * xc k) : ℝ) / (2 : ℝ) ^ s
        - (hc k : ℝ) / (2 : ℝ) ^ s * ((xc k : ℝ) / (2 : ℝ) ^ s)
        = ((roundHalfUpShift s (hc k * xc k) : ℝ)
          - (hc k : ℝ) * (xc k : ℝ) / (2 : ℝ) ^ s) / (2 : ℝ) ^ s := by
      rw [div_mul_div_comm, sub_div, div_div]
    rw [e, abs_div, abs_of_pos hpow, div_le_iff₀ hpow]
    have hδeq : δ = (1 : ℝ) / 2 / (2 : ℝ) ^ s := by
      change (1 : ℝ) / (2 * (2 : ℝ) ^ s) = (1 : ℝ) / 2 / (2 : ℝ) ^ s
      rw [div_div]
    have hcc : δ * (2 : ℝ) ^ s = 1 / 2 := by
      rw [hδeq, div_mul_cancel₀ _ hpow.ne']
    rw [hcc]
    exact h2
  rw [heq]
  have hb := OrderedDotProductError.orderedDotProduct_error_bound m h dh0 x dx0 dp0 da0
    δ δ δ 0 hδ hδ hδ le_rfl hdx' hdh' hdp' hda'
  rw [mul_zero, add_zero] at hb
  exact hb

end CSLibExt.Algorithms.Numerical.FixedPointFIR
