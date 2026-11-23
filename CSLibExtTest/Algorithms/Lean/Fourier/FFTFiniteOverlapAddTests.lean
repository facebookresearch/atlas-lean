/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.FiniteOverlapAdd

@[expose] public section

set_option autoImplicit false

open CSLibExt.Algorithms.Lean.Fourier.FFT.SupportBoundedPadding
open CSLibExt.Algorithms.Lean.Fourier.FFT.FiniteOverlapAdd

/-! The signal `[1, 2, 3, 5, 7]` at hop `L = 2` has the unequal nonzero blocks
`[1, 2]` and `[3, 5]` and the zero-padded final block `[7, 0]`. With the kernel
`[2, 1]` the linear convolution is `[2, 5, 8, 13, 19, 7]`, whose tail
coefficient `7` sits at index `N + M - 2 = 5`. -/

/-- Five samples at hop two make three blocks. -/
example : blockCount 5 2 = 3 := by decide

/-- The final block is zero padded. -/
example : block 5 2 ![1, 2, 3, 5, 7] 2 = ![7, 0] := by
  funext i
  fin_cases i <;> simp [block, extendNat]

/-- The linear convolution at its first index. -/
example : linearConvolution 5 2 ![1, 2, 3, 5, 7] ![2, 1] 0 = 2 := by
  norm_num [linearConvolution, extendNat]

/-- The tail coefficient of the linear convolution. -/
example : linearConvolution 5 2 ![1, 2, 3, 5, 7] ![2, 1] 5 = 7 := by
  norm_num [linearConvolution, extendNat, Finset.sum_range_succ]

/-! FFT size `Q = L + M - 1 = 3`, evaluated frame by frame. -/

/-- The first output sample comes from the first frame alone. -/
example : overlapAdd 3 5 2 2 ![1, 2, 3, 5, 7] ![2, 1] 0 = 2 := by
  have hs : ∀ F : ZMod 3 → ℂ, ∑ j, F j = F 0 + F 1 + F 2 := fun F => Fin.sum_univ_three F
  have h1 : (1 : ZMod 3).val = 1 := rfl
  have h2 : (2 : ZMod 3).val = 2 := rfl
  norm_num [overlapAdd, blockCount, blockFrame, cyclicConvolution, zeroExtend, block, extendNat,
    Finset.sum_range_succ, hs, h1, h2]

/-- An interior sample adds two overlapping frames. -/
example : overlapAdd 3 5 2 2 ![1, 2, 3, 5, 7] ![2, 1] 3 = 13 := by
  have hs : ∀ F : ZMod 3 → ℂ, ∑ j, F j = F 0 + F 1 + F 2 := fun F => Fin.sum_univ_three F
  have h1 : (1 : ZMod 3).val = 1 := rfl
  have h2 : (2 : ZMod 3).val = 2 := rfl
  norm_num [overlapAdd, blockCount, blockFrame, cyclicConvolution, zeroExtend, block, extendNat,
    Finset.sum_range_succ, hs, h1, h2]

/-- The tail sample comes from the zero-padded final frame. -/
example : overlapAdd 3 5 2 2 ![1, 2, 3, 5, 7] ![2, 1] 5 = 7 := by
  have hs : ∀ F : ZMod 3 → ℂ, ∑ j, F j = F 0 + F 1 + F 2 := fun F => Fin.sum_univ_three F
  have h1 : (1 : ZMod 3).val = 1 := rfl
  have h2 : (2 : ZMod 3).val = 2 := rfl
  norm_num [overlapAdd, blockCount, blockFrame, cyclicConvolution, zeroExtend, block, extendNat,
    Finset.sum_range_succ, hs, h1, h2]

/-- Past the tail the output vanishes. -/
example : overlapAdd 3 5 2 2 ![1, 2, 3, 5, 7] ![2, 1] 6 = 0 := by
  have hs : ∀ F : ZMod 3 → ℂ, ∑ j, F j = F 0 + F 1 + F 2 := fun F => Fin.sum_univ_three F
  have h1 : (1 : ZMod 3).val = 1 := rfl
  have h2 : (2 : ZMod 3).val = 2 := rfl
  norm_num [overlapAdd, blockCount, blockFrame, cyclicConvolution, zeroExtend, block, extendNat,
    Finset.sum_range_succ, hs, h1, h2]

/-- The headline theorem at FFT size `3`. -/
example : overlapAdd 3 5 2 2 ![1, 2, 3, 5, 7] ![2, 1] =
    linearConvolution 5 2 ![1, 2, 3, 5, 7] ![2, 1] :=
  overlapAdd_eq_linearConvolution 3 5 2 2 (by norm_num) (by norm_num) (by norm_num) _ _

/-! FFT size `Q = 4 > L + M - 1`: each frame carries one extra zero sample. -/

/-- An interior sample at FFT size `4`. -/
example : overlapAdd 4 5 2 2 ![1, 2, 3, 5, 7] ![2, 1] 1 = 5 := by
  have hs : ∀ F : ZMod 4 → ℂ, ∑ j, F j = F 0 + F 1 + F 2 + F 3 :=
    fun F => Fin.sum_univ_four F
  have h1 : (1 : ZMod 4).val = 1 := rfl
  have h2 : (2 : ZMod 4).val = 2 := rfl
  have h3 : (3 : ZMod 4).val = 3 := rfl
  norm_num [overlapAdd, blockCount, blockFrame, cyclicConvolution, zeroExtend, block, extendNat,
    Finset.sum_range_succ, hs, h1, h2, h3]

/-- The tail sample at FFT size `4`. -/
example : overlapAdd 4 5 2 2 ![1, 2, 3, 5, 7] ![2, 1] 5 = 7 := by
  have hs : ∀ F : ZMod 4 → ℂ, ∑ j, F j = F 0 + F 1 + F 2 + F 3 :=
    fun F => Fin.sum_univ_four F
  have h1 : (1 : ZMod 4).val = 1 := rfl
  have h2 : (2 : ZMod 4).val = 2 := rfl
  have h3 : (3 : ZMod 4).val = 3 := rfl
  norm_num [overlapAdd, blockCount, blockFrame, cyclicConvolution, zeroExtend, block, extendNat,
    Finset.sum_range_succ, hs, h1, h2, h3]

/-- The headline theorem at FFT size `4`, used to read off a tail value. -/
example : overlapAdd 4 5 2 2 ![1, 2, 3, 5, 7] ![2, 1] 5 = 7 := by
  rw [overlapAdd_eq_linearConvolution 4 5 2 2 (by norm_num) (by norm_num) (by norm_num)]
  norm_num [linearConvolution, extendNat, Finset.sum_range_succ]

/-! FFT size `Q = 2 < L + M - 1` with a full first block (`L = 2 ≤ N = 5`):
the first frame wraps its last coefficient onto index `0`. -/

/-- The aliased first sample is `2 + 2 = 4`, not `2`. -/
example : overlapAdd 2 5 2 2 ![1, 2, 3, 5, 7] ![2, 1] 0 = 4 := by
  have hs : ∀ F : ZMod 2 → ℂ, ∑ j, F j = F 0 + F 1 := fun F => Fin.sum_univ_two F
  have h1 : (1 : ZMod 2).val = 1 := rfl
  norm_num [overlapAdd, blockCount, blockFrame, cyclicConvolution, zeroExtend, block, extendNat,
    Finset.sum_range_succ, hs, h1]

/-- So overlap-add at FFT size `2` differs from the linear convolution. -/
example : overlapAdd 2 5 2 2 ![1, 2, 3, 5, 7] ![2, 1] ≠
    linearConvolution 5 2 ![1, 2, 3, 5, 7] ![2, 1] := by
  intro heq
  have h0 := congrFun heq 0
  have hs : ∀ F : ZMod 2 → ℂ, ∑ j, F j = F 0 + F 1 := fun F => Fin.sum_univ_two F
  have h1 : (1 : ZMod 2).val = 1 := rfl
  norm_num [overlapAdd, blockCount, blockFrame, cyclicConvolution, zeroExtend, block, extendNat,
    linearConvolution, Finset.sum_range_succ, hs, h1] at h0

/-- The short-FFT failure theorem in its `L ≤ N` form. -/
example : ∃ x : Fin 5 → ℂ, ∃ h : Fin 2 → ℂ,
    overlapAdd 2 5 2 2 x h ≠ linearConvolution 5 2 x h :=
  overlapAdd_ne_linearConvolution_of_short_fft 2 5 2 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- The circular-aliasing theorem at `Q = L = M = 2`: the last linear
coefficient wraps onto index `L + M - 2 - Q = 0`. -/
example : ∃ x : Fin 5 → ℂ, ∃ h : Fin 2 → ℂ,
    linearConvolution 5 2 x h 2 = 1 ∧ linearConvolution 5 2 x h 0 = 0 ∧
      overlapAdd 2 5 2 2 x h 0 = 1 :=
  overlapAdd_aliases_of_short_fft 2 5 2 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- The circular-aliasing theorem at `Q = L = M = 3`, wrapping index `4`
onto index `1`. -/
example : ∃ x : Fin 3 → ℂ, ∃ h : Fin 3 → ℂ,
    linearConvolution 3 3 x h 4 = 1 ∧ linearConvolution 3 3 x h 1 = 0 ∧
      overlapAdd 3 3 3 3 x h 1 = 1 :=
  overlapAdd_aliases_of_short_fft 3 3 3 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-! FFT size `Q = 1 < L = 2` with `N = L = 2` and `M = 1`: zero extension to
length `1` discards the block sample at offset `1`, so the output is wrong by
truncation, with nothing wrapped. -/

/-- The discarded sample `1` never reaches the output at index `1`. -/
example : overlapAdd 1 2 2 1 ![0, 1] ![1] 1 = 0 := by
  norm_num [overlapAdd, blockCount, blockFrame]

/-- The linear convolution keeps it. -/
example : linearConvolution 2 1 ![0, 1] ![1] 1 = 1 := by
  norm_num [linearConvolution, extendNat, Finset.sum_range_succ]

/-- The generic short-FFT failure theorem still applies in this regime. -/
example : ∃ x : Fin 2 → ℂ, ∃ h : Fin 1 → ℂ,
    overlapAdd 1 2 2 1 x h ≠ linearConvolution 2 1 x h :=
  overlapAdd_ne_linearConvolution_of_short_fft 1 2 2 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-! Keeping only the first `N = 5` samples drops the tail coefficient `7`. -/

/-- Truncation to the input length differs from the linear convolution. -/
example : (fun n => if n < 5 then overlapAdd 3 5 2 2 ![1, 2, 3, 5, 7] ![2, 1] n else 0) ≠
    linearConvolution 5 2 ![1, 2, 3, 5, 7] ![2, 1] := by
  intro heq
  have h5 := congrFun heq 5
  norm_num [linearConvolution, extendNat, Finset.sum_range_succ] at h5

/-- The dropped-tail failure theorem in its `M ≥ 2` form. -/
example : ∃ x : Fin 5 → ℂ, ∃ h : Fin 2 → ℂ,
    (fun n => if n < 5 then overlapAdd 3 5 2 2 x h n else 0) ≠ linearConvolution 5 2 x h :=
  truncation_to_input_length_fails 3 5 2 2 (by norm_num) (by norm_num)
