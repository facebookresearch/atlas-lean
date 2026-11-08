/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.Correctness
public import MathlibExt.Analysis.Fourier.FastFourierTransform
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Init.Data.Array.Lemmas

/-!
# The actual radix-two executor returns every DFT coefficient

The proof reuses the existing Complex Cooley–Tukey identity. Its input samples
are the actual Vector entries, extended by zero through canonical Array.getD.
Primitive roots justify the squared child root and the high-half minus sign.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

open MathlibExt.Analysis.Fourier.FastFourierTransformWanted

private theorem fftSample_eq {n : Nat} (xs : Vector ℂ n) (j : Nat) (hj : j < n) :
    xs.toArray.getD j 0 = xs[j] := by
  exact (Array.getElem_eq_getD (h := by simpa using hj) 0).symm

private theorem fftSplit_dft_even (d : Nat) (root : ℂ)
    (xs : Vector ℂ (2 ^ (d + 1))) (k : Nat) :
    dftSum (2 ^ d) root (fun j => (fftSplit xs).ret.1.toArray.getD j 0) k =
      dftSum (2 ^ d) root (fun j => xs.toArray.getD (2 * j) 0) k := by
  unfold dftSum
  apply Finset.sum_congr rfl
  intro j hj
  have h : j < 2 ^ d := Finset.mem_range.mp hj
  have hxs : 2 * j < 2 ^ (d + 1) := by
    simp only [pow_succ]
    omega
  dsimp only
  apply congrArg (fun z : ℂ => root ^ (j * k) * z)
  calc
    _ = (fftSplit xs).ret.1[j] := fftSample_eq _ j h
    _ = xs[2 * j] := fftSplit_ret_even xs ⟨j, h⟩
    _ = _ := (fftSample_eq xs (2 * j) hxs).symm

private theorem fftSplit_dft_odd (d : Nat) (root : ℂ)
    (xs : Vector ℂ (2 ^ (d + 1))) (k : Nat) :
    dftSum (2 ^ d) root (fun j => (fftSplit xs).ret.2.toArray.getD j 0) k =
      dftSum (2 ^ d) root (fun j => xs.toArray.getD (2 * j + 1) 0) k := by
  unfold dftSum
  apply Finset.sum_congr rfl
  intro j hj
  have h : j < 2 ^ d := Finset.mem_range.mp hj
  have hxs : 2 * j + 1 < 2 ^ (d + 1) := by
    simp only [pow_succ]
    omega
  dsimp only
  apply congrArg (fun z : ℂ => root ^ (j * k) * z)
  calc
    _ = (fftSplit xs).ret.2[j] := fftSample_eq _ j h
    _ = xs[2 * j + 1] := fftSplit_ret_odd xs ⟨j, h⟩
    _ = _ := (fftSample_eq xs (2 * j + 1) hxs).symm

/-- Every coefficient of the actual executed FFT is the complete source DFT sum. -/
theorem fft_correct (d : Nat) (omega : ℂ) (hroot : IsPrimitiveRoot omega (2 ^ d))
    (xs : Vector ℂ (2 ^ d)) (k : Fin (2 ^ d)) :
    (fft d omega xs).ret[k.val] =
      dftSum (2 ^ d) omega (fun j => xs.toArray.getD j 0) k.val := by
  induction d generalizing omega with
  | zero =>
      rw [fft_ret_zero]
      simp [dftSum]
  | succ d ih =>
      have hsquare : IsPrimitiveRoot (omega * omega) (2 ^ d) := by
        have hsq : IsPrimitiveRoot (omega ^ 2) (2 ^ d) :=
          IsPrimitiveRoot.pow (pow_pos (by decide) _) hroot
            (by rw [pow_succ, Nat.mul_comm])
        simpa only [pow_two] using hsq
      have hpow : omega ^ (2 * 2 ^ d) = 1 := by
        simpa only [pow_succ, Nat.mul_comm] using hroot.pow_eq_one
      have hhalf : omega ^ (2 ^ d) = -1 := by
        have h : IsPrimitiveRoot (omega ^ (2 ^ d)) 2 :=
          IsPrimitiveRoot.pow (pow_pos (by decide) _) hroot (pow_succ 2 d)
        exact IsPrimitiveRoot.eq_neg_one_of_two_right h
      have he (i : Fin (2 ^ d)) :
          (fft d (omega * omega) (fftSplit xs).ret.1).ret[i.val] =
            dftSum (2 ^ d) (omega * omega) (fun j => xs.toArray.getD (2 * j) 0) i.val := by
        calc
          _ = dftSum (2 ^ d) (omega * omega)
                (fun j => (fftSplit xs).ret.1.toArray.getD j 0) i.val :=
            ih (omega * omega) hsquare (fftSplit xs).ret.1 i
          _ = _ := fftSplit_dft_even d (omega * omega) xs i.val
      have ho (i : Fin (2 ^ d)) :
          (fft d (omega * omega) (fftSplit xs).ret.2).ret[i.val] =
            dftSum (2 ^ d) (omega * omega) (fun j => xs.toArray.getD (2 * j + 1) 0) i.val := by
        calc
          _ = dftSum (2 ^ d) (omega * omega)
                (fun j => (fftSplit xs).ret.2.toArray.getD j 0) i.val :=
            ih (omega * omega) hsquare (fftSplit xs).ret.2 i
          _ = _ := fftSplit_dft_odd d (omega * omega) xs i.val
      by_cases hk : k.val < 2 ^ d
      · let i : Fin (2 ^ d) := ⟨k.val, hk⟩
        have hct := cooley_tukey (2 ^ d) omega hpow (fun j => xs.toArray.getD j 0) k.val
        rw [Nat.mul_comm 2 (2 ^ d)] at hct
        simp only [pow_two, Nat.mod_eq_of_lt hk] at hct
        rw [fft_ret_succ_low d omega xs i, he i, ho i]
        exact hct.symm
      · have hi : k.val - 2 ^ d < 2 ^ d := by
          have h := k.isLt
          simp only [pow_succ] at h
          omega
        let i : Fin (2 ^ d) := ⟨k.val - 2 ^ d, hi⟩
        have hki : k.val = i.val + 2 ^ d := by dsimp [i]; omega
        have hmod : (i.val + 2 ^ d) % (2 ^ d) = i.val := by
          simp [Nat.mod_eq_of_lt i.isLt]
        have hct := cooley_tukey (2 ^ d) omega hpow
          (fun j => xs.toArray.getD j 0) (i.val + 2 ^ d)
        rw [Nat.mul_comm 2 (2 ^ d)] at hct
        simp only [pow_two, hmod, pow_add, hhalf, mul_neg_one, neg_mul] at hct
        have hret := fft_ret_succ_high d omega xs i
        simp only [he i, ho i, sub_eq_add_neg] at hret
        simpa only [hki, pow_succ] using hret.trans hct.symm

end Cslib.Algorithms.Lean.TimeM
