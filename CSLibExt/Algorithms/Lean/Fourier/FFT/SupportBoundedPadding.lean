/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.BigOperators
public import MathlibExt.Analysis.Fourier.RectangularDFTAdapter
public import MathlibExt.Analysis.Fourier.ZModConvolution

/-!
# Support-bounded zero padding for cyclic convolution

For finitely supported one-dimensional signals of lengths `M, K >= 1`,
zero padding to any length `N >= M + K - 1` makes the cropped cyclic
convolution equal the full linear convolution. The same statement holds
coordinatewise for rectangular two-dimensional supports: a first array
supported on an `M x K` rectangle and a second on a `P x Q` rectangle,
zero padded to `N1 >= M + P - 1` and `N2 >= K + Q - 1`, have cropped
two-dimensional cyclic convolution equal to their full two-dimensional
linear convolution. No dyadic length is assumed for the inputs; the
dyadic padding route is a special case. One slot too short aliases the
last linear coefficient onto an earlier cropped coefficient.

The zero-extension maps are total in their lengths. For nonzero cyclic
lengths and nonempty supports they are faithful extensions exactly when
the cyclic length covers the support (`zeroExtend_injective_iff`,
`zeroExtend2_injective_iff`); a shorter nonzero cyclic length keeps only
the leading entries. Cyclic length zero is degenerate: `ZMod 0` is `ℤ`
and `ZMod.val` is the absolute value there, so every source entry is read
back at its natural index and the map is injective whatever the support
length. Every convolution and transform result assumes nonzero cyclic
lengths, and every result that uses the extension property carries
length bounds that imply coverage.
-/

@[expose] public section

set_option autoImplicit false

namespace CSLibExt.Algorithms.Lean.Fourier.FFT.SupportBoundedPadding

open MathlibExt.Analysis.Fourier.RectangularDFTAdapter

/-- Zero extension of a finite signal to natural indices. -/
def extendNat (M : ℕ) (x : Fin M → ℂ) : ℕ → ℂ :=
  fun i => if h : i < M then x ⟨i, h⟩ else 0

/-- Zero extension of a finite signal to a cyclic index type: the cyclic
index `i` reads source entry `i.val` when it lies below `M` and zero
otherwise. When `M ≤ N` this is a faithful extension
(`zeroExtend_natCast`, `zeroExtend_injective`). For nonzero `N` the
converse holds (`zeroExtend_injective_iff`): when `0 < N < M` it keeps
only the first `N` source entries. At `N = 0`, where `ZMod 0` is `ℤ`,
every source entry is read back at its natural index and the map is
injective for every `M`. -/
def zeroExtend (M N : ℕ) (x : Fin M → ℂ) : ZMod N → ℂ :=
  fun i => extendNat M x i.val

/-- Full linear convolution of two finitely supported signals. -/
def linearConvolution (M K : ℕ) (x : Fin M → ℂ) (y : Fin K → ℂ) : ℕ → ℂ :=
  fun t => ∑ j ∈ Finset.range (t + 1), extendNat M x j * extendNat K y (t - j)

/-- Cyclic convolution on a nonzero cyclic length. -/
def cyclicConvolution (N : ℕ) [NeZero N] (a b : ZMod N → ℂ) : ZMod N → ℂ :=
  fun t => ∑ j : ZMod N, a j * b (t - j)

/-- Zero extension vanishes at and beyond the support length. -/
theorem extendNat_eq_zero_of_le (M : ℕ) (x : Fin M → ℂ) (i : ℕ) (hi : M ≤ i) :
    extendNat M x i = 0 := by
  simp [extendNat, Nat.not_lt.mpr hi]

/-- Zero extension agrees with the signal inside its support. -/
theorem zeroExtend_apply_of_lt (M N : ℕ) (x : Fin M → ℂ) (i : ZMod N)
    (hi : i.val < M) : zeroExtend M N x i = x ⟨i.val, hi⟩ := by
  simp [zeroExtend, extendNat, hi]

/-- When the cyclic length covers the support, zero extension preserves
every source entry. -/
theorem zeroExtend_natCast (M N : ℕ) (hMN : M ≤ N) (x : Fin M → ℂ) (i : Fin M) :
    zeroExtend M N x (i.val : ZMod N) = x i := by
  have hiN : i.val < N := lt_of_lt_of_le i.isLt hMN
  simp [zeroExtend, extendNat, ZMod.val_natCast_of_lt hiN]

/-- When the cyclic length covers the support, zero extension loses no
information. -/
theorem zeroExtend_injective (M N : ℕ) (hMN : M ≤ N) :
    Function.Injective (zeroExtend M N) := by
  intro x x' h
  funext i
  rw [← zeroExtend_natCast M N hMN x i, ← zeroExtend_natCast M N hMN x' i, h]

/-- For a nonzero cyclic length, zero extension is injective exactly
when the cyclic length covers the support. A shorter length identifies
signals that differ only at source index `N`. -/
theorem zeroExtend_injective_iff (M N : ℕ) [NeZero N] :
    Function.Injective (zeroExtend M N) ↔ M ≤ N := by
  refine ⟨fun hinj => ?_, zeroExtend_injective M N⟩
  by_contra hcon
  have hNM : N < M := by omega
  have h : (fun i : Fin M => if i.val = N then (1 : ℂ) else 0) = fun _ => 0 :=
    hinj (by
      funext i
      have hi : i.val ≠ N := (ZMod.val_lt i).ne
      simp [zeroExtend, extendNat, hi])
  have h1 := congrFun h ⟨N, hNM⟩
  simp at h1

private theorem sum_zmod_eq_sum_range (N : ℕ) [NeZero N] (F : ZMod N → ℂ) :
    ∑ j : ZMod N, F j = ∑ n ∈ Finset.range N, F (n : ZMod N) := by
  let e : Fin N ≃ ZMod N :=
    { toFun := fun i => (i.val : ZMod N)
      invFun := fun j => ⟨j.val, ZMod.val_lt j⟩
      left_inv := fun i => by
        simp [ZMod.val_natCast_of_lt i.isLt]
      right_inv := fun j => by
        simp }
  have h1 : ∑ j : ZMod N, F j = ∑ i : Fin N, F (e i) := (e.sum_comp F).symm
  rw [h1]
  have hfun : (fun i : Fin N => F (e i)) = (fun i : Fin N => F ((i.val : ℕ) : ZMod N)) := rfl
  rw [hfun]
  exact Fin.sum_univ_eq_sum_range (fun n => F (n : ZMod N)) N

private theorem sub_val_eq_of_le (N t n : ℕ) [NeZero N] (htN : t < N) (hnN : n < N) (hle : n ≤ t) :
    ((t : ZMod N) - (n : ZMod N)).val = t - n := by
  have ht : ((t : ZMod N).val) = t := ZMod.val_natCast_of_lt htN
  have hn : ((n : ZMod N).val) = n := ZMod.val_natCast_of_lt hnN
  have hle' : (n : ZMod N).val ≤ (t : ZMod N).val := by rw [hn, ht]; exact hle
  have h := ZMod.val_sub hle'
  rw [ht, hn] at h
  exact h

private theorem le_of_sub_val_of_lt (M K N t n : ℕ) [NeZero N]
    (_hM : 1 ≤ M) (_hK : 1 ≤ K) (hN : M + K - 1 ≤ N)
    (ht : t < M + K - 1) (_hnN : n < N) (hnM : n < M) (hlt : t < n) :
    K ≤ ((t : ZMod N) - (n : ZMod N)).val := by
  by_contra hcon
  have hcon_lt : ((t : ZMod N) - (n : ZMod N)).val < K := by omega
  have htN : t < N := lt_of_lt_of_le ht hN
  have hwnN : ((t : ZMod N) - (n : ZMod N)).val + n < N := by omega
  have hwcast : ((((t : ZMod N) - (n : ZMod N)).val : ℕ) : ZMod N)
      = (t : ZMod N) - (n : ZMod N) :=
    ZMod.natCast_zmod_val _
  have ht_eq : (t : ZMod N)
      = ((((t : ZMod N) - (n : ZMod N)).val + n : ℕ) : ZMod N) := by
    have h1 : ((((t : ZMod N) - (n : ZMod N)).val : ℕ) : ZMod N) + (n : ZMod N)
        = (t : ZMod N) := by
      rw [hwcast]
      exact sub_add_cancel _ _
    have h2 : ((((t : ZMod N) - (n : ZMod N)).val + n : ℕ) : ZMod N)
        = ((((t : ZMod N) - (n : ZMod N)).val : ℕ) : ZMod N) + (n : ZMod N) := by
      simp [Nat.cast_add]
    rw [h2]
    exact h1.symm
  have hval := congrArg ZMod.val ht_eq
  rw [ZMod.val_natCast_of_lt htN, ZMod.val_natCast_of_lt hwnN] at hval
  omega

/-- The zero-extended cyclic convolution is the inverse transform of
the pointwise product of the two transforms. -/
theorem cyclicConvolution_eq_invDFT_mul (M K N : ℕ) [NeZero N]
    (x : Fin M → ℂ) (y : Fin K → ℂ) :
    cyclicConvolution N (zeroExtend M N x) (zeroExtend K N y) =
      ZMod.dft.symm (fun k => ZMod.dft (zeroExtend M N x) k *
        ZMod.dft (zeroExtend K N y) k) := by
  ext t
  simp only [cyclicConvolution]
  exact (ZMod.invDFT_mul_dft _ _ t).symm

/-- Headline one-dimensional result: padding to at least the support
sum minus one makes every cropped cyclic coefficient below the linear
length equal the full linear coefficient. -/
theorem padded_cyclic_eq_linear (M K N : ℕ) [NeZero N] (hM : 1 ≤ M) (hK : 1 ≤ K)
    (hN : M + K - 1 ≤ N) (x : Fin M → ℂ) (y : Fin K → ℂ) (t : ℕ)
    (ht : t < M + K - 1) :
    cyclicConvolution N (zeroExtend M N x) (zeroExtend K N y) (t : ZMod N) =
      linearConvolution M K x y t := by
  have htN : t < N := lt_of_lt_of_le ht hN
  have ht1N : t + 1 ≤ N := by omega
  simp only [cyclicConvolution, linearConvolution]
  rw [sum_zmod_eq_sum_range N
    (fun j => zeroExtend M N x j * zeroExtend K N y ((t : ZMod N) - j))]
  have hrewrite : ∀ n ∈ Finset.range N,
      zeroExtend M N x (n : ZMod N) * zeroExtend K N y ((t : ZMod N) - (n : ZMod N))
        = extendNat M x n * extendNat K y (((t : ZMod N) - (n : ZMod N)).val) := by
    intro n hn
    rw [Finset.mem_range] at hn
    simp only [zeroExtend, ZMod.val_natCast_of_lt hn]
  have hsum_eq : (∑ n ∈ Finset.range N,
        zeroExtend M N x (n : ZMod N) * zeroExtend K N y ((t : ZMod N) - (n : ZMod N)))
      = (∑ n ∈ Finset.range N,
        extendNat M x n * extendNat K y (((t : ZMod N) - (n : ZMod N)).val)) :=
    Finset.sum_congr rfl hrewrite
  rw [hsum_eq]
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun n => extendNat M x n * extendNat K y (((t : ZMod N) - (n : ZMod N)).val))
    ht1N
  have hIco_zero : (∑ n ∈ Finset.Ico (t + 1) N,
      extendNat M x n * extendNat K y (((t : ZMod N) - (n : ZMod N)).val)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [Finset.mem_Ico] at hn
    obtain ⟨hle, hltN⟩ := hn
    have hlt : t < n := by omega
    by_cases hMn : M ≤ n
    · have h0 : extendNat M x n = 0 := extendNat_eq_zero_of_le M x n hMn
      simp [h0]
    · have hnM : n < M := by omega
      have hKle : K ≤ ((t : ZMod N) - (n : ZMod N)).val :=
        le_of_sub_val_of_lt M K N t n hM hK hN ht hltN hnM hlt
      have h0 : extendNat K y (((t : ZMod N) - (n : ZMod N)).val) = 0 :=
        extendNat_eq_zero_of_le K y _ hKle
      simp [h0]
  have hrange_eq : (∑ n ∈ Finset.range (t + 1),
        extendNat M x n * extendNat K y (((t : ZMod N) - (n : ZMod N)).val))
      = (∑ n ∈ Finset.range (t + 1), extendNat M x n * extendNat K y (t - n)) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_range] at hn
    have hle : n ≤ t := by omega
    have hnN : n < N := lt_of_le_of_lt hle htN
    have hval : (((t : ZMod N) - (n : ZMod N)).val) = t - n :=
      sub_val_eq_of_le N t n htN hnN hle
    rw [hval]
  calc (∑ n ∈ Finset.range N,
        extendNat M x n * extendNat K y (((t : ZMod N) - (n : ZMod N)).val))
      = (∑ n ∈ Finset.range (t + 1),
          extendNat M x n * extendNat K y (((t : ZMod N) - (n : ZMod N)).val))
          + (∑ n ∈ Finset.Ico (t + 1) N,
          extendNat M x n * extendNat K y (((t : ZMod N) - (n : ZMod N)).val)) := by
        rw [hsplit]
    _ = (∑ n ∈ Finset.range (t + 1),
          extendNat M x n * extendNat K y (((t : ZMod N) - (n : ZMod N)).val)) + 0 := by
        rw [hIco_zero]
    _ = (∑ n ∈ Finset.range (t + 1),
          extendNat M x n * extendNat K y (((t : ZMod N) - (n : ZMod N)).val)) := by
        rw [add_zero]
    _ = (∑ n ∈ Finset.range (t + 1), extendNat M x n * extendNat K y (t - n)) :=
        hrange_eq

/-- Dyadic special case of the headline result, matching the stored
dyadic padding length: equal dyadic supports padded to twice the
length satisfy the cropped identity. -/
theorem padded_cyclic_eq_linear_dyadic (d : ℕ) (x y : Fin (2 ^ d) → ℂ) (t : ℕ)
    (ht : t < 2 ^ d + 2 ^ d - 1) :
    cyclicConvolution (2 ^ (d + 1)) (zeroExtend (2 ^ d) (2 ^ (d + 1)) x)
        (zeroExtend (2 ^ d) (2 ^ (d + 1)) y) (t : ZMod (2 ^ (d + 1))) =
      linearConvolution (2 ^ d) (2 ^ d) x y t := by
  have hM : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  have hpow : 2 ^ (d + 1) = 2 ^ d * 2 := pow_succ 2 d
  have hN : 2 ^ d + 2 ^ d - 1 ≤ 2 ^ (d + 1) := by omega
  have hNe : NeZero (2 ^ (d + 1)) := ⟨by positivity⟩
  exact padded_cyclic_eq_linear _ _ _ hM hM hN x y t ht

private theorem alias_sub_eq (M K : ℕ) [NeZero (M + K - 2)] (hM : 2 ≤ M) (hK : 2 ≤ K) :
    (0 : ZMod (M + K - 2)) - ((M - 1 : ℕ) : ZMod (M + K - 2))
      = ((K - 1 : ℕ) : ZMod (M + K - 2)) := by
  have hadd : ((M - 1 : ℕ) : ZMod (M + K - 2)) + ((K - 1 : ℕ) : ZMod (M + K - 2)) = 0 := by
    have hcast : ((M - 1 : ℕ) : ZMod (M + K - 2)) + ((K - 1 : ℕ) : ZMod (M + K - 2))
        = (((M - 1 + (K - 1) : ℕ)) : ZMod (M + K - 2)) := by
      simp [Nat.cast_add]
    have hsum : M - 1 + (K - 1) = M + K - 2 := by omega
    rw [hcast, hsum]
    exact ZMod.natCast_self _
  have hba : ((K - 1 : ℕ) : ZMod (M + K - 2)) + ((M - 1 : ℕ) : ZMod (M + K - 2)) = 0 := by
    have hcomm := add_comm (((K - 1 : ℕ)) : ZMod (M + K - 2)) (((M - 1 : ℕ)) : ZMod (M + K - 2))
    rw [hcomm]
    exact hadd
  have hb : ((K - 1 : ℕ) : ZMod (M + K - 2))
      = -(((M - 1 : ℕ) : ZMod (M + K - 2))) :=
    eq_neg_of_add_eq_zero_left hba
  have h0sub : (0 : ZMod (M + K - 2)) - ((M - 1 : ℕ) : ZMod (M + K - 2))
      = -(((M - 1 : ℕ) : ZMod (M + K - 2))) := by
    simp [zero_sub]
  rw [h0sub]
  exact hb.symm

/-- One slot too short aliases: for supports of length at least two,
at the length `M + K - 2` there are signals whose cyclic coefficient
at the cropped origin differs from the linear coefficient there. -/
theorem one_short_padding_aliases (M K : ℕ) [NeZero (M + K - 2)] (hM : 2 ≤ M) (hK : 2 ≤ K) :
    ∃ x : Fin M → ℂ, ∃ y : Fin K → ℂ,
      cyclicConvolution (M + K - 2)
          (zeroExtend M (M + K - 2) x) (zeroExtend K (M + K - 2) y)
          (0 : ZMod (M + K - 2)) ≠ linearConvolution M K x y 0 := by
  refine ⟨fun i => if i.val = M - 1 then 1 else 0,
    fun j => if j.val = K - 1 then 1 else 0, ?_⟩
  have hM1M : M - 1 < M := by omega
  have hK1K : K - 1 < K := by omega
  have hM1N : M - 1 < M + K - 2 := by omega
  have hK1N : K - 1 < M + K - 2 := by omega
  have h0M : (0 : ℕ) < M := by omega
  have h0neM : (0 : ℕ) ≠ M - 1 := by omega
  have hlin : linearConvolution M K
      (fun i => if i.val = M - 1 then (1 : ℂ) else 0)
      (fun j => if j.val = K - 1 then (1 : ℂ) else 0) 0 = 0 := by
    simp only [linearConvolution]
    rw [Finset.sum_range_one]
    simp only [Nat.sub_zero]
    have hext0 : extendNat M (fun i => if i.val = M - 1 then (1 : ℂ) else 0) 0 = 0 := by
      simp [extendNat, h0M, h0neM]
    simp [hext0]
  have hcyc : cyclicConvolution (M + K - 2)
      (zeroExtend M (M + K - 2) (fun i => if i.val = M - 1 then (1 : ℂ) else 0))
      (zeroExtend K (M + K - 2) (fun j => if j.val = K - 1 then (1 : ℂ) else 0))
      (0 : ZMod (M + K - 2)) = 1 := by
    simp only [cyclicConvolution]
    have hsum : (∑ j : ZMod (M + K - 2),
        zeroExtend M (M + K - 2) (fun i => if i.val = M - 1 then (1 : ℂ) else 0) j *
        zeroExtend K (M + K - 2) (fun j => if j.val = K - 1 then (1 : ℂ) else 0)
          ((0 : ZMod (M + K - 2)) - j))
        = zeroExtend M (M + K - 2) (fun i => if i.val = M - 1 then (1 : ℂ) else 0)
            ((M - 1 : ℕ) : ZMod (M + K - 2)) *
          zeroExtend K (M + K - 2) (fun j => if j.val = K - 1 then (1 : ℂ) else 0)
            ((0 : ZMod (M + K - 2)) - ((M - 1 : ℕ) : ZMod (M + K - 2))) := by
      apply Finset.sum_eq_single_of_mem ((M - 1 : ℕ) : ZMod (M + K - 2))
      · exact Finset.mem_univ _
      · intro b _ hb
        have hbval : b.val ≠ M - 1 := by
          intro hcontra
          apply hb
          have hj := ZMod.natCast_zmod_val b
          rw [hcontra] at hj
          exact hj.symm
        have hfirst : zeroExtend M (M + K - 2)
            (fun i => if i.val = M - 1 then (1 : ℂ) else 0) b = 0 := by
          simp only [zeroExtend]
          by_cases hlt : b.val < M
          · simp [extendNat, hlt, hbval]
          · have hle : M ≤ b.val := by omega
            exact extendNat_eq_zero_of_le M _ _ hle
        simp [hfirst]
    rw [hsum]
    have hfirst : zeroExtend M (M + K - 2)
        (fun i => if i.val = M - 1 then (1 : ℂ) else 0)
        ((M - 1 : ℕ) : ZMod (M + K - 2)) = 1 := by
      simp only [zeroExtend, ZMod.val_natCast_of_lt hM1N]
      simp [extendNat, hM1M]
    have hsecond : zeroExtend K (M + K - 2)
        (fun j => if j.val = K - 1 then (1 : ℂ) else 0)
        ((0 : ZMod (M + K - 2)) - ((M - 1 : ℕ) : ZMod (M + K - 2))) = 1 := by
      rw [alias_sub_eq M K hM hK]
      simp only [zeroExtend, ZMod.val_natCast_of_lt hK1N]
      simp [extendNat, hK1K]
    rw [hfirst, hsecond, mul_one]
  rw [hcyc, hlin]
  norm_num

/-- Zero extension of a rectangularly supported array to natural pairs. -/
def extendNat2 (M K : ℕ) (x : Fin M × Fin K → ℂ) : ℕ × ℕ → ℂ :=
  fun p => if h1 : p.1 < M then if h2 : p.2 < K then x (⟨p.1, h1⟩, ⟨p.2, h2⟩) else 0 else 0

/-- Zero extension of a rectangularly supported array to cyclic pairs,
coordinatewise as in `zeroExtend`. When `M ≤ N1` and `K ≤ N2` this is a
faithful extension (`zeroExtend2_natCast`, `zeroExtend2_injective`).
For nonzero lengths and a nonempty support the converse holds
(`zeroExtend2_injective_iff`): a shorter length keeps only the leading
`N1 x N2` block. As in `zeroExtend`, a zero length on either axis reads
that axis back at its natural indices. -/
def zeroExtend2 (M K N1 N2 : ℕ) (x : Fin M × Fin K → ℂ) : ZMod N1 × ZMod N2 → ℂ :=
  fun p => extendNat2 M K x (p.1.val, p.2.val)

/-- When both cyclic lengths cover the rectangular support, zero
extension preserves every source entry. -/
theorem zeroExtend2_natCast (M K N1 N2 : ℕ) (hM : M ≤ N1) (hK : K ≤ N2)
    (x : Fin M × Fin K → ℂ) (i : Fin M) (j : Fin K) :
    zeroExtend2 M K N1 N2 x ((i.val : ZMod N1), (j.val : ZMod N2)) = x (i, j) := by
  have hi : i.val < N1 := lt_of_lt_of_le i.isLt hM
  have hj : j.val < N2 := lt_of_lt_of_le j.isLt hK
  simp [zeroExtend2, extendNat2, ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj]

/-- When both cyclic lengths cover the rectangular support, zero
extension loses no information. -/
theorem zeroExtend2_injective (M K N1 N2 : ℕ) (hM : M ≤ N1) (hK : K ≤ N2) :
    Function.Injective (zeroExtend2 M K N1 N2) := by
  intro x x' h
  funext p
  rw [← zeroExtend2_natCast M K N1 N2 hM hK x p.1 p.2,
    ← zeroExtend2_natCast M K N1 N2 hM hK x' p.1 p.2, h]

/-- For nonzero cyclic lengths and a nonempty rectangular support, zero
extension is injective exactly when both cyclic lengths cover the
support. -/
theorem zeroExtend2_injective_iff (M K N1 N2 : ℕ) [NeZero N1] [NeZero N2]
    (hM : 1 ≤ M) (hK : 1 ≤ K) :
    Function.Injective (zeroExtend2 M K N1 N2) ↔ M ≤ N1 ∧ K ≤ N2 := by
  refine ⟨fun hinj => ?_, fun h => zeroExtend2_injective M K N1 N2 h.1 h.2⟩
  by_contra hcon
  rcases Nat.lt_or_ge N1 M with h1 | h1
  · have h : (fun p : Fin M × Fin K => if p.1.val = N1 then (1 : ℂ) else 0) = fun _ => 0 :=
      hinj (by
        funext p
        have hp : p.1.val ≠ N1 := (ZMod.val_lt p.1).ne
        simp [zeroExtend2, extendNat2, hp])
    have h2 := congrFun h (⟨N1, h1⟩, ⟨0, hK⟩)
    simp at h2
  · have hN2K : N2 < K := by omega
    have h : (fun p : Fin M × Fin K => if p.2.val = N2 then (1 : ℂ) else 0) = fun _ => 0 :=
      hinj (by
        funext p
        have hp : p.2.val ≠ N2 := (ZMod.val_lt p.2).ne
        simp [zeroExtend2, extendNat2, hp])
    have h2 := congrFun h (⟨0, hM⟩, ⟨N2, hN2K⟩)
    simp at h2

/-- Full two-dimensional linear convolution of rectangular supports. -/
def linearConvolution2 (M K P Q : ℕ) (x : Fin M × Fin K → ℂ)
    (y : Fin P × Fin Q → ℂ) : ℕ × ℕ → ℂ :=
  fun t => ∑ i ∈ Finset.range (t.1 + 1), ∑ j ∈ Finset.range (t.2 + 1),
    extendNat2 M K x (i, j) * extendNat2 P Q y (t.1 - i, t.2 - j)

private theorem extendNat2_eq_zero_of_le_left (M K : ℕ) (x : Fin M × Fin K → ℂ)
    (p1 p2 : ℕ) (h : M ≤ p1) : extendNat2 M K x (p1, p2) = 0 := by
  simp [extendNat2, Nat.not_lt.mpr h]

private theorem extendNat2_eq_zero_of_le_right (M K : ℕ) (x : Fin M × Fin K → ℂ)
    (p1 p2 : ℕ) (h : K ≤ p2) : extendNat2 M K x (p1, p2) = 0 := by
  simp [extendNat2, Nat.not_lt.mpr h]

private theorem sum_zmod2_eq_sum_range (M N : ℕ) [NeZero M] [NeZero N]
    (F : ZMod M → ZMod N → ℂ) :
    (∑ i : ZMod M, ∑ j : ZMod N, F i j)
      = (∑ m ∈ Finset.range M, ∑ n ∈ Finset.range N, F (m : ZMod M) (n : ZMod N)) := by
  rw [sum_zmod_eq_sum_range M (fun i => ∑ j : ZMod N, F i j)]
  apply Finset.sum_congr rfl
  intro m _
  exact sum_zmod_eq_sum_range N (fun j => F (m : ZMod M) j)

/-- Headline rectangular result: padding each axis to at least its
support sum minus one makes every cropped two-dimensional cyclic
coefficient inside the linear rectangle equal the full linear
coefficient. -/
theorem padded_cyclic_eq_linear_two_dim (M K P Q N1 N2 : ℕ) [NeZero N1] [NeZero N2]
    (hM : 1 ≤ M) (hK : 1 ≤ K) (hP : 1 ≤ P) (hQ : 1 ≤ Q)
    (hN1 : M + P - 1 ≤ N1) (hN2 : K + Q - 1 ≤ N2)
    (x : Fin M × Fin K → ℂ) (y : Fin P × Fin Q → ℂ) (t1 t2 : ℕ)
    (ht1 : t1 < M + P - 1) (ht2 : t2 < K + Q - 1) :
    circularConvolution2 (zeroExtend2 M K N1 N2 x) (zeroExtend2 P Q N1 N2 y)
        ((t1 : ZMod N1), (t2 : ZMod N2)) =
      linearConvolution2 M K P Q x y (t1, t2) := by
  have ht1N1 : t1 < N1 := lt_of_lt_of_le ht1 hN1
  have ht2N2 : t2 < N2 := lt_of_lt_of_le ht2 hN2
  have ht1N : t1 + 1 ≤ N1 := by omega
  have ht2N : t2 + 1 ≤ N2 := by omega
  simp only [circularConvolution2, linearConvolution2]
  rw [sum_zmod2_eq_sum_range N1 N2 (fun i j =>
    zeroExtend2 M K N1 N2 x (i, j) *
    zeroExtend2 P Q N1 N2 y ((t1 : ZMod N1) - i, (t2 : ZMod N2) - j))]
  have hrewrite : ∀ n1 ∈ Finset.range N1, ∀ n2 ∈ Finset.range N2,
      zeroExtend2 M K N1 N2 x ((n1 : ZMod N1), (n2 : ZMod N2)) *
        zeroExtend2 P Q N1 N2 y
          ((t1 : ZMod N1) - (n1 : ZMod N1), (t2 : ZMod N2) - (n2 : ZMod N2))
      = extendNat2 M K x (n1, n2) *
        extendNat2 P Q y
          ((((t1 : ZMod N1) - (n1 : ZMod N1)).val),
           (((t2 : ZMod N2) - (n2 : ZMod N2)).val)) := by
    intro n1 hn1 n2 hn2
    rw [Finset.mem_range] at hn1 hn2
    simp only [zeroExtend2, ZMod.val_natCast_of_lt hn1, ZMod.val_natCast_of_lt hn2]
  have hsum_eq : (∑ n1 ∈ Finset.range N1, ∑ n2 ∈ Finset.range N2,
        zeroExtend2 M K N1 N2 x ((n1 : ZMod N1), (n2 : ZMod N2)) *
        zeroExtend2 P Q N1 N2 y
          ((t1 : ZMod N1) - (n1 : ZMod N1), (t2 : ZMod N2) - (n2 : ZMod N2)))
      = (∑ n1 ∈ Finset.range N1, ∑ n2 ∈ Finset.range N2,
        extendNat2 M K x (n1, n2) *
        extendNat2 P Q y
          ((((t1 : ZMod N1) - (n1 : ZMod N1)).val),
           (((t2 : ZMod N2) - (n2 : ZMod N2)).val))) := by
    apply Finset.sum_congr rfl
    intro n1 hn1
    apply Finset.sum_congr rfl
    intro n2 hn2
    exact hrewrite n1 hn1 n2 hn2
  rw [hsum_eq]
  have hsplit1 := Finset.sum_range_add_sum_Ico
    (fun n1 => ∑ n2 ∈ Finset.range N2,
      extendNat2 M K x (n1, n2) *
      extendNat2 P Q y
        ((((t1 : ZMod N1) - (n1 : ZMod N1)).val),
         (((t2 : ZMod N2) - (n2 : ZMod N2)).val)))
    ht1N
  have hIco1_zero : (∑ n1 ∈ Finset.Ico (t1 + 1) N1, ∑ n2 ∈ Finset.range N2,
      extendNat2 M K x (n1, n2) *
      extendNat2 P Q y
        ((((t1 : ZMod N1) - (n1 : ZMod N1)).val),
         (((t2 : ZMod N2) - (n2 : ZMod N2)).val))) = 0 := by
    apply Finset.sum_eq_zero
    intro n1 hn1
    rw [Finset.mem_Ico] at hn1
    obtain ⟨hle1, hltN1⟩ := hn1
    have hlt1 : t1 < n1 := by omega
    apply Finset.sum_eq_zero
    intro n2 hn2
    rw [Finset.mem_range] at hn2
    by_cases hMn1 : M ≤ n1
    · have h0 := extendNat2_eq_zero_of_le_left M K x n1 n2 hMn1
      simp [h0]
    · have hn1M : n1 < M := by omega
      by_cases hKn2 : K ≤ n2
      · have h0 := extendNat2_eq_zero_of_le_right M K x n1 n2 hKn2
        simp [h0]
      · have hn2K : n2 < K := by omega
        have hPle : P ≤ ((t1 : ZMod N1) - (n1 : ZMod N1)).val :=
          le_of_sub_val_of_lt M P N1 t1 n1 hM hP hN1 ht1 hltN1 hn1M hlt1
        have h0 := extendNat2_eq_zero_of_le_left P Q y
          (((t1 : ZMod N1) - (n1 : ZMod N1)).val)
          (((t2 : ZMod N2) - (n2 : ZMod N2)).val) hPle
        simp [h0]
  have hinner_split : ∀ n1 ∈ Finset.range (t1 + 1),
      (∑ n2 ∈ Finset.range N2,
        extendNat2 M K x (n1, n2) *
        extendNat2 P Q y
          ((((t1 : ZMod N1) - (n1 : ZMod N1)).val),
           (((t2 : ZMod N2) - (n2 : ZMod N2)).val)))
      = (∑ n2 ∈ Finset.range (t2 + 1),
        extendNat2 M K x (n1, n2) *
        extendNat2 P Q y
          ((((t1 : ZMod N1) - (n1 : ZMod N1)).val),
           (((t2 : ZMod N2) - (n2 : ZMod N2)).val))) := by
    intro n1 hn1
    rw [Finset.mem_range] at hn1
    have hle1 : n1 ≤ t1 := by omega
    have hn1N1 : n1 < N1 := lt_of_le_of_lt hle1 ht1N1
    have hsplit2 := Finset.sum_range_add_sum_Ico
      (fun n2 => extendNat2 M K x (n1, n2) *
        extendNat2 P Q y
          ((((t1 : ZMod N1) - (n1 : ZMod N1)).val),
           (((t2 : ZMod N2) - (n2 : ZMod N2)).val)))
      ht2N
    have hIco2_zero : (∑ n2 ∈ Finset.Ico (t2 + 1) N2,
        extendNat2 M K x (n1, n2) *
        extendNat2 P Q y
          ((((t1 : ZMod N1) - (n1 : ZMod N1)).val),
           (((t2 : ZMod N2) - (n2 : ZMod N2)).val))) = 0 := by
      apply Finset.sum_eq_zero
      intro n2 hn2
      rw [Finset.mem_Ico] at hn2
      obtain ⟨hle2, hltN2⟩ := hn2
      have hlt2 : t2 < n2 := by omega
      by_cases hMn1 : M ≤ n1
      · have h0 := extendNat2_eq_zero_of_le_left M K x n1 n2 hMn1
        simp [h0]
      · have hn1M : n1 < M := by omega
        by_cases hKn2 : K ≤ n2
        · have h0 := extendNat2_eq_zero_of_le_right M K x n1 n2 hKn2
          simp [h0]
        · have hn2K : n2 < K := by omega
          have hQle : Q ≤ ((t2 : ZMod N2) - (n2 : ZMod N2)).val :=
            le_of_sub_val_of_lt K Q N2 t2 n2 hK hQ hN2 ht2 hltN2 hn2K hlt2
          have h0 := extendNat2_eq_zero_of_le_right P Q y
            (((t1 : ZMod N1) - (n1 : ZMod N1)).val)
            (((t2 : ZMod N2) - (n2 : ZMod N2)).val) hQle
          simp [h0]
    have hsplit2' := hsplit2.symm
    rw [hIco2_zero, add_zero] at hsplit2'
    exact hsplit2'
  have houter : (∑ n1 ∈ Finset.range N1, ∑ n2 ∈ Finset.range N2,
        extendNat2 M K x (n1, n2) *
        extendNat2 P Q y
          ((((t1 : ZMod N1) - (n1 : ZMod N1)).val),
           (((t2 : ZMod N2) - (n2 : ZMod N2)).val)))
      = (∑ n1 ∈ Finset.range (t1 + 1), ∑ n2 ∈ Finset.range (t2 + 1),
        extendNat2 M K x (n1, n2) *
        extendNat2 P Q y
          ((((t1 : ZMod N1) - (n1 : ZMod N1)).val),
           (((t2 : ZMod N2) - (n2 : ZMod N2)).val))) := by
    have hsplit1' := hsplit1.symm
    rw [hIco1_zero, add_zero] at hsplit1'
    have h2 : (∑ n1 ∈ Finset.range (t1 + 1), ∑ n2 ∈ Finset.range N2,
          extendNat2 M K x (n1, n2) *
          extendNat2 P Q y
            ((((t1 : ZMod N1) - (n1 : ZMod N1)).val),
             (((t2 : ZMod N2) - (n2 : ZMod N2)).val)))
        = (∑ n1 ∈ Finset.range (t1 + 1), ∑ n2 ∈ Finset.range (t2 + 1),
          extendNat2 M K x (n1, n2) *
          extendNat2 P Q y
            ((((t1 : ZMod N1) - (n1 : ZMod N1)).val),
             (((t2 : ZMod N2) - (n2 : ZMod N2)).val))) := by
      apply Finset.sum_congr rfl
      intro n1 hn1
      exact hinner_split n1 hn1
    exact hsplit1'.trans h2
  rw [houter]
  apply Finset.sum_congr rfl
  intro n1 hn1
  rw [Finset.mem_range] at hn1
  have hle1 : n1 ≤ t1 := by omega
  have hn1N1 : n1 < N1 := lt_of_le_of_lt hle1 ht1N1
  have hval1 : (((t1 : ZMod N1) - (n1 : ZMod N1)).val) = t1 - n1 :=
    sub_val_eq_of_le N1 t1 n1 ht1N1 hn1N1 hle1
  apply Finset.sum_congr rfl
  intro n2 hn2
  rw [Finset.mem_range] at hn2
  have hle2 : n2 ≤ t2 := by omega
  have hn2N2 : n2 < N2 := lt_of_le_of_lt hle2 ht2N2
  have hval2 : (((t2 : ZMod N2) - (n2 : ZMod N2)).val) = t2 - n2 :=
    sub_val_eq_of_le N2 t2 n2 ht2N2 hn2N2 hle2
  rw [hval1, hval2]

/-- The rectangular cyclic convolution is the rectangular inverse
transform of the pointwise product of the row-then-column transforms
of the zero extensions. This is the rectangular convolution theorem
`rectangularInvDFT_mul_rowColumnDFT` specialized to zero-extended
arrays. -/
theorem rectangular_cyclic_eq_inverse_transform_product (M K P Q N1 N2 : ℕ)
    [NeZero N1] [NeZero N2] (x : Fin M × Fin K → ℂ) (y : Fin P × Fin Q → ℂ) :
    circularConvolution2 (zeroExtend2 M K N1 N2 x) (zeroExtend2 P Q N1 N2 y) =
      rectangularInvDFT (fun p => rowColumnDFT (zeroExtend2 M K N1 N2 x) p *
        rowColumnDFT (zeroExtend2 P Q N1 N2 y) p) :=
  (rectangularInvDFT_mul_rowColumnDFT _ _).symm

end CSLibExt.Algorithms.Lean.Fourier.FFT.SupportBoundedPadding
