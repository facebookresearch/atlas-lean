/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.SupportBoundedPadding

/-!
# Overlap-add block convolution with a finite FFT size

A finite signal of length `N` is cut into consecutive, disjoint blocks of
length `L ≥ 1` (there are `⌈N / L⌉` of them, and the last one is zero padded).
Each block is convolved with a kernel of length `M ≥ 1` by a length-`Q`
cyclic convolution, which is the inverse length-`Q` DFT of the product of the
two length-`Q` DFTs. Shifting every frame by its block start `b * L` and
adding the frames is the overlap-add method.

The main result, `overlapAdd_eq_linearConvolution`, states that for
`Q ≥ L + M - 1` overlap-add equals the full linear convolution of the signal
with the kernel at every natural index, including the final `M - 1` tail.
The proof splits into a transform-free reindexing of the convolution sum
(`linearConvolution_eq_sum_shifted_blocks`) and the zero-padding identity for
each frame (`blockFrame_eq_linearConvolution`, from `padded_cyclic_eq_linear`).

Three boundary results show the hypotheses matter:

- `truncation_to_input_length_fails`: for `M ≥ 2`, keeping only the first `N`
  output samples loses the tail;
- `overlapAdd_ne_linearConvolution_of_short_fft`: once the signal holds a full
  first block (`L ≤ N`), every FFT size `Q < L + M - 1` gives a wrong output.
  When `Q < L` or `Q < M` the cause is truncation, not wraparound: zero
  extension to length `Q` discards block or kernel entries;
- `overlapAdd_aliases_of_short_fft`: when also `L ≤ Q` and `M ≤ Q`, the
  failure is circular aliasing; the last linear coefficient, at index
  `L + M - 2`, wraps onto index `L + M - 2 - Q`.

The restrictions are needed: for `M = 1` the tail is empty, and a signal
shorter than one block can make a short FFT size harmless.

Reference: A. V. Oppenheim and R. W. Schafer, *Discrete-Time Signal
Processing*, linear convolution with the DFT by the overlap-add method.
-/

@[expose] public section

set_option autoImplicit false

namespace CSLibExt.Algorithms.Lean.Fourier.FFT.FiniteOverlapAdd

open CSLibExt.Algorithms.Lean.Fourier.FFT.SupportBoundedPadding

/-! ### Block partition -/

/-- Number of hop-`L` blocks covering a length-`N` signal: `⌈N / L⌉`. -/
def blockCount (N L : ℕ) : ℕ :=
  (N + L - 1) / L

/-- Block `b` of a length-`N` signal at hop `L`: samples `b * L` through
`b * L + L - 1`, zero past the end of the signal. -/
def block (N L : ℕ) (x : Fin N → ℂ) (b : ℕ) : Fin L → ℂ :=
  fun i => extendNat N x (b * L + i.val)

/-- The blocks cover the signal. -/
theorem le_blockCount_mul (N L : ℕ) (hL : 1 ≤ L) :
    N ≤ blockCount N L * L := by
  unfold blockCount
  have hL0 : 0 < L := by omega
  have hmod : (N + L - 1) / L * L + (N + L - 1) % L = N + L - 1 := by
    have h := Nat.div_add_mod (N + L - 1) L
    rwa [mul_comm] at h
  have hlt : (N + L - 1) % L < L := Nat.mod_lt _ hL0
  set A := (N + L - 1) / L * L with hA
  set r := (N + L - 1) % L with hr
  omega

/-- No block is empty: the last block starts inside the signal. -/
theorem blockCount_sub_one_mul_lt (N L : ℕ) (hL : 1 ≤ L) (hN : 1 ≤ N) :
    (blockCount N L - 1) * L < N := by
  unfold blockCount
  have hL0 : 0 < L := by omega
  have hle : (N + L - 1) / L * L ≤ N + L - 1 := Nat.div_mul_le_self _ _
  have hq : 1 ≤ (N + L - 1) / L := (Nat.one_le_div_iff hL0).mpr (by omega)
  have hsub : ((N + L - 1) / L - 1) * L = (N + L - 1) / L * L - L := by
    rw [Nat.sub_mul, one_mul]
  set A := (N + L - 1) / L * L with hA
  set B := ((N + L - 1) / L - 1) * L with hB
  omega

/-- Inside the signal a block holds the signal sample. -/
theorem block_apply_of_lt (N L : ℕ) (x : Fin N → ℂ) (b : ℕ) (i : Fin L)
    (hi : b * L + i.val < N) :
    block N L x b i = x ⟨b * L + i.val, hi⟩ := by
  unfold block extendNat
  simp [hi]

/-- Past the end of the signal a block is zero padded. -/
theorem block_apply_eq_zero_of_le (N L : ℕ) (x : Fin N → ℂ) (b : ℕ) (i : Fin L)
    (hi : N ≤ b * L + i.val) :
    block N L x b i = 0 := by
  unfold block extendNat
  simp [Nat.not_lt.mpr hi]

/-- Disjoint consecutive partition: sample `n` sits in block `n / L` at
offset `n % L`, and only there. -/
theorem extendNat_eq_block_div_mod (N L : ℕ) (hL : 1 ≤ L) (x : Fin N → ℂ) (n : ℕ) :
    extendNat N x n = block N L x (n / L) ⟨n % L, Nat.mod_lt n (by omega)⟩ := by
  unfold block
  have h : (n / L) * L + n % L = n := by
    have hmod := Nat.div_add_mod n L
    rwa [mul_comm] at hmod
  rw [h]

/-! ### Block frames and overlap-add -/

/-- The length-`Q` cyclic convolution frame of block `b` with the kernel,
read at natural offsets and zero from offset `Q` on. -/
def blockFrame (Q : ℕ) [NeZero Q] (N L M : ℕ) (x : Fin N → ℂ) (h : Fin M → ℂ)
    (b : ℕ) : ℕ → ℂ :=
  fun t => if t < Q then
    cyclicConvolution Q (zeroExtend L Q (block N L x b)) (zeroExtend M Q h) (t : ZMod Q)
  else 0

/-- Overlap-add: shift each block frame by its block start `b * L` and add
the frames of all `blockCount N L` blocks. -/
def overlapAdd (Q : ℕ) [NeZero Q] (N L M : ℕ) (x : Fin N → ℂ) (h : Fin M → ℂ) :
    ℕ → ℂ :=
  fun n => ∑ b ∈ Finset.range (blockCount N L),
    if b * L ≤ n then blockFrame Q N L M x h b (n - b * L) else 0

/-- Each frame value inside the frame is the inverse length-`Q` DFT of the
product of the length-`Q` DFTs of the padded block and padded kernel. -/
theorem blockFrame_eq_invDFT_mul (Q : ℕ) [NeZero Q] (N L M : ℕ) (x : Fin N → ℂ)
    (h : Fin M → ℂ) (b t : ℕ) (ht : t < Q) :
    blockFrame Q N L M x h b t =
      ZMod.dft.symm (fun k => ZMod.dft (zeroExtend L Q (block N L x b)) k *
        ZMod.dft (zeroExtend M Q h) k) (t : ZMod Q) := by
  unfold blockFrame
  simp only [ht, ↓reduceIte]
  have hmul := cyclicConvolution_eq_invDFT_mul L M Q (block N L x b) h
  rw [hmul]

private theorem zeroExtend_eq_zero_of_le (M Q : ℕ) (x : Fin M → ℂ) (j : ZMod Q)
    (hj : M ≤ j.val) :
    zeroExtend M Q x j = 0 := by
  unfold zeroExtend
  exact extendNat_eq_zero_of_le M x j.val hj

private theorem linearConvolution_eq_zero_of_ge (L M : ℕ) (x : Fin L → ℂ) (h : Fin M → ℂ)
    (t : ℕ) (ht : L + M - 1 ≤ t) :
    linearConvolution L M x h t = 0 := by
  unfold linearConvolution
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Finset.mem_range] at hj
  have hjt : j ≤ t := by omega
  by_cases hjL : j < L
  · have htj : M ≤ t - j := by omega
    rw [extendNat_eq_zero_of_le M h (t - j) htj, mul_zero]
  · have hLj : L ≤ j := by omega
    rw [extendNat_eq_zero_of_le L x j hLj, zero_mul]

private theorem cyclic_eq_zero_of_ge (Q L M : ℕ) [NeZero Q] (x : Fin L → ℂ) (h : Fin M → ℂ)
    (t : ℕ) (htQ : t < Q) (ht : L + M - 1 ≤ t) :
    cyclicConvolution Q (zeroExtend L Q x) (zeroExtend M Q h) (t : ZMod Q) = 0 := by
  unfold cyclicConvolution
  refine Fintype.sum_eq_zero _ (fun j => ?_)
  by_cases hjL : j.val < L
  · have hval_t : (t : ZMod Q).val = t := ZMod.val_natCast_of_lt htQ
    have hadd : j + ((t : ZMod Q) - j) = (t : ZMod Q) := by abel
    have hval_add := congrArg ZMod.val hadd
    simp only [ZMod.val_add] at hval_add
    rw [hval_t] at hval_add
    have hmod_le := Nat.mod_le (j.val + ((t : ZMod Q) - j).val) Q
    have hle : t ≤ j.val + ((t : ZMod Q) - j).val := by omega
    have hMle : M ≤ ((t : ZMod Q) - j).val := by omega
    rw [zeroExtend_eq_zero_of_le M Q h _ hMle, mul_zero]
  · have hLle : L ≤ j.val := by omega
    rw [zeroExtend_eq_zero_of_le L Q x j hLle, zero_mul]

/-- With FFT size at least `L + M - 1`, every block frame is the full
linear convolution of that block with the kernel, at every natural
offset (the frame tail past `L + M - 1` is zero). -/
theorem blockFrame_eq_linearConvolution (Q : ℕ) [NeZero Q] (N L M : ℕ)
    (hL : 1 ≤ L) (hM : 1 ≤ M) (hQ : L + M - 1 ≤ Q) (x : Fin N → ℂ) (h : Fin M → ℂ)
    (b : ℕ) :
    blockFrame Q N L M x h b = linearConvolution L M (block N L x b) h := by
  funext t
  by_cases htQ : t < Q
  · by_cases htLM : t < L + M - 1
    · unfold blockFrame
      simp only [htQ, ↓reduceIte]
      exact padded_cyclic_eq_linear L M Q hL hM hQ (block N L x b) h t htLM
    · have hge : L + M - 1 ≤ t := by omega
      have hframe0 : blockFrame Q N L M x h b t = 0 := by
        unfold blockFrame
        simp only [htQ, ↓reduceIte]
        exact cyclic_eq_zero_of_ge Q L M (block N L x b) h t htQ hge
      have hlin0 : linearConvolution L M (block N L x b) h t = 0 :=
        linearConvolution_eq_zero_of_ge L M (block N L x b) h t hge
      rw [hframe0, hlin0]
  · have hge : L + M - 1 ≤ t := by omega
    have hframe0 : blockFrame Q N L M x h b t = 0 := by
      unfold blockFrame
      simp [htQ]
    have hlin0 : linearConvolution L M (block N L x b) h t = 0 :=
      linearConvolution_eq_zero_of_ge L M (block N L x b) h t hge
    rw [hframe0, hlin0]

private theorem extendNat_block (N L : ℕ) (x : Fin N → ℂ) (b i : ℕ) :
    extendNat L (block N L x b) i =
      if i < L then extendNat N x (b * L + i) else 0 := by
  conv_lhs => unfold extendNat block
  by_cases hi : i < L
  · simp [hi]
  · simp [hi]

private theorem shifted_per_block (N L M : ℕ) (x : Fin N → ℂ) (h : Fin M → ℂ)
    (n b : ℕ) :
    (if b * L ≤ n then linearConvolution L M (block N L x b) h (n - b * L) else 0) =
      ∑ i ∈ Finset.range L,
        (if b * L + i ≤ n then extendNat N x (b * L + i) * extendNat M h (n - (b * L + i))
          else 0) := by
  by_cases hb : b * L ≤ n
  · simp only [hb, ↓reduceIte]
    unfold linearConvolution
    have hterm : ∀ i, extendNat L (block N L x b) i * extendNat M h (n - b * L - i) =
        (if i < L then extendNat N x (b * L + i) * extendNat M h (n - (b * L + i))
          else 0) := by
      intro i
      rw [extendNat_block]
      by_cases hi : i < L
      · simp only [hi, ↓reduceIte]
        have hsub : n - b * L - i = n - (b * L + i) := (Nat.sub_add_eq n (b * L) i).symm
        rw [hsub]
      · simp [hi]
    have hLHS : (∑ i ∈ Finset.range (n - b * L + 1),
          extendNat L (block N L x b) i * extendNat M h (n - b * L - i)) =
        ∑ i ∈ Finset.range (n - b * L + 1),
          (if i < L then extendNat N x (b * L + i) * extendNat M h (n - (b * L + i))
            else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hterm i
    rw [hLHS]
    conv_lhs => rw [← Finset.sum_filter]
    conv_rhs => rw [← Finset.sum_filter]
    have hset : (Finset.range (n - b * L + 1)).filter (fun i => i < L) =
        (Finset.range L).filter (fun i => b * L + i ≤ n) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hset]
  · simp only [hb, ↓reduceIte]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have hne : ¬ (b * L + i ≤ n) := by omega
    simp [hne]

/-- Transform-free decomposition: the full linear convolution is the sum
of the block linear convolutions shifted by their block starts. -/
theorem linearConvolution_eq_sum_shifted_blocks (N L M : ℕ) (hL : 1 ≤ L)
    (x : Fin N → ℂ) (h : Fin M → ℂ) (n : ℕ) :
    linearConvolution N M x h n =
      ∑ b ∈ Finset.range (blockCount N L),
        if b * L ≤ n then linearConvolution L M (block N L x b) h (n - b * L) else 0 := by
  have hL0 : 0 < L := by omega
  have hRHS : (∑ b ∈ Finset.range (blockCount N L),
        (if b * L ≤ n then linearConvolution L M (block N L x b) h (n - b * L) else 0)) =
      ∑ b ∈ Finset.range (blockCount N L), ∑ i ∈ Finset.range L,
        (if b * L + i ≤ n then extendNat N x (b * L + i) * extendNat M h (n - (b * L + i))
          else 0) := by
    apply Finset.sum_congr rfl
    intro b _
    exact shifted_per_block N L M x h n b
  rw [hRHS]
  have hprod : (∑ b ∈ Finset.range (blockCount N L), ∑ i ∈ Finset.range L,
        (if b * L + i ≤ n then extendNat N x (b * L + i) * extendNat M h (n - (b * L + i))
          else 0)) =
      ∑ p ∈ Finset.range (blockCount N L) ×ˢ Finset.range L,
        (if p.1 * L + p.2 ≤ n then
            extendNat N x (p.1 * L + p.2) * extendNat M h (n - (p.1 * L + p.2))
          else 0) := by
    exact (Finset.sum_product (Finset.range (blockCount N L)) (Finset.range L)
      (fun p => if p.1 * L + p.2 ≤ n then
        extendNat N x (p.1 * L + p.2) * extendNat M h (n - (p.1 * L + p.2)) else 0)).symm
  rw [hprod]
  have hbij : (∑ p ∈ Finset.range (blockCount N L) ×ˢ Finset.range L,
        (if p.1 * L + p.2 ≤ n then
            extendNat N x (p.1 * L + p.2) * extendNat M h (n - (p.1 * L + p.2))
          else 0)) =
      ∑ j ∈ Finset.range (blockCount N L * L),
        (if j ≤ n then extendNat N x j * extendNat M h (n - j) else 0) := by
    refine Finset.sum_bij (M := ℂ) (s := Finset.range (blockCount N L) ×ˢ Finset.range L)
      (t := Finset.range (blockCount N L * L))
      (f := fun p => if p.1 * L + p.2 ≤ n then
        extendNat N x (p.1 * L + p.2) * extendNat M h (n - (p.1 * L + p.2)) else 0)
      (g := fun j => if j ≤ n then extendNat N x j * extendNat M h (n - j) else 0) ?_ ?_ ?_ ?_ ?_
    · exact fun (p : ℕ × ℕ) (_ : p ∈ Finset.range (blockCount N L) ×ˢ Finset.range L) =>
        p.1 * L + p.2
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_range] at hp
      simp only [Finset.mem_range]
      obtain ⟨hb, hi⟩ := hp
      have hb1 : p.1 + 1 ≤ blockCount N L := by omega
      have hmul := Nat.mul_le_mul_right L hb1
      have hrewrite : (p.1 + 1) * L = p.1 * L + L := by ring
      rw [hrewrite] at hmul
      omega
    · intro p1 hp1 p2 hp2 heq
      simp only [Finset.mem_product, Finset.mem_range] at hp1 hp2
      obtain ⟨hb1, hi1⟩ := hp1
      obtain ⟨hb2, hi2⟩ := hp2
      have hdiv1 : (p1.1 * L + p1.2) / L = p1.1 := by
        conv_lhs => rw [mul_comm p1.1 L]
        rw [Nat.mul_add_div hL0]
        rw [Nat.div_eq_of_lt hi1, add_zero]
      have hdiv2 : (p2.1 * L + p2.2) / L = p2.1 := by
        conv_lhs => rw [mul_comm p2.1 L]
        rw [Nat.mul_add_div hL0]
        rw [Nat.div_eq_of_lt hi2, add_zero]
      have hmod1 : (p1.1 * L + p1.2) % L = p1.2 := by
        conv_lhs => rw [mul_comm p1.1 L]
        rw [Nat.mul_add_mod]
        exact Nat.mod_eq_of_lt hi1
      have hmod2 : (p2.1 * L + p2.2) % L = p2.2 := by
        conv_lhs => rw [mul_comm p2.1 L]
        rw [Nat.mul_add_mod]
        exact Nat.mod_eq_of_lt hi2
      have hb : p1.1 = p2.1 := by
        have hcongr := congrArg (· / L) heq
        simp only [hdiv1, hdiv2] at hcongr
        exact hcongr
      have hi : p1.2 = p2.2 := by
        have hcongr := congrArg (· % L) heq
        simp only [hmod1, hmod2] at hcongr
        exact hcongr
      exact Prod.ext_iff.mpr ⟨hb, hi⟩
    · intro j hj
      simp only [Finset.mem_range] at hj
      have hb : j / L < blockCount N L := (Nat.div_lt_iff_lt_mul hL0).mpr hj
      have hi : j % L < L := Nat.mod_lt j hL0
      refine ⟨(j / L, j % L), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hb,
        Finset.mem_range.mpr hi⟩, ?_⟩
      have hcomm : j / L * L + j % L = j := by
        have h := Nat.div_add_mod j L
        rwa [mul_comm] at h
      exact hcomm
    · intro p _
      rfl
  rw [hbij]
  unfold linearConvolution
  have hcover : N ≤ blockCount N L * L := le_blockCount_mul N L hL
  have hRHS2 : (∑ j ∈ Finset.range (blockCount N L * L),
        (if j ≤ n then extendNat N x j * extendNat M h (n - j) else 0)) =
      ∑ j ∈ Finset.range (blockCount N L * L) ∩ Finset.range (n + 1),
        extendNat N x j * extendNat M h (n - j) := by
    have hfilter : (Finset.range (blockCount N L * L)).filter (fun j => j ≤ n) =
        Finset.range (blockCount N L * L) ∩ Finset.range (n + 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_inter]
      omega
    have hsum : (∑ j ∈ Finset.range (blockCount N L * L),
          (if j ≤ n then extendNat N x j * extendNat M h (n - j) else 0)) =
        ∑ j ∈ (Finset.range (blockCount N L * L)).filter (fun j => j ≤ n),
          extendNat N x j * extendNat M h (n - j) := by
      exact (Finset.sum_filter _ _).symm
    rw [hsum, hfilter]
  have hLHS : (∑ j ∈ Finset.range (n + 1), extendNat N x j * extendNat M h (n - j)) =
      ∑ j ∈ Finset.range (n + 1) ∩ Finset.range (blockCount N L * L),
        extendNat N x j * extendNat M h (n - j) := by
    symm
    refine Finset.sum_subset Finset.inter_subset_left (fun j hj1 hj2 => ?_)
    have hj_not : j ∉ Finset.range (blockCount N L * L) := by
      intro hmem
      exact hj2 (Finset.mem_inter.mpr ⟨hj1, hmem⟩)
    simp only [Finset.mem_range] at hj_not
    have hNj : N ≤ j := by omega
    have h0 : extendNat N x j = 0 := extendNat_eq_zero_of_le N x j hNj
    simp [h0]
  rw [hRHS2, hLHS]
  congr 1
  exact Finset.inter_comm _ _

/-- Headline: overlap-add with FFT size `Q >= L + M - 1` equals the full
linear convolution at every natural index, including the final
`M - 1` tail and beyond it. -/
theorem overlapAdd_eq_linearConvolution (Q : ℕ) [NeZero Q] (N L M : ℕ)
    (hL : 1 ≤ L) (hM : 1 ≤ M) (hQ : L + M - 1 ≤ Q) (x : Fin N → ℂ) (h : Fin M → ℂ) :
    overlapAdd Q N L M x h = linearConvolution N M x h := by
  funext n
  have hdecomp := linearConvolution_eq_sum_shifted_blocks N L M hL x h n
  unfold overlapAdd
  rw [hdecomp]
  apply Finset.sum_congr rfl
  intro b _
  have hfb := blockFrame_eq_linearConvolution Q N L M hL hM hQ x h b
  by_cases hb : b * L ≤ n
  · simp only [hb, ↓reduceIte]
    exact congrFun hfb (n - b * L)
  · simp [hb]

/-! ### Boundary cases -/

/-- The tail is needed: for a kernel of length at least two, truncating
the output to the input length loses the final linear coefficients. -/
theorem truncation_to_input_length_fails (Q : ℕ) [NeZero Q] (N L M : ℕ)
    (hN : 1 ≤ N) (hM : 2 ≤ M) :
    ∃ x : Fin N → ℂ, ∃ h : Fin M → ℂ,
      (fun n => if n < N then overlapAdd Q N L M x h n else 0) ≠
        linearConvolution N M x h := by
  refine ⟨fun i => if i.val = N - 1 then 1 else 0, fun j => if j.val = M - 1 then 1 else 0, ?_⟩
  have hN1 : N - 1 < N := by omega
  have hM1 : M - 1 < M := by omega
  have hx : ∀ j, extendNat N (fun i : Fin N => if i.val = N - 1 then (1 : ℂ) else 0) j =
      if j = N - 1 then 1 else 0 := by
    intro j
    unfold extendNat
    by_cases hj : j = N - 1
    · subst hj
      simp [hN1]
    · by_cases hjN : j < N <;> simp [hjN, hj]
  have hy : ∀ k, extendNat M (fun j : Fin M => if j.val = M - 1 then (1 : ℂ) else 0) k =
      if k = M - 1 then 1 else 0 := by
    intro k
    unfold extendNat
    by_cases hk : k = M - 1
    · subst hk
      simp [hM1]
    · by_cases hkM : k < M <;> simp [hkM, hk]
  have ht : (N + M - 2) - (N - 1) = M - 1 := by omega
  have hmem : N - 1 ∈ Finset.range (N + M - 2 + 1) := by
    simp only [Finset.mem_range]
    omega
  have hlin : linearConvolution N M
      (fun i : Fin N => if i.val = N - 1 then (1 : ℂ) else 0)
      (fun j : Fin M => if j.val = M - 1 then (1 : ℂ) else 0) (N + M - 2) = 1 := by
    unfold linearConvolution
    rw [Finset.sum_eq_single (N - 1) (fun b _ hb => by simp [hx, hb])
      (fun h => absurd hmem h)]
    simp [hx, hy, ht]
  have htrunc : (if N + M - 2 < N then overlapAdd Q N L M
      (fun i : Fin N => if i.val = N - 1 then (1 : ℂ) else 0)
      (fun j : Fin M => if j.val = M - 1 then (1 : ℂ) else 0) (N + M - 2) else 0) = 0 := by
    simp [Nat.not_lt.mpr (show N ≤ N + M - 2 by omega)]
  intro heq
  have hcongr := congrFun heq (N + M - 2)
  rw [htrunc, hlin] at hcongr
  simp at hcongr

/-- An FFT size below `L + M - 1` gives a wrong output: once the signal
holds a full first block, some signal and kernel make overlap-add differ
from the linear convolution. Two mechanisms are covered. When `Q < L` or
`Q < M`, zero extension to length `Q` keeps only the first `Q` entries of
a block or of the kernel, so input is discarded before the cyclic
convolution and no coefficient need wrap (for example `N = L = 2`,
`M = Q = 1`). When `L ≤ Q` and `M ≤ Q` the failure is circular aliasing,
stated in `overlapAdd_aliases_of_short_fft`. -/
theorem overlapAdd_ne_linearConvolution_of_short_fft (Q : ℕ) [NeZero Q] (N L M : ℕ)
    (hL : 1 ≤ L) (hM : 1 ≤ M) (hLN : L ≤ N) (hQ : Q < L + M - 1) :
    ∃ x : Fin N → ℂ, ∃ h : Fin M → ℂ,
      overlapAdd Q N L M x h ≠ linearConvolution N M x h := by
  have hQ1 : 1 ≤ Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  by_cases hsmall : L + M - 1 ≤ 1
  · have hfalse : False := by omega
    exact False.elim hfalse
  · refine ⟨fun i => if i.val = L - 1 then 1 else 0, fun j => if j.val = M - 1 then 1 else 0, ?_⟩
    have hLN1 : L - 1 < N := by omega
    have hM1 : M - 1 < M := by omega
    have hx : ∀ j, extendNat N (fun i : Fin N => if i.val = L - 1 then (1 : ℂ) else 0) j =
        if j = L - 1 then 1 else 0 := by
      intro j
      unfold extendNat
      by_cases hj : j = L - 1
      · subst hj
        simp [hLN1]
      · by_cases hjN : j < N <;> simp [hjN, hj]
    have hy : ∀ k, extendNat M (fun j : Fin M => if j.val = M - 1 then (1 : ℂ) else 0) k =
        if k = M - 1 then 1 else 0 := by
      intro k
      unfold extendNat
      by_cases hk : k = M - 1
      · subst hk
        simp [hM1]
      · by_cases hkM : k < M <;> simp [hkM, hk]
    have ht : (L + M - 2) - (L - 1) = M - 1 := by omega
    have htQ : Q ≤ L + M - 2 := by omega
    have hmem : L - 1 ∈ Finset.range (L + M - 2 + 1) := by
      simp only [Finset.mem_range]
      omega
    have hlin : linearConvolution N M
        (fun i : Fin N => if i.val = L - 1 then (1 : ℂ) else 0)
        (fun j : Fin M => if j.val = M - 1 then (1 : ℂ) else 0) (L + M - 2) = 1 := by
      unfold linearConvolution
      rw [Finset.sum_eq_single (L - 1) (fun b _ hb => by simp [hx, hb])
        (fun h => absurd hmem h)]
      simp [hx, hy, ht]
    have hola : overlapAdd Q N L M
        (fun i : Fin N => if i.val = L - 1 then (1 : ℂ) else 0)
        (fun j : Fin M => if j.val = M - 1 then (1 : ℂ) else 0) (L + M - 2) = 0 := by
      unfold overlapAdd
      apply Finset.sum_eq_zero
      intro b hb
      by_cases hbL : b * L ≤ L + M - 2
      · simp only [hbL, ↓reduceIte]
        by_cases hb0 : b = 0
        · subst hb0
          simp only [zero_mul, Nat.sub_zero]
          unfold blockFrame
          simp [Nat.not_lt.mpr htQ]
        · have hb1 : 1 ≤ b := Nat.pos_of_ne_zero hb0
          have hbLge : L ≤ b * L := by
            conv_lhs => rw [← one_mul L]
            exact Nat.mul_le_mul_right L hb1
          have hblock0 : ∀ i : Fin L, block N L
              (fun i : Fin N => if i.val = L - 1 then (1 : ℂ) else 0) b i = 0 := by
            intro i
            have hne : b * L + i.val ≠ L - 1 := by omega
            unfold block
            rw [hx]
            simp [hne]
          have hz0 : ∀ j : ZMod Q, zeroExtend L Q (block N L
              (fun i : Fin N => if i.val = L - 1 then (1 : ℂ) else 0) b) j = 0 := by
            intro j
            unfold zeroExtend extendNat
            by_cases hj : j.val < L
            · simp [hj, hblock0]
            · simp [hj]
          by_cases hsQ : L + M - 2 - b * L < Q
          · unfold blockFrame
            simp only [hsQ, ↓reduceIte]
            unfold cyclicConvolution
            simp [hz0]
          · unfold blockFrame
            simp [hsQ]
      · simp [hbL]
    intro heq
    have hcongr := congrFun heq (L + M - 2)
    rw [hola, hlin] at hcongr
    simp at hcongr

/-- Circular aliasing at a short FFT size. When the block length and the
kernel length both fit the FFT size (`L ≤ Q`, `M ≤ Q`) but `Q < L + M - 1`,
unit impulses at the end of the first block and at the end of the kernel
have last linear coefficient `1` at index `L + M - 2`. Overlap-add wraps it
onto index `L + M - 2 - Q`, where the linear convolution is `0` and
overlap-add returns `1`. -/
theorem overlapAdd_aliases_of_short_fft (Q : ℕ) [NeZero Q] (N L M : ℕ)
    (hLN : L ≤ N) (hLQ : L ≤ Q) (hMQ : M ≤ Q) (hQ : Q < L + M - 1) :
    ∃ x : Fin N → ℂ, ∃ h : Fin M → ℂ,
      linearConvolution N M x h (L + M - 2) = 1 ∧
      linearConvolution N M x h (L + M - 2 - Q) = 0 ∧
      overlapAdd Q N L M x h (L + M - 2 - Q) = 1 := by
  have hQ1 : 1 ≤ Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  refine ⟨fun i => if i.val = L - 1 then 1 else 0, fun j => if j.val = M - 1 then 1 else 0, ?_⟩
  have hLN1 : L - 1 < N := by omega
  have hM1 : M - 1 < M := by omega
  have hL1L : L - 1 < L := by omega
  have hL1Q : L - 1 < Q := by omega
  have hM1Q : M - 1 < Q := by omega
  have hn0Q : L + M - 2 - Q < Q := by omega
  have hx : ∀ j, extendNat N (fun i : Fin N => if i.val = L - 1 then (1 : ℂ) else 0) j =
      if j = L - 1 then 1 else 0 := by
    intro j
    unfold extendNat
    by_cases hj : j = L - 1
    · subst hj
      simp [hLN1]
    · by_cases hjN : j < N <;> simp [hjN, hj]
  have hy : ∀ k, extendNat M (fun j : Fin M => if j.val = M - 1 then (1 : ℂ) else 0) k =
      if k = M - 1 then 1 else 0 := by
    intro k
    unfold extendNat
    by_cases hk : k = M - 1
    · subst hk
      simp [hM1]
    · by_cases hkM : k < M <;> simp [hkM, hk]
  refine ⟨?_, ?_, ?_⟩
  · have ht : (L + M - 2) - (L - 1) = M - 1 := by omega
    have hmem : L - 1 ∈ Finset.range (L + M - 2 + 1) := by
      simp only [Finset.mem_range]
      omega
    unfold linearConvolution
    rw [Finset.sum_eq_single (L - 1) (fun b _ hb => by simp [hx, hb])
      (fun h => absurd hmem h)]
    simp [hx, hy, ht]
  · unfold linearConvolution
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_range] at hj
    by_cases hjL : j = L - 1
    · have hne : L + M - 2 - Q - (L - 1) ≠ M - 1 := by omega
      rw [hjL, hx, hy]
      simp [hne]
    · rw [hx]
      simp [hjL]
  · have hbc : 0 < blockCount N L := by
      have hcover := le_blockCount_mul N L (by omega)
      rcases Nat.eq_zero_or_pos (blockCount N L) with h0 | h0
      · rw [h0, zero_mul] at hcover
        omega
      · exact h0
    simp only [overlapAdd]
    refine (Finset.sum_eq_single 0 ?_ ?_).trans ?_
    · intro b _ hb0
      have hbL : L ≤ b * L := by
        have hmul := Nat.mul_le_mul_right L (Nat.pos_of_ne_zero hb0)
        omega
      have hnot : ¬ b * L ≤ L + M - 2 - Q := by omega
      simp [hnot]
    · intro h0
      exact absurd (Finset.mem_range.mpr hbc) h0
    · rw [if_pos (by omega)]
      simp only [zero_mul, Nat.sub_zero]
      unfold blockFrame
      simp only [hn0Q, ↓reduceIte]
      simp only [cyclicConvolution]
      refine (Finset.sum_eq_single ((L - 1 : ℕ) : ZMod Q) ?_ ?_).trans ?_
      · intro j _ hj
        have hjval : j.val ≠ L - 1 := by
          intro hcontra
          apply hj
          have hjc := ZMod.natCast_zmod_val j
          rw [hcontra] at hjc
          exact hjc.symm
        simp only [zeroExtend]
        rw [extendNat_block, hx]
        by_cases hjL : j.val < L <;> simp [hjL, hjval]
      · intro h0
        exact absurd (Finset.mem_univ _) h0
      · have hcast : ((L + M - 2 - Q : ℕ) : ZMod Q) - ((L - 1 : ℕ) : ZMod Q) =
            ((M - 1 : ℕ) : ZMod Q) := by
          rw [sub_eq_iff_eq_add, ← Nat.cast_add]
          have hsum : M - 1 + (L - 1) = (L + M - 2 - Q) + Q := by omega
          rw [hsum, Nat.cast_add, ZMod.natCast_self, add_zero]
        rw [hcast]
        simp only [zeroExtend, ZMod.val_natCast_of_lt hL1Q, ZMod.val_natCast_of_lt hM1Q]
        rw [extendNat_block, hx, hy]
        simp [hL1L]

end CSLibExt.Algorithms.Lean.Fourier.FFT.FiniteOverlapAdd
