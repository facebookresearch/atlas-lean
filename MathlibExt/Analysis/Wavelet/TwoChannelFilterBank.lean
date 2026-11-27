/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.ZMod.Basic

/-!
# Perfect reconstruction of the orthogonal two-channel filter bank

One level of the fast wavelet transform (S. Mallat, *A theory for multiresolution signal
decomposition: the wavelet representation*, IEEE Trans. Pattern Anal. Mach. Intell. 11 (1989),
674–693; S. Mallat, *Multiresolution approximations and wavelet orthonormal bases of `L²(ℝ)`*,
Trans. Amer. Math. Soc. 315 (1989), 69–87, Section 4, equations (64)–(68)) splits a signal `x`
into a low-pass and a high-pass half by filtering with a pair of filters `h, g` and keeping one
sample out of two:

`a[n] = ∑_k conj(h[k - 2n]) x[k] = ⟨τ_{2n} h, x⟩` and
`d[n] = ∑_k conj(g[k - 2n]) x[k] = ⟨τ_{2n} g, x⟩`,

where `τ_s h[k] = h[k - s]` is the translate. Reconstruction upsamples and filters again:
`x[k] = ∑_n a[n] h[k - 2n] + ∑_n d[n] g[k - 2n]`. In the frequency domain, Mallat's equations
(66)–(68) say that this decomposition is orthogonal and reconstructs every signal exactly when
the matrix `[[H(ω), G(ω)], [H(ω + π), G(ω + π)]]` is unitary ("conjugate mirror filters"); in
the time domain this is the statement that the even translates of `h` and `g` form an
orthonormal family.

This file proves the finite, periodic version of the statement: for signals on the cyclic
group `ℤ / 2N`, if the `2N` translates `τ_{2n} h, τ_{2n} g` (`0 ≤ n < N`) are orthonormal,
then analysis followed by synthesis is the identity (perfect reconstruction) and the
decomposition preserves energy. The Haar filters `h = (δ₀ + δ₁)/√2`, `g = (δ₀ - δ₁)/√2` are
the simplest example (see the tests).

## Main declarations

* `shift s x` : the cyclic translate `τ_s x`.
* `inner_shift_left` : `⟨τ_s h, x⟩ = ∑_k conj(h[k - s]) x[k]` (filtering and subsampling).
* `filterBankAtoms h g` : the family `τ_{2n} h, τ_{2n} g` indexed by `Fin N ⊕ Fin N`.
* `perfect_reconstruction` : `x = ∑_n a[n] τ_{2n} h + ∑_n d[n] τ_{2n} g`.
* `norm_sq_eq_sum_add_sum` : `‖x‖² = ∑_n |a[n]|² + ∑_n |d[n]|²`.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace MathlibExt.Analysis.Wavelet.TwoChannelFilterBank

variable {N : ℕ}

/-- **Cyclic translate.** For a signal `x` on `ℤ / 2N`, `shift s x` is `k ↦ x[k - s]`. -/
def shift (s : ZMod (2 * N)) (x : EuclideanSpace ℂ (ZMod (2 * N))) :
    EuclideanSpace ℂ (ZMod (2 * N)) :=
  WithLp.toLp 2 fun k => x (k - s)

@[simp]
theorem shift_apply (s : ZMod (2 * N)) (x : EuclideanSpace ℂ (ZMod (2 * N))) (k : ZMod (2 * N)) :
    shift s x k = x (k - s) := rfl

variable [NeZero N]

instance : NeZero (2 * N) := ⟨by have := NeZero.ne N; omega⟩

/-- **Filtering and subsampling as an inner product.** `⟨τ_s h, x⟩ = ∑_k conj(h[k - s]) x[k]`;
at `s = 2n` this is the analysis coefficient `(x ⋆ h̄)[2n]` of the two-channel filter bank,
with `h̄[k] = conj(h[-k])` (Mallat, IEEE Trans. Pattern Anal. Mach. Intell. 11 (1989), the
pyramidal decomposition). -/
theorem inner_shift_left (s : ZMod (2 * N)) (h x : EuclideanSpace ℂ (ZMod (2 * N))) :
    ⟪shift s h, x⟫_ℂ = ∑ k, conj (h (k - s)) * x k := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

/-- **Atoms of the two-channel filter bank.** The even translates `τ_{2n} h` (low-pass) and
`τ_{2n} g` (high-pass), `0 ≤ n < N`, of two filters on `ℤ / 2N`. -/
def filterBankAtoms (h g : EuclideanSpace ℂ (ZMod (2 * N))) :
    Fin N ⊕ Fin N → EuclideanSpace ℂ (ZMod (2 * N)) :=
  Sum.elim (fun n => shift (2 * ((n : ℕ) : ZMod (2 * N))) h)
    (fun n => shift (2 * ((n : ℕ) : ZMod (2 * N))) g)

/-- **The atoms of an orthonormal filter bank form an orthonormal basis.** There are `2N` of
them in a space of dimension `2N`. -/
def filterBankBasis (h g : EuclideanSpace ℂ (ZMod (2 * N)))
    (hon : Orthonormal ℂ (filterBankAtoms h g)) :
    OrthonormalBasis (Fin N ⊕ Fin N) ℂ (EuclideanSpace ℂ (ZMod (2 * N))) :=
  OrthonormalBasis.mk hon
    (hon.linearIndependent.span_eq_top_of_card_eq_finrank' (by
      rw [finrank_euclideanSpace, ZMod.card, Fintype.card_sum, Fintype.card_fin]; ring)).ge

/-- **Perfect reconstruction of the orthogonal two-channel filter bank** (finite periodic
form of S. Mallat, *Multiresolution approximations and wavelet orthonormal bases of `L²(ℝ)`*,
Trans. Amer. Math. Soc. 315 (1989), Section 4, equations (65)–(68)). If the even translates
`τ_{2n} h, τ_{2n} g` (`0 ≤ n < N`) of two filters on `ℤ / 2N` are orthonormal, then every
signal is recovered from its subsampled filter outputs `a[n] = ⟨τ_{2n} h, x⟩` and
`d[n] = ⟨τ_{2n} g, x⟩`: `x = ∑_n a[n] τ_{2n} h + ∑_n d[n] τ_{2n} g`. -/
theorem perfect_reconstruction (h g : EuclideanSpace ℂ (ZMod (2 * N)))
    (hon : Orthonormal ℂ (filterBankAtoms h g)) (x : EuclideanSpace ℂ (ZMod (2 * N))) :
    x = ∑ n : Fin N, ⟪shift (2 * ((n : ℕ) : ZMod (2 * N))) h, x⟫_ℂ •
          shift (2 * ((n : ℕ) : ZMod (2 * N))) h +
        ∑ n : Fin N, ⟪shift (2 * ((n : ℕ) : ZMod (2 * N))) g, x⟫_ℂ •
          shift (2 * ((n : ℕ) : ZMod (2 * N))) g := by
  have := (filterBankBasis h g hon).sum_repr' x
  rw [Fintype.sum_sum_type] at this
  simpa [filterBankBasis, filterBankAtoms] using this.symm

/-- **Energy conservation of the orthogonal two-channel filter bank** (finite periodic form of
the orthogonality of the decomposition in S. Mallat, Trans. Amer. Math. Soc. 315 (1989),
Section 4, the identity after (65)). Under the hypothesis of `perfect_reconstruction`,
`‖x‖² = ∑_n |⟨τ_{2n} h, x⟩|² + ∑_n |⟨τ_{2n} g, x⟩|²`. -/
theorem norm_sq_eq_sum_add_sum (h g : EuclideanSpace ℂ (ZMod (2 * N)))
    (hon : Orthonormal ℂ (filterBankAtoms h g)) (x : EuclideanSpace ℂ (ZMod (2 * N))) :
    ‖x‖ ^ 2 = ∑ n : Fin N, ‖⟪shift (2 * ((n : ℕ) : ZMod (2 * N))) h, x⟫_ℂ‖ ^ 2 +
        ∑ n : Fin N, ‖⟪shift (2 * ((n : ℕ) : ZMod (2 * N))) g, x⟫_ℂ‖ ^ 2 := by
  have := (filterBankBasis h g hon).sum_sq_norm_inner_right x
  rw [Fintype.sum_sum_type] at this
  simpa [filterBankBasis, filterBankAtoms] using this.symm

/-! ### Conjugate mirror filters: the high-pass filter from the low-pass filter -/

/-- **Parity sign.** The sign `(-1)^k` on `ℤ / 2N`, computed from the representative of `k` in
`{0, …, 2N - 1}`; it is multiplicative because `2N` is even. -/
def paritySign (k : ZMod (2 * N)) : ℂ := (-1) ^ k.val

theorem paritySign_add (a b : ZMod (2 * N)) :
    paritySign (a + b) = paritySign a * paritySign b := by
  unfold paritySign
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) (2 * N)]
  rw [pow_add, pow_mul, pow_mul]
  simp

omit [NeZero N] in
theorem paritySign_sq (a : ZMod (2 * N)) : paritySign a * paritySign a = 1 := by
  unfold paritySign
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem paritySign_two_mul (e : ZMod (2 * N)) : paritySign (2 * e) = 1 := by
  rw [two_mul, paritySign_add, paritySign_sq]

theorem paritySign_neg (a : ZMod (2 * N)) : paritySign (-a) = paritySign a := by
  have h1 : paritySign a * paritySign (-a) = 1 := by
    rw [← paritySign_add, add_neg_cancel]; simp [paritySign]
  calc paritySign (-a) = paritySign a * paritySign a * paritySign (-a) := by
        rw [paritySign_sq, one_mul]
    _ = paritySign a := by rw [mul_assoc, h1, mul_one]

theorem paritySign_one : paritySign (1 : ZMod (2 * N)) = -1 := by
  have : Fact (1 < 2 * N) := ⟨by have := NeZero.ne N; omega⟩
  simp [paritySign, ZMod.val_one]

omit [NeZero N] in
theorem conj_paritySign (a : ZMod (2 * N)) : conj (paritySign a) = paritySign a := by
  simp [paritySign]

/-- **Mirror high-pass filter.** `mirrorFilter h k = (-1)^{1-k} conj(h[1 - k])`: the
time-domain form, on `ℤ / 2N`, of the choice `G(ω) = e^{-iω} conj(H(ω + π))` of S. Mallat,
*Multiresolution approximations and wavelet orthonormal bases of `L²(ℝ)`*, Trans. Amer. Math.
Soc. 315 (1989), equation (69), where `H(ω) = ∑ h_k e^{-ikω}` and `G(ω) = ∑ g_k e^{-ikω}`. -/
def mirrorFilter (h : EuclideanSpace ℂ (ZMod (2 * N))) : EuclideanSpace ℂ (ZMod (2 * N)) :=
  WithLp.toLp 2 fun k => paritySign (1 - k) * conj (h (1 - k))

theorem mirrorFilter_apply (h : EuclideanSpace ℂ (ZMod (2 * N))) (k : ZMod (2 * N)) :
    mirrorFilter h k = -(paritySign k * conj (h (1 - k))) := by
  simp only [mirrorFilter, sub_eq_add_neg, paritySign_add, paritySign_one, paritySign_neg]
  ring

/-- **Inner product of two translates.** `⟨τ_s x, τ_t y⟩ = ∑_k conj(x[k]) y[k + s - t]`, a value
of the cross-correlation of `x` and `y`. -/
theorem inner_shift_shift (s t : ZMod (2 * N)) (x y : EuclideanSpace ℂ (ZMod (2 * N))) :
    ⟪shift s x, shift t y⟫_ℂ = ∑ k, conj (x k) * y (k + s - t) := by
  rw [inner_shift_left]
  refine Fintype.sum_equiv (Equiv.subRight s) _ _ fun k => ?_
  simp [sub_add_cancel]

theorem inner_shift_mirror_mirror (h : EuclideanSpace ℂ (ZMod (2 * N))) (e : ZMod (2 * N)) :
    ∑ k, conj (mirrorFilter h k) * mirrorFilter h (k + 2 * e) =
      ∑ k, conj (h k) * h (k + 2 * e) := by
  have hterm : ∀ k, conj (mirrorFilter h k) * mirrorFilter h (k + 2 * e) =
      h (1 - k) * conj (h (1 - k - 2 * e)) := by
    intro k
    rw [mirrorFilter_apply, mirrorFilter_apply, paritySign_add, paritySign_two_mul,
      show (1 : ZMod (2 * N)) - (k + 2 * e) = 1 - k - 2 * e by ring]
    simp only [map_neg, map_mul, conj_paritySign, Complex.conj_conj, mul_one]
    have := paritySign_sq k
    linear_combination (h (1 - k) * conj (h (1 - k - 2 * e))) * this
  simp only [hterm]
  refine Fintype.sum_equiv (Equiv.subLeft (1 - 2 * e)) _ _ fun k => ?_
  simp only [Equiv.subLeft_apply]
  rw [show (1 : ZMod (2 * N)) - 2 * e - k + 2 * e = 1 - k by ring,
    show (1 : ZMod (2 * N)) - k - 2 * e = 1 - 2 * e - k by ring, mul_comm]

theorem inner_shift_self_mirror (h : EuclideanSpace ℂ (ZMod (2 * N))) (e : ZMod (2 * N)) :
    ∑ k, conj (h k) * mirrorFilter h (k + 2 * e) = 0 := by
  set c : ZMod (2 * N) := 1 - 2 * e
  have hterm : ∀ k, conj (h k) * mirrorFilter h (k + 2 * e) =
      -(paritySign k * (conj (h k) * conj (h (c - k)))) := by
    intro k
    rw [mirrorFilter_apply, paritySign_add, paritySign_two_mul,
      show (1 : ZMod (2 * N)) - (k + 2 * e) = c - k by simp only [c]; ring]
    ring
  simp only [hterm, Finset.sum_neg_distrib, neg_eq_zero]
  set S := ∑ k, paritySign k * (conj (h k) * conj (h (c - k)))
  have hinv : S = -S := by
    conv_lhs => rw [show S = ∑ k, paritySign (c - k) * (conj (h (c - k)) * conj (h (c - (c - k))))
      from (Fintype.sum_equiv (Equiv.subLeft c) _ _ fun k => rfl).symm]
    simp only [sub_sub_cancel, S, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sub_eq_add_neg c k, paritySign_add, paritySign_neg]
    simp only [c, sub_eq_add_neg, paritySign_add, paritySign_one, paritySign_neg,
      paritySign_two_mul]
    ring
  have h2 : (2 : ℂ) * S = 0 := by linear_combination hinv
  simpa using h2

/-- **Conjugate mirror filters give an orthonormal two-channel filter bank** (finite periodic
form of S. Mallat, *Multiresolution approximations and wavelet orthonormal bases of `L²(ℝ)`*,
Trans. Amer. Math. Soc. 315 (1989), Section 4, equations (66)–(69)). If the even translates
`τ_{2n} h` (`0 ≤ n < N`) of a filter `h` on `ℤ / 2N` are orthonormal, then with the mirror
filter `g[k] = (-1)^{1-k} conj(h[1 - k])` of (69) the whole family `τ_{2n} h, τ_{2n} g` is
orthonormal, so `perfect_reconstruction` applies. -/
theorem orthonormal_filterBankAtoms_mirrorFilter (h : EuclideanSpace ℂ (ZMod (2 * N)))
    (hh : Orthonormal ℂ fun n : Fin N => shift (2 * ((n : ℕ) : ZMod (2 * N))) h) :
    Orthonormal ℂ (filterBankAtoms h (mirrorFilter h)) := by
  rw [orthonormal_iff_ite] at hh ⊢
  have hgg : ∀ m n : Fin N,
      ⟪shift (2 * ((m : ℕ) : ZMod (2 * N))) (mirrorFilter h),
        shift (2 * ((n : ℕ) : ZMod (2 * N))) (mirrorFilter h)⟫_ℂ =
      ⟪shift (2 * ((m : ℕ) : ZMod (2 * N))) h, shift (2 * ((n : ℕ) : ZMod (2 * N))) h⟫_ℂ := by
    intro m n
    rw [inner_shift_shift, inner_shift_shift]
    simp only [show ∀ k : ZMod (2 * N), k + 2 * ((m : ℕ) : ZMod (2 * N)) -
        2 * ((n : ℕ) : ZMod (2 * N)) =
        k + 2 * (((m : ℕ) : ZMod (2 * N)) - ((n : ℕ) : ZMod (2 * N))) from fun k => by ring]
    exact inner_shift_mirror_mirror h _
  have hhg : ∀ m n : Fin N,
      ⟪shift (2 * ((m : ℕ) : ZMod (2 * N))) h,
        shift (2 * ((n : ℕ) : ZMod (2 * N))) (mirrorFilter h)⟫_ℂ = 0 := by
    intro m n
    rw [inner_shift_shift]
    simp only [show ∀ k : ZMod (2 * N), k + 2 * ((m : ℕ) : ZMod (2 * N)) -
        2 * ((n : ℕ) : ZMod (2 * N)) =
        k + 2 * (((m : ℕ) : ZMod (2 * N)) - ((n : ℕ) : ZMod (2 * N))) from fun k => by ring]
    exact inner_shift_self_mirror h _
  rintro (m | m) (n | n)
  · simpa [filterBankAtoms] using hh m n
  · simpa [filterBankAtoms] using hhg m n
  · simp only [filterBankAtoms, Sum.elim_inr, Sum.elim_inl, reduceCtorEq, ↓reduceIte]
    rw [← inner_conj_symm, hhg n m, map_zero]
  · simpa [filterBankAtoms, hgg] using hh m n

end MathlibExt.Analysis.Wavelet.TwoChannelFilterBank
