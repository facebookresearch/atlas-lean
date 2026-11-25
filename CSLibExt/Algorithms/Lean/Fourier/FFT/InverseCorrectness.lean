/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.Inverse
public import CSLibExt.Algorithms.Lean.Fourier.FFT.DFTCorrectness
public import Mathlib.Algebra.Star.BigOperators
public import Init.Data.Vector.Lemmas

/-!
# Correctness of the executed conjugate/FFT/conjugate/normalize procedure

Every equality below concerns the actual returned Vector. The proof transports
the complete executed FFT coefficient sum through the canonical star ring
automorphism. The source normalization remains the explicitly executed scale.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

open MathlibExt.Analysis.Fourier.FastFourierTransformWanted

private theorem fft_star_primitive (d : Nat) (omega : ℂ)
    (hroot : IsPrimitiveRoot omega (2 ^ d)) :
    IsPrimitiveRoot (star omega) (2 ^ d) := by
  exact hroot.map_of_injective (f := (starRingAut : ℂ ≃+* ℂ))
    (starRingAut : ℂ ≃+* ℂ).injective

private theorem fftConjugate_sample {n : Nat} (xs : Vector ℂ n)
    (j : Nat) (hj : j < n) :
    (fftConjugate xs).ret.toArray.getD j 0 = star (xs.toArray.getD j 0) := by
  change (xs.map star).toArray.getD j 0 = star (xs.toArray.getD j 0)
  rw [← Array.getElem_eq_getD (h := by simpa using hj) 0,
    ← Array.getElem_eq_getD (h := by simpa using hj) 0]
  exact Vector.getElem_map star hj

/-- **Conjugating around the FFT conjugates the root.** Let $N = 2^d$, let $\omega \in \mathbb{C}$
be a primitive $N$-th root of unity and let $x \in \mathbb{C}^N$. Conjugating every entry of $x$,
running the FFT procedure with root $\omega$ and conjugating every entry of the result gives the
same vector as running the FFT procedure on $x$ with root $\overline{\omega}$. -/
theorem fft_conjugate_ret (d : Nat) (omega : ℂ)
    (hroot : IsPrimitiveRoot omega (2 ^ d)) (xs : Vector ℂ (2 ^ d)) :
    (fftConjugate (fft d omega (fftConjugate xs).ret).ret).ret =
      (fft d (star omega) xs).ret := by
  apply Vector.ext
  intro k hk
  change ((fft d omega (fftConjugate xs).ret).ret.map star)[k] =
    (fft d (star omega) xs).ret[k]
  rw [Vector.getElem_map]
  rw [fft_correct d omega hroot (fftConjugate xs).ret ⟨k, hk⟩,
    fft_correct d (star omega) (fft_star_primitive d omega hroot) xs ⟨k, hk⟩]
  unfold dftSum
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j < 2 ^ d := Finset.mem_range.mp hj
  dsimp only
  rw [fftConjugate_sample xs j hjn]
  simp only [star_mul, star_star, star_pow]
  exact mul_comm _ _

/-- **The inverse FFT is a normalized FFT at the conjugate root.** Let $N = 2^d$, let
$\omega \in \mathbb{C}$ be a primitive $N$-th root of unity and let $x \in \mathbb{C}^N$. The
output of the inverse FFT procedure on $x$ with root $\omega$ is the output of the FFT procedure
on $x$ with root $\overline{\omega}$ with every entry multiplied by $N^{-1}$. -/
theorem ifft_ret (d : Nat) (omega : ℂ)
    (hroot : IsPrimitiveRoot omega (2 ^ d)) (xs : Vector ℂ (2 ^ d)) :
    (ifft d omega xs).ret =
      (fft d (star omega) xs).ret.map (fun x => (2 ^ d : ℂ)⁻¹ * x) := by
  change (fftConjugate (fft d omega (fftConjugate xs).ret).ret).ret.map
      (fun x => ((2 ^ d : Nat) : ℂ)⁻¹ * x) = _
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [fft_conjugate_ret d omega hroot xs]

/-- **Correctness of the inverse FFT.** Let $N = 2^d$, let $\omega \in \mathbb{C}$ be a primitive
$N$-th root of unity and let $x \in \mathbb{C}^N$. For every $k < N$, entry $k$ of the output of
the inverse FFT procedure on $x$ with root $\omega$ equals $N^{-1}$ times the discrete Fourier sum
of length $N$ with root $\overline{\omega}$ at frequency $k$ of the sequence $j \mapsto x_j$ (set
to $0$ for $j \ge N$), that is, $N^{-1} \sum_{j=0}^{N-1} \overline{\omega}^{jk} x_j$. -/
theorem ifft_correct (d : Nat) (omega : ℂ)
    (hroot : IsPrimitiveRoot omega (2 ^ d)) (xs : Vector ℂ (2 ^ d))
    (k : Fin (2 ^ d)) :
    (ifft d omega xs).ret[k.val] =
      (2 ^ d : ℂ)⁻¹ *
        dftSum (2 ^ d) (star omega) (fun j => xs.toArray.getD j 0) k.val := by
  rw [ifft_ret d omega hroot xs, Vector.getElem_map]
  rw [fft_correct d (star omega) (fft_star_primitive d omega hroot) xs k]

end Cslib.Algorithms.Lean.TimeM
