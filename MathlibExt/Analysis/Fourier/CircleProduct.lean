/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Adapted from arnovich/gimle-forseti, commit
d5239d8f0ebbc12b11616a1e3ce0228203fd231f,
`docs/spikes/353-scout-ks/round7/KSProjection/Product.lean`. Author: arnovich.

MIT License

Copyright (c) 2025 Gimle Labs

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import Mathlib.Analysis.Fourier.AddCircle
/-!
# Fourier modulation and circle correlation

Multiplication by a character shifts Fourier coefficients. The Hilbert-basis
identity then gives the unconditionally convergent correlation series for a
continuous circle function, without assuming absolute convergence of its
Fourier expansion.
-/
@[expose] public section
namespace AddCircle
open Complex MeasureTheory Set
open scoped ComplexConjugate
/-- Multiplication by a character shifts the Fourier coefficient index. -/
theorem fourierCoeff_modulate {T : ℝ} [Fact (0 < T)]
    (F : C(AddCircle T, ℂ)) (n m : ℤ) :
    fourierCoeff ((fourier (-n) * F : C(AddCircle T, ℂ))) m =
      fourierCoeff F (m + n) := by
  unfold fourierCoeff
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [ContinuousMap.mul_apply, smul_eq_mul, neg_add, fourier_add]
  ring

/-- The Fourier correlation series of a continuous circle field converges to the
coefficient of its squared modulus.  Convergence comes from the Hilbert basis. -/
theorem circle_correlation_hasSum {T : ℝ} [Fact (0 < T)]
    (F : C(AddCircle T, ℂ)) (n : ℤ) :
    HasSum (fun m : ℤ => conj (fourierCoeff F m) * fourierCoeff F (m + n))
      (fourierCoeff (fun t => conj (F t) * F t) n) := by
  let G : C(AddCircle T, ℂ) := fourier (-n) * F
  let X : Lp ℂ 2 haarAddCircle := ContinuousMap.toLp 2 haarAddCircle ℂ F
  let Y : Lp ℂ 2 haarAddCircle := ContinuousMap.toLp 2 haarAddCircle ℂ G
  have hb (z : Lp ℂ 2 (@haarAddCircle T _)) (m : ℤ) :
      inner ℂ (fourierBasis m) z = fourierCoeff z m := by
    rw [← HilbertBasis.repr_apply_apply, fourierBasis_repr]
  have hx (m : ℤ) : fourierCoeff X m = fourierCoeff F m :=
    fourierCoeff_toLp F m
  have hy (m : ℤ) : fourierCoeff Y m = fourierCoeff F (m + n) := by
    rw [show fourierCoeff Y m = fourierCoeff G m from fourierCoeff_toLp G m]
    exact fourierCoeff_modulate F n m
  have hm (m : ℤ) :
      inner ℂ X (fourierBasis m) * inner ℂ (fourierBasis m) Y =
        conj (fourierCoeff F m) * fourierCoeff F (m + n) := by
    rw [← inner_conj_symm X (fourierBasis m), hb, hb, hx, hy]
  have hi : inner ℂ X Y = fourierCoeff (fun t => conj (F t) * F t) n := by
    rw [MeasureTheory.L2.inner_def, fourierCoeff]
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) haarAddCircle F,
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) haarAddCircle G] with t hxt hyt
    change X t = F t at hxt
    change Y t = G t at hyt
    rw [hxt, hyt]
    simp only [RCLike.inner_apply', G, ContinuousMap.mul_apply, smul_eq_mul]
    ring
  simpa only [hm, hi] using fourierBasis.hasSum_inner_mul_inner X Y

end AddCircle
