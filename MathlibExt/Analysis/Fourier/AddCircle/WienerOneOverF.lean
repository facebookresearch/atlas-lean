/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval.Analysis.WienerOneOverF` in leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e (manifest
`manifests/problems/wiener_inverse_closed.toml`, rev 1, submitter Kim Morrison,
status archived), licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0); lean-eval ships no `NOTICE` file.
The adapted portions are the definition `InWienerAlgebra` and the statement of
`wiener_inverse_closed` only; the proof is new.
-/

module

public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.Analysis.Normed.Order.Hom.Basic
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import MathlibExt.Analysis.Fourier.AddCircle.FourierUniqueness
public import MathlibExt.Analysis.Fourier.AddCircle.RiemannLebesgue

@[expose] public section

namespace MathlibExt.Analysis.WienerOneOverFWanted
namespace Analysis.WienerOneOverF

/-!
# Wiener's `1/f` theorem

§226 of Oliver Knill's *Some Fundamental Theorems in Mathematics*. Wiener's
lemma for the circle algebra: if a continuous function on the circle has
absolutely summable Fourier coefficients and is nowhere zero, then its
pointwise inverse again has absolutely summable Fourier coefficients.

mathlib has the additive circle, the Fourier characters `fourier`, Fourier
coefficients `fourierCoeff`, and `hasSum_fourier_series_of_summable`, but not
the Wiener algebra or the spectral-invariance theorem. This module builds the
Wiener algebra as a commutative Banach algebra and proves the
spectral-invariance theorem `wiener_inverse_closed` by classifying the
characters of the algebra: every character is evaluation at a point of the
circle, so a nowhere-zero function has `0` outside its spectrum and is a unit
in the algebra.

## Main results

* `InWienerAlgebra`: a continuous function on the circle lies in the Wiener
  algebra when its Fourier coefficients are summable.
* `wiener_inverse_closed`: a nowhere-zero function in the Wiener algebra has
  a pointwise inverse in the Wiener algebra.
-/

open Filter Topology

open MathlibExt.Analysis.Fourier.AddCircle.FourierUniqueness

noncomputable section

variable {T : ℝ} [Fact (0 < T)]

set_option linter.dupNamespace false in
/-- **Functions with absolutely convergent Fourier series.** Let $T > 0$. A continuous function
$f : \mathbb{R}/T\mathbb{Z} \to \mathbb{C}$ lies in the Wiener algebra when the family of its
Fourier coefficients $\hat f(n) = \frac{1}{T} \int_0^T f(x) e^{-2\pi i n x / T} \, dx$,
$n \in \mathbb{Z}$, is summable in $\mathbb{C}$.

For complex families, summability is equivalent to
$\sum_{n \in \mathbb{Z}} |\hat f(n)| < \infty$. -/
def InWienerAlgebra (f : C(AddCircle T, ℂ)) : Prop :=
  Summable (fourierCoeff f)

/-- The fiber of the addition map `ℤ × ℤ → ℤ` over `n`: the pairs `(k, j)`
with `k + j = n`. -/
private abbrev fiberSet (n : ℤ) : Set (ℤ × ℤ) :=
  (fun p : ℤ × ℤ => p.1 + p.2) ⁻¹' {n}

/-- Reindexing a fiber of the addition map by its first coordinate. -/
private def fiberEquiv (n : ℤ) : fiberSet n ≃ ℤ where
  toFun p := p.1.1
  invFun k := ⟨(k, n - k), by simp [fiberSet]⟩
  left_inv p := by
    obtain ⟨⟨k, j⟩, hj⟩ := p
    have hj' : k + j = n := hj
    apply Subtype.ext
    simp only
    congr 1
    omega
  right_inv k := rfl

/-- A sum over a fiber of the addition map is a sum over the first
coordinate. -/
private theorem fiber_tsum_eq {F : ℤ × ℤ → ℂ} (n : ℤ) :
    (∑' b : fiberSet n, F b.1) = ∑' k, F (k, n - k) := by
  have hcongr : (∑' b : fiberSet n, F b.1)
      = ∑' b : fiberSet n, F (b.1.1, n - b.1.1) := by
    apply tsum_congr
    intro b
    obtain ⟨⟨k, j⟩, hj⟩ := b
    have hj' : k + j = n := hj
    change F (k, j) = F (k, n - k)
    rw [show (k, n - k) = (k, j) from Prod.ext rfl (by omega)]
  calc (∑' b : fiberSet n, F b.1)
      = ∑' b : fiberSet n, F (b.1.1, n - b.1.1) := hcongr
    _ = ∑' k, F (k, n - k) := (fiberEquiv n).tsum_eq (fun k => F (k, n - k))

/-- The real-valued version of `fiber_tsum_eq`. -/
private theorem fiber_tsum_eq_real {F : ℤ × ℤ → ℝ} (n : ℤ) :
    (∑' b : fiberSet n, F b.1) = ∑' k, F (k, n - k) := by
  have hcongr : (∑' b : fiberSet n, F b.1)
      = ∑' b : fiberSet n, F (b.1.1, n - b.1.1) := by
    apply tsum_congr
    intro b
    obtain ⟨⟨k, j⟩, hj⟩ := b
    have hj' : k + j = n := hj
    change F (k, j) = F (k, n - k)
    rw [show (k, n - k) = (k, j) from Prod.ext rfl (by omega)]
  calc (∑' b : fiberSet n, F b.1)
      = ∑' b : fiberSet n, F (b.1.1, n - b.1.1) := hcongr
    _ = ∑' k, F (k, n - k) := (fiberEquiv n).tsum_eq (fun k => F (k, n - k))

/-- The norms of the terms of a convolution fiber are summable. -/
private theorem summable_norm_conv_inner {a b : ℤ → ℂ}
    (ha : Summable fun n => ‖a n‖) (hb : Summable fun n => ‖b n‖) (n : ℤ) :
    Summable fun k => ‖a k‖ * ‖b (n - k)‖ := by
  have hB : ∀ k, ‖b (n - k)‖ ≤ ∑' j, ‖b j‖ :=
    fun k => hb.le_tsum (n - k) (fun _ _ => norm_nonneg _)
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun k => mul_le_mul_of_nonneg_left (hB k) (norm_nonneg _)) ?_
  simpa using ha.mul_right (∑' j, ‖b j‖)

/-- The terms of a convolution fiber are summable. -/
private theorem summable_conv_fiber {a b : ℤ → ℂ}
    (ha : Summable fun n => ‖a n‖) (hb : Summable fun n => ‖b n‖) (n : ℤ) :
    Summable fun k => a k * b (n - k) := by
  have hnorm : Summable fun k => ‖a k * b (n - k)‖ := by
    have hB : ∀ k, ‖b (n - k)‖ ≤ ∑' j, ‖b j‖ :=
      fun k => hb.le_tsum (n - k) (fun _ _ => norm_nonneg _)
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => norm_mul_le _ _)
      (Summable.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (fun k => mul_le_mul_of_nonneg_left (hB k) (norm_nonneg _))
        (by simpa using ha.mul_right (∑' j, ‖b j‖)))
  exact hnorm.of_norm

/-- The convolution of two absolutely summable families has a sum: the
convolution sums, over `n`, give the product of the sums. -/
private theorem hasSum_conv {a b : ℤ → ℂ}
    (ha : Summable fun n => ‖a n‖) (hb : Summable fun n => ‖b n‖) :
    HasSum (fun n => ∑' k, a k * b (n - k)) ((∑' n, a n) * ∑' n, b n) := by
  have hF : Summable fun p : ℤ × ℤ => a p.1 * b p.2 :=
    summable_mul_of_summable_norm ha hb
  have hsum : HasSum (fun p : ℤ × ℤ => a p.1 * b p.2) ((∑' n, a n) * ∑' n, b n) := by
    rw [tsum_mul_tsum_of_summable_norm ha hb]
    exact hF.hasSum
  have hfib := hsum.tsum_fiberwise (fun p : ℤ × ℤ => p.1 + p.2)
  refine hfib.congr_fun fun n => ?_
  exact (fiber_tsum_eq (n := n) (F := fun p : ℤ × ℤ => a p.1 * b p.2)).symm

/-- The convolution of two absolutely summable families is summable. -/
private theorem summable_conv {a b : ℤ → ℂ}
    (ha : Summable fun n => ‖a n‖) (hb : Summable fun n => ‖b n‖) :
    Summable fun n => ∑' k, a k * b (n - k) :=
  (hasSum_conv ha hb).summable

/-- The norm of a norm is the norm, for real numbers. -/
private theorem norm_summable_of_norm {a : ℤ → ℂ} (ha : Summable fun n => ‖a n‖) :
    Summable fun n => ‖(‖a n‖ : ℝ)‖ := by
  simpa only [norm_norm] using ha

/-- The norms of the convolution sums are summable. -/
private theorem summable_norm_conv {a b : ℤ → ℂ}
    (ha : Summable fun n => ‖a n‖) (hb : Summable fun n => ‖b n‖) :
    Summable fun n => ‖∑' k, a k * b (n - k)‖ := by
  have hF : Summable fun p : ℤ × ℤ => ‖a p.1‖ * ‖b p.2‖ :=
    Summable.mul_of_nonneg ha hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hsum : HasSum (fun p : ℤ × ℤ => ‖a p.1‖ * ‖b p.2‖)
      ((∑' n, ‖a n‖) * ∑' n, ‖b n‖) := by
    have e := tsum_mul_tsum_of_summable_norm (f := fun n => ‖a n‖) (g := fun n => ‖b n‖)
      (norm_summable_of_norm ha) (norm_summable_of_norm hb)
    rw [e]
    exact hF.hasSum
  have hfib := hsum.tsum_fiberwise (fun p : ℤ × ℤ => p.1 + p.2)
  have hinner : HasSum (fun n => ∑' k, ‖a k‖ * ‖b (n - k)‖)
      ((∑' n, ‖a n‖) * ∑' n, ‖b n‖) := by
    refine hfib.congr_fun fun n => ?_
    exact (fiber_tsum_eq_real (n := n)
      (F := fun p : ℤ × ℤ => ‖a p.1‖ * ‖b p.2‖)).symm
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => (norm_tsum_le_tsum_norm (summable_conv_fiber ha hb n).norm).trans
      (Summable.tsum_le_tsum (fun k => norm_mul_le _ _)
        (summable_conv_fiber ha hb n).norm (summable_norm_conv_inner ha hb n)))
    hinner.summable

/-- The `ℓ¹` norm of a convolution is at most the product of the `ℓ¹` norms. -/
private theorem tsum_norm_conv_le {a b : ℤ → ℂ}
    (ha : Summable fun n => ‖a n‖) (hb : Summable fun n => ‖b n‖) :
    ∑' n, ‖∑' k, a k * b (n - k)‖ ≤ (∑' n, ‖a n‖) * ∑' n, ‖b n‖ := by
  have hF : Summable fun p : ℤ × ℤ => ‖a p.1‖ * ‖b p.2‖ :=
    Summable.mul_of_nonneg ha hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hsum : HasSum (fun p : ℤ × ℤ => ‖a p.1‖ * ‖b p.2‖)
      ((∑' n, ‖a n‖) * ∑' n, ‖b n‖) := by
    have e := tsum_mul_tsum_of_summable_norm (f := fun n => ‖a n‖) (g := fun n => ‖b n‖)
      (norm_summable_of_norm ha) (norm_summable_of_norm hb)
    rw [e]
    exact hF.hasSum
  have hinner : HasSum (fun n => ∑' k, ‖a k‖ * ‖b (n - k)‖)
      ((∑' n, ‖a n‖) * ∑' n, ‖b n‖) := by
    refine (hsum.tsum_fiberwise (fun p : ℤ × ℤ => p.1 + p.2)).congr_fun fun n => ?_
    exact (fiber_tsum_eq_real (n := n)
      (F := fun p : ℤ × ℤ => ‖a p.1‖ * ‖b p.2‖)).symm
  refine (Summable.tsum_le_tsum
    (fun n => (norm_tsum_le_tsum_norm (summable_conv_fiber ha hb n).norm).trans
      (Summable.tsum_le_tsum (fun k => norm_mul_le _ _)
        (summable_conv_fiber ha hb n).norm (summable_norm_conv_inner ha hb n)))
    (summable_norm_conv ha hb) hinner.summable).trans_eq hinner.tsum_eq

/-- The Fourier coefficients of a product are the convolution of the
Fourier coefficients. -/
private theorem fourierCoeff_mul {f g : C(AddCircle T, ℂ)}
    (hf : Summable (fourierCoeff f)) (hg : Summable (fourierCoeff g)) :
    fourierCoeff (f * g) =
      fun n => ∑' k, fourierCoeff f k * fourierCoeff g (n - k) := by
  have ha : Summable fun n => ‖fourierCoeff f n‖ := hf.norm
  have hb : Summable fun n => ‖fourierCoeff g n‖ := hg.norm
  apply fourierCoeff_eq_of_hasSum_of_summable_norm (c :=
    fun n => ∑' k, fourierCoeff f k * fourierCoeff g (n - k))
  · intro x
    have hfn : ∀ m : ℤ, ‖fourier m x‖ = 1 := fun m => by
      rw [fourier_apply]
      exact Circle.norm_coe _
    have hfx : HasSum (fun m => fourierCoeff f m • fourier m x) (f x) :=
      has_pointwise_sum_fourier_series_of_summable hf x
    have hgx : HasSum (fun k => fourierCoeff g k • fourier k x) (g x) :=
      has_pointwise_sum_fourier_series_of_summable hg x
    have hnormF : Summable fun m => ‖fourierCoeff f m • fourier m x‖ := by
      simpa [norm_smul, hfn] using ha
    have hnormG : Summable fun k => ‖fourierCoeff g k • fourier k x‖ := by
      simpa [norm_smul, hfn] using hb
    have hpair : Summable fun p : ℤ × ℤ =>
        (fourierCoeff f p.1 • fourier p.1 x) * (fourierCoeff g p.2 • fourier p.2 x) :=
      (Summable.mul_norm hnormF hnormG).of_norm
    have hsum : HasSum (fun p : ℤ × ℤ =>
        (fourierCoeff f p.1 • fourier p.1 x) * (fourierCoeff g p.2 • fourier p.2 x))
        (f x * g x) := by
      have e := tsum_mul_tsum_of_summable_norm hnormF hnormG
      rw [hfx.tsum_eq, hgx.tsum_eq] at e
      rw [e]
      exact hpair.hasSum
    have hfib := hsum.tsum_fiberwise (fun p : ℤ × ℤ => p.1 + p.2)
    have hterm : ∀ (n k : ℤ),
        (fourierCoeff f k • fourier k x) * (fourierCoeff g (n - k) • fourier (n - k) x)
          = (fourierCoeff f k * fourierCoeff g (n - k)) • fourier n x := by
      intro n k
      rw [smul_eq_mul, smul_eq_mul, smul_eq_mul]
      have hfour : fourier k x * fourier (n - k) x = fourier n x := by
        calc fourier k x * fourier (n - k) x = fourier (k + (n - k)) x := fourier_add.symm
          _ = fourier n x := by rw [show k + (n - k) = n by omega]
      rw [← hfour]
      ring
    have hfiber : ∀ n : ℤ,
        HasSum (fun k => (fourierCoeff f k • fourier k x) *
          (fourierCoeff g (n - k) • fourier (n - k) x))
          ((∑' k, fourierCoeff f k * fourierCoeff g (n - k)) • fourier n x) := by
      intro n
      have h := (summable_conv_fiber ha hb n).hasSum.smul_const (fourier n x)
      refine h.congr_fun fun k => ?_
      rw [hterm]
    have hconv : HasSum (fun n => (∑' k, fourierCoeff f k * fourierCoeff g (n - k)) •
        fourier n x) (f x * g x) := by
      refine hfib.congr_fun fun n => ?_
      have h1 : (∑' b : fiberSet n, (fourierCoeff f b.1.1 • fourier b.1.1 x) *
          (fourierCoeff g b.1.2 • fourier b.1.2 x))
          = ∑' k, (fourierCoeff f k • fourier k x) *
            (fourierCoeff g (n - k) • fourier (n - k) x) :=
        fiber_tsum_eq (n := n) (F := fun p : ℤ × ℤ =>
          (fourierCoeff f p.1 • fourier p.1 x) *
            (fourierCoeff g p.2 • fourier p.2 x))
      exact (hfiber n).tsum_eq.symm.trans h1.symm
    refine hconv.congr_fun fun n => ?_
    rw [smul_eq_mul, smul_eq_mul, mul_comm]
  · exact summable_norm_conv ha hb

/-- A continuous function on the circle is integrable for Haar measure. -/
private theorem continuous_integrable (f : C(AddCircle T, ℂ)) :
    MeasureTheory.Integrable (⇑f) AddCircle.haarAddCircle :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Fourier coefficients are additive. -/
private theorem fourierCoeff_add' (f g : C(AddCircle T, ℂ)) :
    fourierCoeff (f + g) = fourierCoeff f + fourierCoeff g :=
  fourierCoeff.add (continuous_integrable f) (continuous_integrable g)

/-- Fourier coefficients are homogeneous for complex scalars. -/
private theorem fourierCoeff_smul' (c : ℂ) (f : C(AddCircle T, ℂ)) (n : ℤ) :
    fourierCoeff (c • f) n = c • fourierCoeff f n :=
  fourierCoeff.const_smul (⇑f) c n

/-- Fourier coefficients change sign under negation. -/
private theorem fourierCoeff_neg' (f : C(AddCircle T, ℂ)) (n : ℤ) :
    fourierCoeff (-f) n = -fourierCoeff f n := by
  have h0 : fourierCoeff (0 : C(AddCircle T, ℂ)) n = 0 := by
    simp [fourierCoeff]
  have h := congr_fun (fourierCoeff_add' f (-f)) n
  simp only [Pi.add_apply] at h
  rw [add_neg_cancel, h0] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- A Fourier coefficient is bounded by the sup norm. -/
private theorem norm_fourierCoeff_le (f : C(AddCircle T, ℂ)) (n : ℤ) :
    ‖fourierCoeff f n‖ ≤ ‖f‖ := by
  have h1 :=
    MathlibExt.Analysis.Fourier.AddCircle.RiemannLebesgue.norm_fourierCoeff_le_integral_norm
      (f := (⇑f)) n
  refine h1.trans ?_
  have h2 : ∫ t : AddCircle T, ‖f t‖ ∂AddCircle.haarAddCircle ≤ ‖f‖ := by
    have hmono : ∫ t : AddCircle T, ‖f t‖ ∂AddCircle.haarAddCircle
        ≤ ∫ _ : AddCircle T, ‖f‖ ∂AddCircle.haarAddCircle :=
      MeasureTheory.integral_mono_ae
        (f.continuous.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (MeasureTheory.integrable_const _)
        (Filter.Eventually.of_forall fun t => ContinuousMap.norm_coe_le_norm f t)
    simpa using hmono
  exact h2

/-- Fourier coefficients are subtractive. -/
private theorem fourierCoeff_sub' (f g : C(AddCircle T, ℂ)) (n : ℤ) :
    fourierCoeff (f - g) n = fourierCoeff f n - fourierCoeff g n := by
  calc fourierCoeff (f - g) n
      = fourierCoeff f n + fourierCoeff (-g) n := by
        rw [sub_eq_add_neg]
        exact congr_fun (fourierCoeff_add' f (-g)) n
    _ = fourierCoeff f n - fourierCoeff g n := by
        rw [fourierCoeff_neg', sub_eq_add_neg]

/-- Constant functions lie in the Wiener algebra. -/
private theorem wiener_mem_algebraMap (c : ℂ) :
    InWienerAlgebra (algebraMap ℂ C(AddCircle T, ℂ) c) := by
  have hfun : (⇑(algebraMap ℂ C(AddCircle T, ℂ) c) : AddCircle T → ℂ) = fun _ => c := rfl
  change Summable (fourierCoeff (⇑(algebraMap ℂ C(AddCircle T, ℂ) c)))
  rw [hfun, fourierCoeff_const]
  apply summable_of_ne_finset_zero (s := {0})
  intro b hb
  by_cases h : b = 0
  · exact absurd (Finset.mem_singleton.mpr h) hb
  · exact Pi.single_eq_of_ne (M := fun _ : ℤ => ℂ) h c

/-- The Wiener algebra, as a subalgebra of the continuous functions on the
circle: the functions with summable Fourier coefficients. This subalgebra
only supplies the ring operations; the normed structure is built on the
wrapper `WienerAlgebra` below, which has no competing norm instances. -/
private def wienerSubalgebra : Subalgebra ℂ C(AddCircle T, ℂ) where
  carrier := {f | InWienerAlgebra f}
  mul_mem' := by
    intro f g hf hg
    change Summable (fourierCoeff (f * g))
    rw [fourierCoeff_mul hf hg]
    exact summable_conv hf.norm hg.norm
  add_mem' := by
    intro f g hf hg
    change Summable (fourierCoeff (f + g))
    rw [fourierCoeff_add']
    exact hf.add hg
  algebraMap_mem' := by
    intro c
    exact wiener_mem_algebraMap c

/-- The Wiener algebra: a continuous function on the circle together with the
summability of its Fourier coefficients, bundled as a structure so that the
normed algebra structure below is the only one Lean can find on it. -/
private structure WienerAlgebra (T : ℝ) [Fact (0 < T)] where
  toSub : ↥(wienerSubalgebra (T := T))

/-- The underlying continuous function of an element of the Wiener algebra. -/
private def WienerAlgebra.toFun (a : WienerAlgebra T) : C(AddCircle T, ℂ) := a.toSub

private instance wienerCoe : Coe (WienerAlgebra T) C(AddCircle T, ℂ) :=
  ⟨WienerAlgebra.toFun⟩

/-- Extensionality for the Wiener algebra. -/
private theorem WienerAlgebra.ext {a b : WienerAlgebra T}
    (h : a.toFun = b.toFun) : a = b := by
  obtain ⟨x⟩ := a
  obtain ⟨y⟩ := b
  have hxy : x = y := Subtype.ext h
  cases hxy
  rfl

/-- The underlying function determines an element of the Wiener algebra. -/
private theorem wiener_toFun_injective :
    Function.Injective (fun a : WienerAlgebra T => a.toFun) :=
  fun _ _ h => WienerAlgebra.ext h

private noncomputable instance wienerZero : Zero (WienerAlgebra T) := ⟨⟨0⟩⟩
private noncomputable instance wienerOne : One (WienerAlgebra T) := ⟨⟨1⟩⟩
private noncomputable instance wienerAdd : Add (WienerAlgebra T) :=
  ⟨fun a b => ⟨a.toSub + b.toSub⟩⟩
private noncomputable instance wienerMul : Mul (WienerAlgebra T) :=
  ⟨fun a b => ⟨a.toSub * b.toSub⟩⟩
private noncomputable instance wienerNeg : Neg (WienerAlgebra T) := ⟨fun a => ⟨-a.toSub⟩⟩
private noncomputable instance wienerSub : Sub (WienerAlgebra T) :=
  ⟨fun a b => ⟨a.toSub - b.toSub⟩⟩
private noncomputable instance wienerNSMul : SMul ℕ (WienerAlgebra T) :=
  ⟨fun n a => ⟨n • a.toSub⟩⟩
private noncomputable instance wienerZSMul : SMul ℤ (WienerAlgebra T) :=
  ⟨fun n a => ⟨n • a.toSub⟩⟩
private noncomputable instance wienerPow : Pow (WienerAlgebra T) ℕ :=
  ⟨fun a n => ⟨a.toSub ^ n⟩⟩
private noncomputable instance wienerNatCast : NatCast (WienerAlgebra T) :=
  ⟨fun n => ⟨(n : ↥(wienerSubalgebra (T := T)))⟩⟩
private noncomputable instance wienerIntCast : IntCast (WienerAlgebra T) :=
  ⟨fun n => ⟨(n : ↥(wienerSubalgebra (T := T)))⟩⟩
private noncomputable instance wienerSMul : SMul ℂ (WienerAlgebra T) :=
  ⟨fun c a => ⟨c • a.toSub⟩⟩

/-- The underlying function of `0` is `0`. -/
private theorem wiener_toFun_zero : (0 : WienerAlgebra T).toFun = 0 := rfl

/-- The underlying function of `1` is `1`. -/
private theorem wiener_toFun_one : (1 : WienerAlgebra T).toFun = 1 := rfl

/-- The underlying function of a sum is the sum. -/
private theorem wiener_toFun_add (a b : WienerAlgebra T) :
    (a + b).toFun = a.toFun + b.toFun :=
  rfl

/-- The underlying function of a product is the product. -/
private theorem wiener_toFun_mul (a b : WienerAlgebra T) :
    (a * b).toFun = a.toFun * b.toFun :=
  rfl

/-- The underlying function of a negation is the negation. -/
private theorem wiener_toFun_neg (a : WienerAlgebra T) :
    (-a).toFun = -a.toFun := rfl

/-- The underlying function of a difference is the difference. -/
private theorem wiener_toFun_sub (a b : WienerAlgebra T) :
    (a - b).toFun = a.toFun - b.toFun :=
  rfl

/-- The underlying function of a natural-number multiple is the multiple. -/
private theorem wiener_toFun_nsmul (n : ℕ) (a : WienerAlgebra T) :
    (n • a).toFun = n • a.toFun :=
  AddSubmonoidClass.coe_nsmul a.toSub n

/-- The underlying function of an integer multiple is the multiple. -/
private theorem wiener_toFun_zsmul (n : ℤ) (a : WienerAlgebra T) :
    (n • a).toFun = n • a.toFun :=
  AddSubgroupClass.coe_zsmul a.toSub n

/-- The underlying function of a power is the power. -/
private theorem wiener_toFun_pow (a : WienerAlgebra T) (n : ℕ) :
    (a ^ n).toFun = a.toFun ^ n :=
  Subalgebra.coe_pow _ a.toSub n

/-- The underlying function of a natural-number cast is the cast. -/
private theorem wiener_toFun_natCast (n : ℕ) :
    (n : WienerAlgebra T).toFun = (n : C(AddCircle T, ℂ)) :=
  SubringClass.coe_natCast _ n

/-- The underlying function of an integer cast is the cast. -/
private theorem wiener_toFun_intCast (n : ℤ) :
    (n : WienerAlgebra T).toFun = (n : C(AddCircle T, ℂ)) :=
  SubringClass.coe_intCast _ n

/-- The underlying function of a complex scalar multiple is the multiple. -/
private theorem wiener_toFun_smul (c : ℂ) (a : WienerAlgebra T) :
    (c • a).toFun = c • a.toFun := by
  change ((c • a.toSub : ↥(wienerSubalgebra (T := T))) : C(AddCircle T, ℂ))
    = c • (a.toSub : C(AddCircle T, ℂ))
  ext x
  simp [Algebra.smul_def, smul_eq_mul]

/-- The Wiener algebra is an additive commutative group. -/
private instance wienerAddCommGroup : AddCommGroup (WienerAlgebra T) :=
  Function.Injective.addCommGroup (fun a : WienerAlgebra T => a.toFun)
    wiener_toFun_injective wiener_toFun_zero wiener_toFun_add wiener_toFun_neg
    wiener_toFun_sub (fun x n => wiener_toFun_nsmul n x)
    (fun x n => wiener_toFun_zsmul n x)

/-- The Wiener algebra is a commutative ring. -/
private instance wienerCommRing : CommRing (WienerAlgebra T) :=
  Function.Injective.commRing (fun a : WienerAlgebra T => a.toFun) wiener_toFun_injective
    wiener_toFun_zero wiener_toFun_one wiener_toFun_add wiener_toFun_mul wiener_toFun_neg
    wiener_toFun_sub wiener_toFun_nsmul wiener_toFun_zsmul wiener_toFun_pow
    wiener_toFun_natCast wiener_toFun_intCast

/-- The inclusion of the Wiener algebra in the continuous functions, as an
additive monoid homomorphism. -/
private def wienerToFunAddHom : WienerAlgebra T →+ C(AddCircle T, ℂ) where
  toFun a := a.toFun
  map_zero' := wiener_toFun_zero
  map_add' := wiener_toFun_add

/-- The Wiener algebra is a module over `ℂ`. -/
private instance wienerModule : Module ℂ (WienerAlgebra T) :=
  Function.Injective.module ℂ wienerToFunAddHom wiener_toFun_injective wiener_toFun_smul

/-- The embedding of `ℂ` in the Wiener algebra, as a ring homomorphism. -/
private def wienerAlgebraMap : ℂ →+* WienerAlgebra T where
  toFun c := ⟨⟨algebraMap ℂ C(AddCircle T, ℂ) c, wiener_mem_algebraMap c⟩⟩
  map_one' := by
    apply WienerAlgebra.ext
    exact map_one _
  map_mul' := by
    intro c d
    apply WienerAlgebra.ext
    exact map_mul _ _ _
  map_zero' := by
    apply WienerAlgebra.ext
    exact map_zero _
  map_add' := by
    intro c d
    apply WienerAlgebra.ext
    exact map_add _ _ _

/-- The underlying function of `wienerAlgebraMap c` is the constant function `c`. -/
private theorem wiener_toFun_algebraMap (c : ℂ) :
    (wienerAlgebraMap c).toFun = algebraMap ℂ C(AddCircle T, ℂ) c :=
  rfl

/-- The Wiener algebra is an algebra over `ℂ`. -/
private instance wienerAlgebra : Algebra ℂ (WienerAlgebra T) where
  algebraMap := wienerAlgebraMap
  commutes' c a := by
    apply WienerAlgebra.ext
    rw [wiener_toFun_mul, wiener_toFun_mul, wiener_toFun_algebraMap]
    rw [mul_comm]
  smul_def' c a := by
    apply WienerAlgebra.ext
    rw [wiener_toFun_smul, wiener_toFun_mul, wiener_toFun_algebraMap]
    rw [Algebra.smul_def]

/-- The Wiener norm: the `ℓ¹` norm of the Fourier coefficients. -/
private def wienerNorm : AddGroupNorm (WienerAlgebra T) where
  toFun a := ∑' n, ‖fourierCoeff (a.toFun) n‖
  map_zero' := by
    rw [wiener_toFun_zero]
    simp [fourierCoeff]
  add_le' := by
    intro a b
    have hcoeff : fourierCoeff ((a + b).toFun)
        = fourierCoeff a.toFun + fourierCoeff b.toFun :=
      fourierCoeff_add' _ _
    have hsum : Summable fun n => ‖fourierCoeff a.toFun n‖ + ‖fourierCoeff b.toFun n‖ :=
      a.toSub.2.norm.add b.toSub.2.norm
    calc ∑' n, ‖fourierCoeff ((a + b).toFun) n‖
        = ∑' n, ‖fourierCoeff a.toFun n + fourierCoeff b.toFun n‖ := by
          rw [hcoeff]
          rfl
      _ ≤ ∑' n, (‖fourierCoeff a.toFun n‖ + ‖fourierCoeff b.toFun n‖) :=
          Summable.tsum_le_tsum (fun n => norm_add_le _ _)
            (Summable.of_nonneg_of_le (fun n => norm_nonneg _)
              (fun n => norm_add_le _ _) hsum) hsum
      _ = _ := a.toSub.2.norm.tsum_add b.toSub.2.norm
  neg' := by
    intro a
    apply tsum_congr
    intro n
    rw [wiener_toFun_neg a, fourierCoeff_neg', norm_neg]
  eq_zero_of_map_eq_zero' := by
    intro a ha
    have hcoeff : ∀ n, fourierCoeff a.toFun n = 0 := by
      intro n
      have hle : ‖fourierCoeff a.toFun n‖ ≤ ∑' m, ‖fourierCoeff a.toFun m‖ :=
        a.toSub.2.norm.le_tsum n (fun _ _ => norm_nonneg _)
      rw [ha] at hle
      exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
    apply WienerAlgebra.ext
    exact eq_zero_of_fourierCoeff_eq_zero hcoeff

/-- The Wiener algebra with the `ℓ¹` norm of Fourier coefficients is a normed
additive commutative group. -/
private instance wienerNormedAddCommGroup :
    NormedAddCommGroup (WienerAlgebra T) :=
  AddGroupNormClass.toNormedAddCommGroup wienerNorm

/-- The Wiener norm is the `ℓ¹` norm of the Fourier coefficients. -/
private theorem wiener_norm_eq (a : WienerAlgebra T) :
    ‖a‖ = ∑' n, ‖fourierCoeff a.toFun n‖ :=
  AddGroupNormClass.toNormedAddCommGroup_norm_eq wienerNorm a

/-- The Wiener algebra is a normed space over `ℂ`. -/
private instance wienerNormedSpace : NormedSpace ℂ (WienerAlgebra T) where
  norm_smul_le := by
    intro c a
    have hcoeff : ∀ n, fourierCoeff ((c • a).toFun) n = c • fourierCoeff a.toFun n := by
      intro n
      rw [wiener_toFun_smul]
      exact fourierCoeff_smul' c _ n
    have heq : ‖c • a‖ = ‖c‖ * ‖a‖ := by
      calc ‖c • a‖
          = ∑' n, ‖fourierCoeff ((c • a).toFun) n‖ := wiener_norm_eq _
        _ = ∑' n, ‖c‖ * ‖fourierCoeff a.toFun n‖ := by
            apply tsum_congr
            intro n
            rw [hcoeff, norm_smul]
        _ = ‖c‖ * ∑' n, ‖fourierCoeff a.toFun n‖ := tsum_mul_left
        _ = ‖c‖ * ‖a‖ := by rw [wiener_norm_eq]
    exact heq.le

/-- The Wiener algebra is a normed commutative ring. -/
private instance wienerNormedCommRing : NormedCommRing (WienerAlgebra T) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le := by
    intro a b
    simp only [wiener_norm_eq]
    have hcoeff : fourierCoeff ((a * b).toFun)
        = fun n => ∑' k, fourierCoeff a.toFun k * fourierCoeff b.toFun (n - k) := by
      rw [wiener_toFun_mul]
      exact fourierCoeff_mul a.toSub.2 b.toSub.2
    rw [hcoeff]
    exact tsum_norm_conv_le a.toSub.2.norm b.toSub.2.norm

/-- The Wiener algebra is a normed algebra over `ℂ`. -/
private instance wienerNormedAlgebra : NormedAlgebra ℂ (WienerAlgebra T) where
  norm_smul_le := by
    intro c a
    exact (norm_smul c a).le

/-- A value of a continuous function is bounded by the `ℓ¹` norm of its
Fourier coefficients. -/
private theorem norm_apply_le_tsum_coeff (f : C(AddCircle T, ℂ)) (hf : InWienerAlgebra f)
    (x : AddCircle T) :
    ‖f x‖ ≤ ∑' n, ‖fourierCoeff f n‖ := by
  have hfn : ∀ m : ℤ, ‖fourier m x‖ = 1 := fun m => by
    rw [fourier_apply]
    exact Circle.norm_coe _
  have h := has_pointwise_sum_fourier_series_of_summable hf x
  rw [← h.tsum_eq]
  calc ‖∑' n, fourierCoeff f n • fourier n x‖
      ≤ ∑' n, ‖fourierCoeff f n • fourier n x‖ :=
        norm_tsum_le_tsum_norm (by simpa [norm_smul, hfn] using hf.norm)
    _ = ∑' n, ‖fourierCoeff f n‖ := by
        apply tsum_congr
        intro n
        rw [norm_smul, hfn, mul_one]

/-- A value of a Wiener function is bounded by its Wiener norm. -/
private theorem norm_apply_le_wiener_norm (a : WienerAlgebra T) (x : AddCircle T) :
    ‖a.toFun x‖ ≤ ‖a‖ := by
  rw [wiener_norm_eq]
  exact norm_apply_le_tsum_coeff a.toFun a.toSub.2 x

/-- The coercion from the Wiener algebra to continuous functions is
distance-nonincreasing. -/
private theorem dist_coe_le (a b : WienerAlgebra T) :
    dist a.toFun b.toFun ≤ dist a b := by
  rw [dist_eq_norm, dist_eq_norm, wiener_norm_eq]
  exact (ContinuousMap.norm_le _ (by positivity)).mpr
    (fun x => by
      rw [← wiener_toFun_sub]
      exact norm_apply_le_tsum_coeff _ ((a - b).toSub.2) x)

/-- Fourier coefficients of a difference in the Wiener algebra. -/
private theorem fourierCoeff_sub_wiener (v w : WienerAlgebra T) (n : ℤ) :
    fourierCoeff ((v - w).toFun) n = fourierCoeff v.toFun n - fourierCoeff w.toFun n := by
  rw [wiener_toFun_sub]
  exact fourierCoeff_sub' _ _ n

/-- Completeness of `ℓ¹(ℤ)`: a sequence of absolutely summable families whose
pairwise `ℓ¹` distances go to zero has an absolutely summable limit, to which
it converges in `ℓ¹` norm. -/
private theorem exists_summable_of_cauchy {a : ℕ → ℤ → ℂ}
    (ha : ∀ k, Summable fun n => ‖a k n‖)
    (hc : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ l ≥ N, ∑' n, ‖a k n - a l n‖ < ε) :
    ∃ b : ℤ → ℂ, Summable (fun n => ‖b n‖) ∧
      (∀ n, Tendsto (fun k => a k n) atTop (𝓝 (b n))) ∧
      ∀ ε > 0, ∃ N, ∀ k ≥ N, ∑' n, ‖a k n - b n‖ < ε := by
  have hdiff : ∀ k l : ℕ, Summable fun n => ‖a k n - a l n‖ := by
    intro k l
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => norm_sub_le _ _) ((ha k).add (ha l))
  have hcauchy : ∀ n : ℤ, CauchySeq fun k => a k n := by
    intro n
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, fun k hk l hl => ?_⟩
    rw [dist_eq_norm]
    refine (hdiff k l).le_tsum n (fun _ _ => norm_nonneg _) |>.trans_lt ?_
    exact hN k hk l hl
  choose b hb using fun n => cauchySeq_tendsto_of_complete (hcauchy n)
  have hbound : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ S : Finset ℤ,
      ∑ n ∈ S, ‖a k n - b n‖ ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, fun k hk S => ?_⟩
    have hfin : Tendsto (fun l => ∑ n ∈ S, ‖a l n - a k n‖) atTop
        (𝓝 (∑ n ∈ S, ‖b n - a k n‖)) := by
      refine Finset.induction_on S ?_ ?_
      · simp
      · intro n S hn ih
        simp only [Finset.sum_insert hn]
        exact (((hb n).sub tendsto_const_nhds).norm).add ih
    have hle : ∑ n ∈ S, ‖b n - a k n‖ ≤ ε := by
      refine le_of_tendsto hfin ?_
      rw [Filter.eventually_atTop]
      exact ⟨N, fun l hl =>
        ((hdiff l k).sum_le_tsum S (fun _ _ => norm_nonneg _)).trans_lt
          (hN l hl k hk) |>.le⟩
    calc ∑ n ∈ S, ‖a k n - b n‖
        = ∑ n ∈ S, ‖b n - a k n‖ :=
          Finset.sum_congr rfl (fun n _ => norm_sub_rev _ _)
      _ ≤ ε := hle
  have hbSumm : Summable fun n => ‖b n‖ := by
    obtain ⟨N, hN⟩ := hbound 1 one_pos
    apply summable_of_sum_le (c := (∑' n, ‖a N n‖) + 1) (fun n => norm_nonneg _)
    intro S
    calc ∑ n ∈ S, ‖b n‖
        ≤ ∑ n ∈ S, (‖a N n‖ + ‖b n - a N n‖) := by
          refine Finset.sum_le_sum fun n _ => ?_
          conv_lhs => rw [← add_sub_cancel (a N n) (b n)]
          exact norm_add_le _ _
      _ = (∑ n ∈ S, ‖a N n‖) + ∑ n ∈ S, ‖a N n - b n‖ := by
          rw [Finset.sum_add_distrib]
          congr 1
          exact Finset.sum_congr rfl (fun n _ => (norm_sub_rev _ _).symm)
      _ ≤ (∑' n, ‖a N n‖) + 1 :=
          add_le_add ((ha N).sum_le_tsum S (fun _ _ => norm_nonneg _)) (hN N le_rfl S)
  refine ⟨b, hbSumm, hb, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hbound (ε / 2) (by positivity)
  refine ⟨N, fun k hk => ?_⟩
  have hsum : Summable fun n => ‖a k n - b n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_sub_le _ _)
      ((ha k).add hbSumm)
  exact (Summable.tsum_le_of_sum_le hsum (fun S => hN k hk S)).trans_lt (half_lt_self hε)

/-- A Fourier coefficient is Lipschitz for the sup norm. -/
private theorem dist_fourierCoeff_le (f g : C(AddCircle T, ℂ)) (n : ℤ) :
    dist (fourierCoeff f n) (fourierCoeff g n) ≤ dist f g := by
  rw [dist_eq_norm, dist_eq_norm, ← fourierCoeff_sub' f g n]
  exact norm_fourierCoeff_le _ _

/-- The Wiener algebra is complete. -/
private instance wienerCompleteSpace : CompleteSpace (WienerAlgebra T) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨b, hbSumm, hbPt, hblim⟩ := exists_summable_of_cauchy
    (a := fun k n => fourierCoeff (u k).toFun n)
    (fun k => (u k).toSub.2.norm) (by
      intro ε hε
      obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hu) ε hε
      refine ⟨N, fun k hk l hl => ?_⟩
      have hcalc : ∑' n, ‖fourierCoeff (u k).toFun n - fourierCoeff (u l).toFun n‖
          = dist (u k) (u l) := by
        calc ∑' n, ‖fourierCoeff (u k).toFun n - fourierCoeff (u l).toFun n‖
            = ∑' n, ‖fourierCoeff ((u k - u l).toFun) n‖ := by
              apply tsum_congr
              intro n
              rw [fourierCoeff_sub_wiener]
          _ = ‖u k - u l‖ := (wiener_norm_eq _).symm
          _ = dist (u k) (u l) := (dist_eq_norm _ _).symm
      rw [hcalc]
      exact hN k hk l hl)
  have hCauchyC : CauchySeq fun k => (u k).toFun := by
    rw [Metric.cauchySeq_iff] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    exact ⟨N, fun k hk l hl => (dist_coe_le (u k) (u l)).trans_lt (hN k hk l hl)⟩
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hCauchyC
  have hcoeffF : ∀ n, fourierCoeff F n = b n := by
    intro n
    have hlim1 : Tendsto (fun k => fourierCoeff (u k).toFun n) atTop
        (𝓝 (fourierCoeff F n)) := by
      have hdist : Tendsto (fun k => dist (fourierCoeff (u k).toFun n) (fourierCoeff F n))
          atTop (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
          (fun k => dist_nonneg) (fun k => dist_fourierCoeff_le _ _ n)
        exact tendsto_iff_dist_tendsto_zero.mp hF
      exact tendsto_iff_dist_tendsto_zero.mpr hdist
    exact tendsto_nhds_unique hlim1 (hbPt n)
  have hFmem : InWienerAlgebra F := by
    change Summable (fourierCoeff F)
    rw [funext hcoeffF]
    exact hbSumm.of_norm
  refine ⟨⟨⟨F, hFmem⟩⟩, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hblim ε hε
  refine ⟨N, fun k hk => ?_⟩
  rw [dist_eq_norm, wiener_norm_eq]
  calc ∑' n, ‖fourierCoeff ((u k - ⟨⟨F, hFmem⟩⟩).toFun) n‖
      = ∑' n, ‖fourierCoeff (u k).toFun n - b n‖ := by
        apply tsum_congr
        intro n
        rw [fourierCoeff_sub_wiener]
        have hFn : ((⟨⟨F, hFmem⟩⟩ : WienerAlgebra T).toFun) = F := rfl
        rw [hFn, hcoeffF n]
    _ < ε := hN k hk

/-- The Fourier monomial of index `n`, as an element of the Wiener algebra. -/
private def wienerMonomial (n : ℤ) : WienerAlgebra T :=
  ⟨⟨fourier n, by
    change Summable (fourierCoeff (fourier n))
    rw [fourierCoeff_fourier]
    apply summable_of_ne_finset_zero (s := {n})
    intro b hb
    by_cases h : b = n
    · exact absurd (Finset.mem_singleton.mpr h) hb
    · exact Pi.single_eq_of_ne (M := fun _ : ℤ => ℂ) h 1⟩⟩

/-- The underlying function of a monomial is the monomial. -/
private theorem wienerMonomial_toFun (n : ℤ) : (wienerMonomial (T := T) n).toFun = fourier n := rfl

/-- Monomials multiply by adding indices. -/
private theorem wienerMonomial_add (m n : ℤ) :
    wienerMonomial (T := T) (m + n) = wienerMonomial (T := T) m * wienerMonomial (T := T) n := by
  apply WienerAlgebra.ext
  rw [wiener_toFun_mul, wienerMonomial_toFun, wienerMonomial_toFun, wienerMonomial_toFun]
  ext x
  exact fourier_add

/-- The monomial of index `0` is `1`. -/
private theorem wienerMonomial_zero : wienerMonomial (T := T) 0 = 1 := by
  apply WienerAlgebra.ext
  rw [wienerMonomial_toFun]
  ext x
  exact fourier_zero

/-- Every monomial has Wiener norm `1`. -/
private theorem wienerMonomial_norm (n : ℤ) : ‖wienerMonomial (T := T) n‖ = 1 := by
  rw [wiener_norm_eq, wienerMonomial_toFun, fourierCoeff_fourier, tsum_eq_single n]
  · simp
  · intro m hm
    rw [Pi.single_eq_of_ne (M := fun _ : ℤ => ℂ) hm 1, norm_zero]

/-- A character takes the value `ζ ^ k` on the `k`-th monomial, where
`ζ` is its value on the first monomial. -/
private theorem character_monomial_pow (φ : WeakDual.characterSpace ℂ (WienerAlgebra T)) (k : ℕ) :
    φ (wienerMonomial k) = (φ (wienerMonomial 1)) ^ k := by
  induction k with
  | zero =>
    rw [Nat.cast_zero, wienerMonomial_zero]
    simp [map_one]
  | succ k ih =>
    have h1 : wienerMonomial (T := T) ((k : ℤ) + 1)
        = wienerMonomial (T := T) k * wienerMonomial (T := T) 1 :=
      wienerMonomial_add _ _
    have h2 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
    rw [h2, h1, map_mul, ih, pow_succ]

/-- A character takes the value `ζ ^ (-k)` on the `(-k)`-th monomial. -/
private theorem character_monomial_neg (φ : WeakDual.characterSpace ℂ (WienerAlgebra T)) (k : ℕ) :
    φ (wienerMonomial (-(k : ℤ))) = (φ (wienerMonomial 1)) ^ (-(k : ℤ)) := by
  have hprod : wienerMonomial (T := T) (-(k : ℤ)) * wienerMonomial (T := T) k = 1 := by
    rw [← wienerMonomial_add, neg_add_cancel, wienerMonomial_zero]
  have hφ : φ (wienerMonomial (-(k : ℤ))) * (φ (wienerMonomial 1)) ^ k = 1 := by
    rw [← character_monomial_pow, ← map_mul, hprod, map_one]
  calc φ (wienerMonomial (-(k : ℤ))) = ((φ (wienerMonomial 1)) ^ k)⁻¹ :=
        eq_inv_of_mul_eq_one_left hφ
    _ = (φ (wienerMonomial 1)) ^ (-(k : ℤ)) := by
        rw [zpow_neg, zpow_natCast]

/-- A character takes the value `ζ ^ n` on the `n`-th monomial. -/
private theorem character_monomial_zpow (φ : WeakDual.characterSpace ℂ (WienerAlgebra T)) (n : ℤ) :
    φ (wienerMonomial n) = (φ (wienerMonomial 1)) ^ n := by
  cases n with
  | ofNat k =>
    change φ (wienerMonomial (k : ℤ)) = (φ (wienerMonomial 1)) ^ (k : ℤ)
    rw [zpow_natCast]
    exact character_monomial_pow φ k
  | negSucc k =>
    have hk : Int.negSucc k = -((k + 1 : ℕ) : ℤ) := by simp [Int.negSucc_eq]
    rw [hk]
    exact character_monomial_neg φ (k + 1)

/-- The value of a character on the first monomial has modulus `1`. -/
private theorem character_zeta_norm (φ : WeakDual.characterSpace ℂ (WienerAlgebra T)) :
    ‖φ (wienerMonomial 1)‖ = 1 := by
  set ζ := φ (wienerMonomial 1) with hζ
  set η := φ (wienerMonomial (-1)) with hη
  have hprod : ζ * η = 1 := by
    have h := map_mul φ (wienerMonomial 1) (wienerMonomial (-1))
    rw [← wienerMonomial_add, show (1 : ℤ) + -1 = 0 by norm_num, wienerMonomial_zero,
      map_one] at h
    exact h.symm
  have hηeq : η = ζ⁻¹ := eq_inv_of_mul_eq_one_right hprod
  have hbound : ∀ k : ℕ, ‖ζ ^ k‖ ≤ ‖WeakDual.CharacterSpace.toCLM φ‖ := by
    intro k
    have h1 := ContinuousLinearMap.le_opNorm (WeakDual.CharacterSpace.toCLM φ)
      (wienerMonomial (k : ℤ))
    rw [wienerMonomial_norm, mul_one] at h1
    have h2 : (WeakDual.CharacterSpace.toCLM φ) (wienerMonomial (k : ℤ)) = ζ ^ k := by
      change φ (wienerMonomial (k : ℤ)) = ζ ^ k
      rw [character_monomial_pow]
    rw [h2] at h1
    exact h1
  have hboundη : ∀ k : ℕ, ‖η ^ k‖ ≤ ‖WeakDual.CharacterSpace.toCLM φ‖ := by
    intro k
    have h1 := ContinuousLinearMap.le_opNorm (WeakDual.CharacterSpace.toCLM φ)
      ((wienerMonomial (T := T) (-1)) ^ k)
    have h2 : (WeakDual.CharacterSpace.toCLM φ) ((wienerMonomial (T := T) (-1)) ^ k) = η ^ k := by
      change φ ((wienerMonomial (T := T) (-1)) ^ k) = η ^ k
      rw [map_pow]
    rw [h2] at h1
    have hpow : ∀ k : ℕ, ‖(wienerMonomial (T := T) (-1)) ^ k‖ ≤ 1 := by
      intro k
      induction k with
      | zero => simp [pow_zero, ← wienerMonomial_zero, wienerMonomial_norm]
      | succ k ih =>
        rw [pow_succ]
        calc ‖(wienerMonomial (T := T) (-1)) ^ k * wienerMonomial (T := T) (-1)‖
            ≤ ‖(wienerMonomial (T := T) (-1)) ^ k‖ * ‖wienerMonomial (T := T) (-1)‖ :=
              norm_mul_le _ _
          _ ≤ 1 * 1 :=
              mul_le_mul ih (le_of_eq (wienerMonomial_norm _)) (norm_nonneg _)
                zero_le_one
          _ = 1 := mul_one 1
    refine h1.trans ?_
    calc ‖WeakDual.CharacterSpace.toCLM φ‖ * ‖(wienerMonomial (T := T) (-1)) ^ k‖
        ≤ ‖WeakDual.CharacterSpace.toCLM φ‖ * 1 :=
          mul_le_mul_of_nonneg_left (hpow k) (ContinuousLinearMap.opNorm_nonneg _)
      _ = ‖WeakDual.CharacterSpace.toCLM φ‖ := mul_one _
  have hζle : ‖ζ‖ ≤ 1 := by
    by_contra h
    have hlt : (1 : ℝ) < ‖ζ‖ := not_le.mp h
    obtain ⟨k, hk⟩ :=
      (tendsto_pow_atTop_atTop_of_one_lt hlt).eventually_gt_atTop
        ‖WeakDual.CharacterSpace.toCLM φ‖ |>.exists
    have hnorm : ‖ζ ^ k‖ = ‖ζ‖ ^ k := norm_pow _ _
    exact absurd (hnorm ▸ hbound k) (not_le.mpr hk)
  have hηle : ‖η‖ ≤ 1 := by
    by_contra h
    have hlt : (1 : ℝ) < ‖η‖ := not_le.mp h
    obtain ⟨k, hk⟩ :=
      (tendsto_pow_atTop_atTop_of_one_lt hlt).eventually_gt_atTop
        ‖WeakDual.CharacterSpace.toCLM φ‖ |>.exists
    have hnorm : ‖η ^ k‖ = ‖η‖ ^ k := norm_pow _ _
    exact absurd (hnorm ▸ hboundη k) (not_le.mpr hk)
  have hζne : ‖ζ‖ ≠ 0 := by
    intro h0
    have : ζ = 0 := norm_eq_zero.mp h0
    rw [this, zero_mul] at hprod
    exact zero_ne_one hprod
  have hle : (1 : ℝ) ≤ ‖ζ‖ := by
    calc (1 : ℝ) = ‖ζ‖⁻¹ * ‖ζ‖ := (inv_mul_cancel₀ hζne).symm
      _ ≤ 1 * ‖ζ‖ :=
          mul_le_mul_of_nonneg_right (by rw [← norm_inv, ← hηeq]; exact hηle) (norm_nonneg _)
      _ = ‖ζ‖ := one_mul _
  exact le_antisymm hζle hle

/-- A Fourier monomial is a power of the first monomial, pointwise. -/
private theorem fourier_zpow {S : ℝ} (n : ℤ) (x : AddCircle S) :
    fourier n x = (fourier 1 x) ^ n := by
  simp only [fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow, zpow_one]

/-- The inclusion of the Wiener algebra in the continuous functions, as a
continuous linear map. -/
private def wienerToFunCLM : WienerAlgebra T →L[ℂ] C(AddCircle T, ℂ) where
  toFun a := a.toFun
  map_add' := wiener_toFun_add
  map_smul' := wiener_toFun_smul
  cont := by
    have hLip : LipschitzWith 1 (fun a : WienerAlgebra T => a.toFun) :=
      LipschitzWith.of_dist_le_mul (by intro a b; simpa using dist_coe_le a b)
    exact hLip.continuous

/-- Every character of the Wiener algebra is evaluation at a point of the
circle. -/
private theorem character_apply (φ : WeakDual.characterSpace ℂ (WienerAlgebra T))
    (a : WienerAlgebra T) :
    ∃ x : AddCircle T, φ a = a.toFun x := by
  have hζnorm := character_zeta_norm φ
  have hT : T ≠ 0 := ne_of_gt (Fact.out : (0 : ℝ) < T)
  let z : Circle := ⟨φ (wienerMonomial 1), mem_sphere_zero_iff_norm.mpr hζnorm⟩
  let x : AddCircle T := (AddCircle.homeomorphCircle hT).symm z
  have h1 : AddCircle.toCircle x = z := by
    rw [← AddCircle.homeomorphCircle_apply hT]
    exact (AddCircle.homeomorphCircle hT).apply_symm_apply z
  have hfx : (fourier 1) x = φ (wienerMonomial 1) := by
    rw [fourier_one, h1]
  have hHasSum : HasSum (fun n : ℤ => fourierCoeff a.toFun n • wienerMonomial (T := T) n) a := by
    have hnorm : Summable fun n => ‖fourierCoeff a.toFun n • wienerMonomial (T := T) n‖ := by
      have hfun : (fun n => ‖fourierCoeff a.toFun n • wienerMonomial (T := T) n‖)
          = fun n => ‖fourierCoeff a.toFun n‖ := by
        funext n
        rw [norm_smul, wienerMonomial_norm, mul_one]
      rw [hfun]
      exact a.toSub.2.norm
    obtain ⟨L, hL⟩ : ∃ L, HasSum (fun n => fourierCoeff a.toFun n • wienerMonomial (T := T) n) L :=
      ⟨∑' n, fourierCoeff a.toFun n • wienerMonomial (T := T) n, (hnorm.of_norm).hasSum⟩
    have hC : HasSum (fun n => fourierCoeff a.toFun n • fourier (T := T) n) a.toFun :=
      hasSum_fourier_series_of_summable a.toSub.2
    have htoFun : (fun n => (fourierCoeff a.toFun n • wienerMonomial (T := T) n).toFun)
        = fun n => fourierCoeff a.toFun n • fourier (T := T) n := by
      funext n
      rw [wiener_toFun_smul, wienerMonomial_toFun]
    have hCL : HasSum
        (fun n => (fourierCoeff a.toFun n • wienerMonomial (T := T) n).toFun) L.toFun := by
      have h := (wienerToFunCLM (T := T)).hasSum hL
      have hcoe : (fun n => wienerToFunCLM (fourierCoeff a.toFun n • wienerMonomial (T := T) n))
          = fun n => (fourierCoeff a.toFun n • wienerMonomial (T := T) n).toFun := rfl
      rw [hcoe] at h
      exact h
    rw [htoFun] at hCL
    have hLeq : L.toFun = a.toFun := hCL.unique hC
    have : L = a := WienerAlgebra.ext hLeq
    rw [this] at hL
    exact hL
  refine ⟨x, ?_⟩
  have hφ : φ a = ∑' n, fourierCoeff a.toFun n * (φ (wienerMonomial 1)) ^ n := by
    have h1 := (WeakDual.CharacterSpace.toCLM φ).hasSum hHasSum
    have h2 : (fun n => (WeakDual.CharacterSpace.toCLM φ)
        (fourierCoeff a.toFun n • wienerMonomial (T := T) n))
        = fun n => fourierCoeff a.toFun n * (φ (wienerMonomial 1)) ^ n := by
      funext n
      change φ (fourierCoeff a.toFun n • wienerMonomial (T := T) n)
        = fourierCoeff a.toFun n * (φ (wienerMonomial 1)) ^ n
      rw [map_smul, character_monomial_zpow, smul_eq_mul]
    rw [h2] at h1
    exact h1.tsum_eq.symm
  have hx2 : a.toFun x = ∑' n, fourierCoeff a.toFun n * (φ (wienerMonomial 1)) ^ n := by
    have hpt := has_pointwise_sum_fourier_series_of_summable a.toSub.2 x
    have h3 : (fun n => fourierCoeff (a.toSub : C(AddCircle T, ℂ)) n • fourier n x)
        = fun n => fourierCoeff (a.toSub : C(AddCircle T, ℂ)) n * (φ (wienerMonomial 1)) ^ n := by
      funext n
      rw [smul_eq_mul, fourier_zpow, hfx]
    rw [h3] at hpt
    exact hpt.tsum_eq.symm
  rw [hφ, hx2]

set_option linter.dupNamespace false in
/- **Wiener's `1/f` theorem.** If a function on the circle belongs to the
Wiener algebra and has no zero on the circle, then its pointwise reciprocal
again belongs to the Wiener algebra. -/
/-- **Wiener's 1/f theorem.** Let $T > 0$, and let $f : \mathbb{R}/T\mathbb{Z} \to \mathbb{C}$ be
a continuous function in the Wiener algebra with $f(x) \ne 0$ for every $x$. Then there is a
continuous function $g : \mathbb{R}/T\mathbb{Z} \to \mathbb{C}$ with $g(x) = f(x)^{-1}$ for every
$x$, and $g$ lies in the Wiener algebra.

Source: N. Wiener, Tauberian theorems, Ann. of Math. 33 (1932), 1-100. Listed as §226 in O. Knill,
Some Fundamental Theorems in Mathematics
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Knill, §226. Via
leanprover/lean-eval@38361be, problem `wiener_inverse_closed`. -/
theorem wiener_inverse_closed (f : C(AddCircle T, ℂ))
    (hf : InWienerAlgebra f) (hzero : ∀ x, f x ≠ 0) :
    ∃ g : C(AddCircle T, ℂ),
      (∀ x, g x = (f x)⁻¹) ∧ InWienerAlgebra g := by
  let a : WienerAlgebra T := ⟨⟨f, hf⟩⟩
  have ha : a.toFun = f := rfl
  have hunit : IsUnit a := by
    by_contra h
    have hspec : (0 : ℂ) ∈ spectrum ℂ a := (spectrum.zero_mem_iff ℂ).mpr h
    obtain ⟨φ, hφ⟩ := WeakDual.CharacterSpace.mem_spectrum_iff_exists.mp hspec
    obtain ⟨x, hx⟩ := character_apply φ a
    have hz : f x = 0 := by
      rw [← ha, ← hx, hφ]
    exact hzero x hz
  obtain ⟨u, hu⟩ := hunit
  refine ⟨(↑(u⁻¹) : WienerAlgebra T).toFun, ?_, (↑(u⁻¹) : WienerAlgebra T).toSub.2⟩
  intro x
  have hmul : (↑(u⁻¹) : WienerAlgebra T).toFun x * f x = 1 := by
    have h1 : (↑(u⁻¹) : WienerAlgebra T) * a = 1 := by
      rw [← hu]
      exact u.inv_mul
    have h2 : ((↑(u⁻¹) : WienerAlgebra T) * a).toFun x = (1 : WienerAlgebra T).toFun x := by
      rw [h1]
    rw [wiener_toFun_mul] at h2
    simp only [wiener_toFun_one] at h2
    rw [ha] at h2
    exact h2
  exact eq_inv_of_mul_eq_one_left hmul

end

end Analysis.WienerOneOverF

end MathlibExt.Analysis.WienerOneOverFWanted
