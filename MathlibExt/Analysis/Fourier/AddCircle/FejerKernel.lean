/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.AddCircle

/-!
# The Fejér kernel on the additive circle

For a period `T > 0`, the `N`-th Fejér kernel `K_N` on `AddCircle T` is the Cesàro mean
of the Dirichlet kernels. For a real representative `r` of `x : AddCircle T`:
`K_N(x) = (N + 1)⁻¹ • ∑_{k=0}^{N} ∑_{n=-k}^{k} e^{2πi n r / T}`.

The main results are the defining properties of an approximation to the identity:

* `AddCircle.fejerKernel_symmetric`: `K_N(-x) = K_N(x)`.
* `AddCircle.integral_fejerKernel`: `∫ K_N = 1`.
* `AddCircle.fejerKernel_nonneg`: `0 ≤ Re K_N(x)`.
* `AddCircle.fejerKernel_eq_ofReal`: `K_N(x) = (N + 1)⁻¹ * ‖∑_{k=0}^{N} fourier k x‖²`
  as a nonnegative real number, so `‖K_N(x)‖ = Re K_N(x)`.
* `AddCircle.fejer_kernel_properties`: the bundled properties above, plus `T`-periodicity
  and the decay estimate `‖K_N(x)‖ ≤ 4 / ((N + 1) * δ²)` whenever
  `δ ≤ ‖1 - fourier 1 x‖`.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/FourierSeries.lean`
(targets: Definition of the Fejér kernel, April 15, 2021; Proposition on its
properties, April 15, 2021). The v1 file used the namespace `FourierSeries`;
here the kernel lives in Mathlib's `AddCircle` namespace, alongside `AddCircle.haarAddCircle`
(the Fourier monomials themselves live in the root namespace as `fourier`).
-/

@[expose] public section

variable {T : ℝ} [hT : Fact (0 < T)]

open MeasureTheory AddCircle Finset Filter Complex

namespace AddCircle

/-- **The Fejér kernel.** Let $T > 0$ and, for $n \in \mathbb{Z}$, let
$e_n(x) = e^{2\pi i n x / T}$ be the $n$-th Fourier character on the circle
$\mathbb{R}/T\mathbb{Z}$. For a natural number $N$, the $N$-th Fejér kernel is the function
$K_N : \mathbb{R}/T\mathbb{Z} \to \mathbb{C}$ given by the Cesàro mean of the Dirichlet kernels,
$K_N(x) = \frac{1}{N+1} \sum_{k=0}^{N} \sum_{n=-k}^{k} e_n(x)$.

Writing $x$ also for a real representative, when $\sin(\pi x / T) \ne 0$ the kernel has the closed
form $K_N(x) = \frac{1}{N+1} \left(\frac{\sin((N+1)\pi x / T)}{\sin(\pi x / T)}\right)^2$.
This normalization is for the Haar probability measure on $\mathbb{R}/T\mathbb{Z}$; for $T = 2\pi$,
the kernel for integration against Lebesgue measure is $K_N / (2\pi)$. -/
noncomputable def fejerKernel (N : ℕ) : AddCircle T → ℂ :=
  fun x => ((N : ℂ) + 1)⁻¹ • ∑ k ∈ range (N + 1),
    ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), fourier n x

/-- **Integrability of Fourier characters.** Let $T > 0$. For every integer $n$, the Fourier
character $e_n(x) = e^{2\pi i n x / T}$ is integrable on the circle $\mathbb{R}/T\mathbb{Z}$ with
respect to the normalized Haar measure, the Haar measure of total mass $1$. -/
theorem fourier_integrable (n : ℤ) :
    Integrable (fun t : AddCircle T => (fourier n t : ℂ)) haarAddCircle :=
  Integrable.of_bound (C := 1) (map_continuous (fourier n)).aestronglyMeasurable
    (ae_of_all _ (fun t => by rw [fourier_apply, Circle.norm_coe]))

/-- **Integral of a Fourier character.** Let $T > 0$ and, for $n \in \mathbb{Z}$, let
$e_n(t) = e^{2\pi i n t / T}$ be the $n$-th Fourier character on the circle
$\mathbb{R}/T\mathbb{Z}$. With respect to the Haar probability measure on the circle,
$\int e_n = 1$ if $n = 0$ and $\int e_n = 0$ otherwise. This is the orthogonality of the
Fourier basis. -/
theorem integral_fourier (n : ℤ) :
    ∫ t : AddCircle T, fourier n t ∂haarAddCircle =
    if n = 0 then 1 else 0 := by
  have h := fourierCoeff_fourier (T := T) 0
  have hn := congr_fun h (-n)
  simp only [Pi.single_apply, fourierCoeff] at hn
  simp only [neg_neg] at hn
  have h0 : ∀ t : AddCircle T, (fourier n t : ℂ) • (fourier (0 : ℤ) t : ℂ) = fourier n t := by
    intro t; simp [fourier_apply, zero_smul]
  simp only [h0] at hn
  simp only [show (-n = (0 : ℤ)) ↔ (n = 0) from neg_eq_zero] at hn
  exact hn

/-- **The Dirichlet kernel has integral one.** Let $T > 0$, let
$e_n(t) = e^{2\pi i n t / T}$ be the $n$-th Fourier character on the circle
$\mathbb{R}/T\mathbb{Z}$, and for $k \in \mathbb{N}$ let $D_k = \sum_{n=-k}^{k} e_n$ be the
$k$-th Dirichlet kernel. With respect to the Haar probability measure on the circle,
$\int D_k = 1$; only the term $n = 0$ contributes, by orthogonality. -/
theorem integral_dirichlet_sum (k : ℕ) :
    ∫ t : AddCircle T, ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ),
      fourier n t ∂haarAddCircle = 1 := by
  rw [integral_finsetSum _ (fun n _ => fourier_integrable n)]
  simp only [integral_fourier]
  have h0 : (0 : ℤ) ∈ Finset.Icc (-(k : ℤ)) (k : ℤ) := by simp
  rw [← Finset.add_sum_erase _ _ h0, ite_eq_left rfl]
  have : ∑ x ∈ (Finset.Icc (-(k : ℤ)) (k : ℤ)).erase 0,
      (if x = (0 : ℤ) then (1 : ℂ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [Finset.mem_erase] at hn
    simp [hn.1]
  rw [this, add_zero]

set_option linter.unusedSectionVars false in
/-- **Symmetry of the Fejér kernel.** Let $T > 0$. For every natural number $N$ and every
$x \in \mathbb{R}/T\mathbb{Z}$, the $N$-th Fejér kernel satisfies $K_N(-x) = K_N(x)$. -/
theorem fejerKernel_symmetric (N : ℕ) (x : AddCircle T) :
    fejerKernel N (-x) = fejerKernel N x := by
  unfold fejerKernel
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have key : ∀ n : ℤ, n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ) →
      (fourier n) (-x) = (fourier (-n)) x := by
    intros n _
    simp [fourier_apply, neg_smul]
  rw [Finset.sum_congr rfl (fun n hn => key n hn)]
  rw [← Finset.sum_equiv (Equiv.neg ℤ) (s := Finset.Icc (-(k : ℤ)) (k : ℤ))
    (t := Finset.Icc (-(k : ℤ)) (k : ℤ))]
  · intro n
    simp only [Equiv.neg_apply, Finset.mem_Icc]
    constructor
    · intro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · intro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · intro n _
    simp [Equiv.neg_apply]

/-- **The Fejér kernel has integral one.** Let $T > 0$ and $N \in \mathbb{N}$. The $N$-th Fejér
kernel $K_N$ on the circle $\mathbb{R}/T\mathbb{Z}$ satisfies $\int K_N = 1$ with respect to the
Haar probability measure on the circle. This is one of the defining properties of an
approximation to the identity. -/
theorem integral_fejerKernel (N : ℕ) :
    ∫ t : AddCircle T, fejerKernel N t ∂haarAddCircle = 1 := by
  unfold fejerKernel
  rw [integral_smul]
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _
    (fun n _ => fourier_integrable n))]
  simp only [integral_dirichlet_sum, Finset.sum_const, Finset.card_range]
  simp only [nsmul_eq_mul, mul_one]
  rw [show ((N + 1 : ℕ) : ℂ) = ((N : ℂ) + 1) from by push_cast; ring]
  exact inv_mul_cancel₀ (by
    have : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    exact_mod_cast this.ne')

/-- Arithmetic identity `∑_{k=0}^{N} (2k + 1) = (N+1)²`, used to bound the size of
the iterated Dirichlet sum that defines the Fejér kernel. -/
private lemma sum_odd_eq_sq (N : ℕ) :
    ∑ k ∈ range (N + 1), ((2 : ℝ) * k + 1) = ((N : ℝ) + 1) ^ 2 := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

set_option linter.unusedSectionVars false in
/-- **Pointwise bound for the Fejér kernel.** Let $T > 0$ and $N \in \mathbb{N}$. For every point
$x$ of the circle $\mathbb{R}/T\mathbb{Z}$, the $N$-th Fejér kernel satisfies
$|K_N(x)| \le N + 1$.

This follows from the triangle inequality applied to the iterated Dirichlet sum defining
$K_N$, together with $\sum_{k=0}^{N} (2k+1) = (N+1)^2$. -/
theorem norm_fejerKernel_le (N : ℕ) (x : AddCircle T) :
    ‖fejerKernel N x‖ ≤ (N : ℝ) + 1 := by
  unfold fejerKernel
  rw [norm_smul]
  have hN_inv : ‖((N : ℂ) + 1)⁻¹‖ = ((N : ℝ) + 1)⁻¹ := by
    rw [norm_inv]; congr 1
    have h : ((N : ℂ) + 1) = ((N + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [h, Complex.norm_natCast]; push_cast; ring
  rw [hN_inv]
  have hsum_bound : ‖∑ k ∈ range (N + 1),
      ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), fourier n x‖
    ≤ ((N : ℝ) + 1) ^ 2 := by
    calc ‖∑ k ∈ range (N + 1),
        ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), fourier n x‖
      ≤ ∑ k ∈ range (N + 1),
        ‖∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), fourier n x‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ range (N + 1), ((2 : ℝ) * k + 1) := by
          gcongr with k _
          calc ‖∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), fourier n x‖
            ≤ ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), ‖fourier n x‖ := norm_sum_le _ _
            _ = ∑ _n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), (1 : ℝ) := by
                congr 1; ext n; rw [fourier_apply, Circle.norm_coe]
            _ = (Finset.Icc (-(k : ℤ)) (k : ℤ)).card := by simp
            _ = 2 * k + 1 := by
                have h : (Finset.Icc (-(k : ℤ)) (k : ℤ)).card = 2 * k + 1 := by
                  rw [Int.card_Icc]; omega
                exact_mod_cast h
      _ = ((N : ℝ) + 1) ^ 2 := sum_odd_eq_sq N
  calc ((N : ℝ) + 1)⁻¹ * ‖∑ k ∈ range (N + 1),
      ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), fourier n x‖
    ≤ ((N : ℝ) + 1)⁻¹ * ((N : ℝ) + 1) ^ 2 := by gcongr
    _ = (N : ℝ) + 1 := by field_simp

set_option linter.unusedSectionVars false in
/-- **Continuity of the Fejér kernel.** Let $T > 0$. For every natural number $N$, the $N$-th
Fejér kernel $K_N$ is a continuous function from the circle $\mathbb{R}/T\mathbb{Z}$ to
$\mathbb{C}$. -/
theorem fejerKernel_continuous (N : ℕ) : Continuous (fejerKernel (T := T) N) := by
  unfold fejerKernel
  fun_prop

/-- **Integrability of the Fejér kernel.** Let $T > 0$. For every natural number $N$, the $N$-th
Fejér kernel $K_N$ is integrable on the circle $\mathbb{R}/T\mathbb{Z}$ with respect to the
normalized Haar measure, the Haar measure of total mass $1$. -/
theorem fejerKernel_integrable (N : ℕ) :
    Integrable (fejerKernel (T := T) N) haarAddCircle := by
  apply Integrable.of_bound (C := (N : ℝ) + 1)
  · exact (fejerKernel_continuous N).aestronglyMeasurable
  · exact ae_of_all _ (fun x => norm_fejerKernel_le N x)

omit hT in
/-- **Products of Fourier characters.** Let $T$ be a real number and, for $n \in \mathbb{Z}$, let
$e_n$ be the $n$-th Fourier character on $\mathbb{R}/T\mathbb{Z}$, given by
$e_n(x) = e^{2\pi i n x / T}$ (the constant $1$ when $T = 0$). For every integer $n$ and all
$x, t \in \mathbb{R}/T\mathbb{Z}$, we have $e_{-n}(t)\, e_n(x) = e_n(x - t)$. -/
theorem fourier_neg_mul_fourier_eq (n : ℤ) (x t : AddCircle T) :
    (fourier (-n) t : ℂ) * (fourier n x : ℂ) = (fourier n (x - t) : ℂ) := by
  simp only [fourier_apply]
  rw [smul_sub, show n • x - n • t = n • x + (-n) • t from by rw [neg_smul]; abel]
  rw [toCircle_add]
  simp [Circle.coe_mul, mul_comm]

set_option linter.unusedSectionVars false in
/-- **Reindexing a sum of Fourier characters, negative range.** Let $T > 0$, let
$e_n(t) = e^{2\pi i n t / T}$ be the $n$-th Fourier character on the circle
$\mathbb{R}/T\mathbb{Z}$, and let $N \in \mathbb{N}$. For every point $x$ of the circle,
$\sum_{k=0}^{N} e_{k-(N+1)}(x) = \sum_{n=-(N+1)}^{-1} e_n(x)$.

It is used in the proof that the iterated Dirichlet sum defining the Fejér kernel equals
$\left|\sum_{k=0}^{N} e_k(x)\right|^2$. -/
lemma sum_range_fourier_shift_neg (N : ℕ) (x : AddCircle T) :
    ∑ k ∈ range (N + 1), (fourier ((↑k : ℤ) + -↑(N + 1)) x : ℂ) =
    ∑ n ∈ Finset.Icc (-(↑(N + 1) : ℤ)) (-1 : ℤ), (fourier n x : ℂ) := by
  apply Finset.sum_nbij (fun k : ℕ => (↑k : ℤ) + (-↑(N + 1)))
  · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Icc]
    constructor <;> push_cast <;> omega
  · intro k1 _ k2 _ h; exact_mod_cast show (↑k1 : ℤ) = ↑k2 from by linarith
  · intro n hn
    simp only [Finset.coe_Icc, Finset.coe_range, Set.mem_Icc, Set.mem_image, Set.mem_Iio] at hn ⊢
    exact ⟨(n + ↑(N + 1)).toNat, by push_cast; omega,
      by rw [Int.toNat_of_nonneg (by omega)]; push_cast; ring⟩
  · intro k _; rfl

set_option linter.unusedSectionVars false in
/-- **Reindexing a sum of Fourier characters, positive range.** Let $T > 0$, let
$e_n(t) = e^{2\pi i n t / T}$ be the $n$-th Fourier character on the circle
$\mathbb{R}/T\mathbb{Z}$, and let $N \in \mathbb{N}$. For every point $x$ of the circle,
$\sum_{k=0}^{N} e_{(N+1)-k}(x) = \sum_{n=1}^{N+1} e_n(x)$. -/
lemma sum_range_fourier_shift_pos (N : ℕ) (x : AddCircle T) :
    ∑ k ∈ range (N + 1), (fourier ((↑(N + 1) : ℤ) + -↑k) x : ℂ) =
    ∑ n ∈ Finset.Icc (1 : ℤ) (↑(N + 1)), (fourier n x : ℂ) := by
  apply Finset.sum_nbij (fun k : ℕ => (↑(N + 1) : ℤ) + (-↑k))
  · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Icc]
    constructor <;> push_cast <;> omega
  · intro k1 _ k2 _ h; exact_mod_cast show (↑k1 : ℤ) = ↑k2 from by linarith
  · intro n hn
    simp only [Finset.coe_Icc, Finset.coe_range, Set.mem_Icc, Set.mem_image, Set.mem_Iio] at hn ⊢
    exact ⟨(↑(N + 1) - n).toNat, by push_cast; omega,
      by rw [Int.toNat_of_nonneg (by omega)]; push_cast; ring⟩
  · intro k _; rfl

/-- **The sum of Dirichlet kernels is a squared modulus.** Let $T > 0$ and, for $n \in \mathbb{Z}$,
let $e_n(x) = e^{2\pi i n x / T}$ be the $n$-th Fourier character on the circle
$\mathbb{R}/T\mathbb{Z}$. For every natural number $N$ and every $x \in \mathbb{R}/T\mathbb{Z}$,
put $G = \sum_{k=0}^{N} e_k(x)$. Then the iterated sum of Dirichlet kernels satisfies
$\sum_{k=0}^{N} \sum_{n=-k}^{k} e_n(x) = G\,\overline{G} = |G|^2$. -/
theorem fejer_dirichlet_sum_eq_sq (N : ℕ) (x : AddCircle T) :
    (∑ k ∈ range (N + 1), ∑ n ∈ Finset.Icc (-(k : ℤ)) (↑k), (fourier n x : ℂ)) =
    (∑ k ∈ range (N + 1), (fourier (↑k : ℤ) x : ℂ)) *
    starRingEnd ℂ (∑ k ∈ range (N + 1), (fourier (↑k : ℤ) x : ℂ)) := by
  induction N with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, Nat.cast_zero, neg_zero, Finset.Icc_self]
    rw [fourier_zero, map_one, mul_one]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    set G := ∑ k ∈ range (N + 1), (fourier (↑k : ℤ) x : ℂ) with hG_def
    set z := (fourier (↑(N + 1) : ℤ) x : ℂ) with hz_def
    suffices h : ∑ n ∈ Finset.Icc (-(↑(N + 1) : ℤ)) (↑(N + 1)), (fourier n x : ℂ) =
        G * starRingEnd ℂ z + z * starRingEnd ℂ G + z * starRingEnd ℂ z by
      rw [h, map_add, mul_add, add_mul, add_mul]; ring
    have hGz : G * starRingEnd ℂ z =
        ∑ n ∈ Finset.Icc (-(↑(N + 1) : ℤ)) (-1), (fourier n x : ℂ) := by
      rw [hG_def, hz_def, Finset.sum_mul]
      simp_rw [fourier_neg.symm, ← fourier_add (T := T)]
      exact sum_range_fourier_shift_neg N x
    have hzG : z * starRingEnd ℂ G =
        ∑ n ∈ Finset.Icc (1 : ℤ) (↑(N + 1)), (fourier n x : ℂ) := by
      rw [hG_def, hz_def, map_sum, Finset.mul_sum]
      simp_rw [fourier_neg.symm, ← fourier_add (T := T)]
      exact sum_range_fourier_shift_pos N x
    have hzz : z * starRingEnd ℂ z = fourier (0 : ℤ) x := by
      rw [hz_def, fourier_neg.symm, ← fourier_add]; simp
    rw [hGz, hzG, hzz]
    have h_union : Finset.Icc (-(↑(N + 1) : ℤ)) (↑(N + 1)) =
        Finset.Icc (-(↑(N + 1) : ℤ)) (-1) ∪ {(0 : ℤ)} ∪ Finset.Icc (1 : ℤ) (↑(N + 1)) := by
      ext n; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton]; omega
    have h_disj1 : Disjoint (Finset.Icc (-(↑(N + 1) : ℤ)) (-1) ∪ {(0 : ℤ)})
        (Finset.Icc (1 : ℤ) (↑(N + 1))) := by
      simp only [Finset.disjoint_left, Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton]
      intro n hn; omega
    have h_disj2 : Disjoint (Finset.Icc (-(↑(N + 1) : ℤ)) (-1)) {(0 : ℤ)} := by
      simp only [Finset.disjoint_left, Finset.mem_Icc, Finset.mem_singleton]
      intro n hn; omega
    rw [h_union, Finset.sum_union h_disj1, Finset.sum_union h_disj2, Finset.sum_singleton]
    ring

/-- **Nonnegativity of the Fejér kernel.** Let $T > 0$. For every natural number $N$ and every
$x \in \mathbb{R}/T\mathbb{Z}$, the real part of the $N$-th Fejér kernel at $x$ is nonnegative:
$\operatorname{Re} K_N(x) \ge 0$. -/
theorem fejerKernel_nonneg (N : ℕ) (x : AddCircle T) :
    0 ≤ (fejerKernel N x).re := by
  unfold fejerKernel
  rw [fejer_dirichlet_sum_eq_sq, mul_conj]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring_nf
  apply mul_nonneg
  · have h : (1 + (↑N : ℂ))⁻¹ = ↑((1 + (N : ℝ))⁻¹) := by
      rw [Complex.ofReal_inv]; congr 1; push_cast; ring
    rw [h, Complex.ofReal_re]
    positivity
  · exact normSq_nonneg _

/-- **The Fejér kernel as a squared modulus.** Let $T > 0$ and, for $k \in \mathbb{Z}$, let
$e_k(x) = e^{2\pi i k x / T}$ be the $k$-th Fourier character on the circle
$\mathbb{R}/T\mathbb{Z}$. For every natural number $N$ and every $x \in \mathbb{R}/T\mathbb{Z}$,
the $N$-th Fejér kernel satisfies $K_N(x) = \frac{1}{N+1} \left|\sum_{k=0}^{N} e_k(x)\right|^2$.

In particular $K_N(x)$ is a nonnegative real number, so $|K_N(x)| = \operatorname{Re} K_N(x)$. -/
theorem fejerKernel_eq_ofReal (N : ℕ) (x : AddCircle T) :
    fejerKernel N x = ↑(((N : ℝ) + 1)⁻¹ *
      normSq (∑ k ∈ range (N + 1), (fourier (↑k : ℤ) x : ℂ))) := by
  unfold fejerKernel
  simp only [smul_eq_mul]
  have h_inv : ((N : ℂ) + 1)⁻¹ = ↑(((N : ℝ) + 1)⁻¹) := by
    rw [Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
  have h_sum : (∑ k ∈ range (N + 1), ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), (fourier n x : ℂ)) =
      ↑(normSq (∑ k ∈ range (N + 1), (fourier (↑k : ℤ) x : ℂ))) := by
    rw [fejer_dirichlet_sum_eq_sq, mul_conj]
  rw [h_inv, h_sum, ← Complex.ofReal_mul]

/-- **Properties of the Fejér kernel.** Let $T > 0$, let $N$ be a natural number, let $K_N$ be
the $N$-th Fejér kernel on the circle $\mathbb{R}/T\mathbb{Z}$, let $\mu$ be the normalized Haar
measure on $\mathbb{R}/T\mathbb{Z}$ (of total mass $1$), and let $e_1(x) = e^{2\pi i x / T}$.
Then $\operatorname{Re} K_N(x) \ge 0$ for every $x \in \mathbb{R}/T\mathbb{Z}$;
$K_N(-x) = K_N(x)$ for every $x \in \mathbb{R}/T\mathbb{Z}$; the function on $\mathbb{R}$ sending
$t$ to $K_N$ evaluated at the class of $t$ in $\mathbb{R}/T\mathbb{Z}$ is $T$-periodic;
$\int K_N \, d\mu = 1$; and for every $\delta > 0$ and every $x \in \mathbb{R}/T\mathbb{Z}$ with
$\delta \le |1 - e_1(x)|$ we have $|K_N(x)| \le \frac{4}{(N+1)\delta^2}$. -/
theorem fejer_kernel_properties (N : ℕ) :
    (∀ x : AddCircle T, 0 ≤ (fejerKernel N x).re) ∧
    (∀ x : AddCircle T, fejerKernel N (-x) = fejerKernel N x) ∧
    (Function.Periodic (fun t : ℝ => fejerKernel (T := T) N (↑t)) T) ∧
    (∫ t : AddCircle T, fejerKernel N t ∂haarAddCircle = 1) ∧
    (∀ δ : ℝ, 0 < δ → ∀ x : AddCircle T,
      δ ≤ ‖(1 : ℂ) - fourier (1 : ℤ) x‖ →
      ‖fejerKernel N x‖ ≤ 4 / (((N : ℝ) + 1) * δ ^ 2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fejerKernel_nonneg N
  · exact fejerKernel_symmetric N
  · intro t
    show fejerKernel (T := T) N ↑(t + T) = fejerKernel (T := T) N ↑t
    congr 1
    exact coe_add_period T t
  · exact integral_fejerKernel N
  · intro δ hδ x hx
    unfold fejerKernel
    rw [fejer_dirichlet_sum_eq_sq, mul_conj, norm_smul, norm_inv,
      show ‖(↑N + 1 : ℂ)‖ = ((N : ℝ) + 1) from by norm_cast,
      show ‖(↑(normSq (∑ k ∈ range (N + 1), (fourier (↑k : ℤ) x : ℂ))) : ℂ)‖ =
        ‖∑ k ∈ range (N + 1), (fourier (↑k : ℤ) x : ℂ)‖ ^ 2 from by
        simp only [Complex.norm_real, normSq_eq_norm_sq]
        exact Real.norm_of_nonneg (sq_nonneg _)]
    have hfne : (fourier (1 : ℤ) x : ℂ) ≠ 1 := by
      intro h; linarith [show ‖(1 : ℂ) - fourier (1 : ℤ) x‖ = 0 from by
        rw [h, sub_self, norm_zero]]
    have hfnorm : ‖fourier (1 : ℤ) x‖ = 1 := by rw [fourier_apply]; exact Circle.norm_coe _
    have hfourier_pow : ∀ k : ℕ, (fourier (↑k : ℤ) x : ℂ) = (fourier (1 : ℤ) x) ^ k := by
      intro k; induction k with
      | zero => simp
      | succ n ih => rw [pow_succ, ← ih, ← fourier_add]; push_cast; ring_nf
    have hG_bound : ‖∑ k ∈ range (N + 1), (fourier (↑k : ℤ) x : ℂ)‖ ≤ 2 / δ := by
      conv_lhs => rw [show ∑ k ∈ range (N + 1), (fourier (↑k : ℤ) x : ℂ) =
        ∑ k ∈ range (N + 1), (fourier (1 : ℤ) x) ^ k from by
        congr 1; ext k; exact hfourier_pow k]
      rw [geom_sum_eq hfne (N + 1), norm_div,
        show ‖(fourier (1 : ℤ) x : ℂ) - 1‖ = ‖(1 : ℂ) - fourier (1 : ℤ) x‖ from
          norm_sub_rev _ _]
      calc ‖(fourier (1 : ℤ) x : ℂ) ^ (N + 1) - 1‖ / ‖(1 : ℂ) - fourier (1 : ℤ) x‖
          ≤ 2 / ‖(1 : ℂ) - fourier (1 : ℤ) x‖ := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            calc ‖(fourier (1 : ℤ) x : ℂ) ^ (N + 1) - 1‖
                ≤ ‖(fourier (1 : ℤ) x : ℂ) ^ (N + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
              _ = 2 := by rw [norm_pow, hfnorm, one_pow, norm_one]; norm_num
        _ ≤ 2 / δ := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hδ hx
    calc ((N : ℝ) + 1)⁻¹ * ‖∑ k ∈ range (N + 1), (fourier (↑k : ℤ) x : ℂ)‖ ^ 2
        ≤ ((N : ℝ) + 1)⁻¹ * (2 / δ) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h_nn := norm_nonneg (∑ k ∈ range (N + 1), (fourier (↑k : ℤ) x : ℂ))
          exact sq_le_sq' (by linarith) hG_bound
      _ ≤ 4 / (((N : ℝ) + 1) * δ ^ 2) := le_of_eq (by field_simp; ring)

end AddCircle
