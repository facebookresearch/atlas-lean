/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.PointCount
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Multiset.MapFold
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Ihara's criterion for Ramanujan graphs

For a natural number `q ≥ 2` and a symmetric integer matrix, this module proves Ihara's
criterion: every complex characteristic root `μ ≠ q + 1` satisfies `‖μ‖ ≤ 2 * √q` if and only if
every complex solution `s` of `1 - μ * q ^ (-s) + q ^ (1 - 2 * s) = 0` has real part `1 / 2`.

Source: Daniel Vallières, *Elliptic Curves over Finite Fields and Ramanujan Graphs on Two
Vertices*, INTEGERS 24 (2024), Article A8, Theorem 2 (`integers-2024-A8-thm-2`).
-/

namespace MetaMathlibExt

@[expose] public section

private lemma natCast_pos_of_two_le {q : ℕ} (hq : 2 ≤ q) : (0 : ℝ) < (q : ℝ) := by
  have h0 : 0 < q := by omega
  exact_mod_cast h0

private lemma natCast_ne_one_of_two_le {q : ℕ} (hq : 2 ≤ q) : (q : ℝ) ≠ 1 := by
  have h1 : q ≠ 1 := by omega
  exact_mod_cast h1

private lemma natCast_ne_zero_complex {q : ℕ} (hq : 2 ≤ q) : (q : ℂ) ≠ 0 := by
  have h0 : q ≠ 0 := by omega
  exact_mod_cast h0

private lemma cpow_one_sub_two_mul (q : ℕ) (hq : 2 ≤ q) (s : ℂ) :
    (q : ℂ) ^ (1 - 2 * s) = (q : ℂ) * ((q : ℂ) ^ (-s)) ^ 2 := by
  have hq0 : (q : ℂ) ≠ 0 := natCast_ne_zero_complex hq
  have hexp : (1 : ℂ) - 2 * s = 1 + (-s) + (-s) := by ring
  rw [hexp, Complex.cpow_add _ _ hq0, Complex.cpow_add _ _ hq0, Complex.cpow_one]
  ring

private lemma norm_cpow_natCast (q : ℕ) (hq : 2 ≤ q) (w : ℂ) :
    ‖(q : ℂ) ^ w‖ = (q : ℝ) ^ w.re := by
  have hqpos : (0 : ℝ) < (q : ℝ) := natCast_pos_of_two_le hq
  rw [← Complex.ofReal_natCast]
  exact Complex.norm_cpow_eq_rpow_re_of_pos hqpos w

private lemma re_eq_half_of_normSq (q : ℕ) (hq : 2 ≤ q) (s u : ℂ)
    (hu : u = (q : ℂ) ^ (-s)) (hsq : ‖u‖ ^ 2 = 1 / (q : ℝ)) : s.re = 1 / 2 := by
  have hqpos : (0 : ℝ) < (q : ℝ) := natCast_pos_of_two_le hq
  have hqne1 : (q : ℝ) ≠ 1 := natCast_ne_one_of_two_le hq
  have hnorm : ‖u‖ = (q : ℝ) ^ (-s.re) := by
    rw [hu, norm_cpow_natCast q hq, Complex.neg_re]
  rw [hnorm] at hsq
  have h2 : ((q : ℝ) ^ (-s.re)) ^ 2 = (q : ℝ) ^ (-s.re * 2) := by
    rw [pow_two, ← Real.rpow_add hqpos]
    congr 1
    ring
  rw [h2] at hsq
  have h3 : (1 : ℝ) / (q : ℝ) = (q : ℝ) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg (le_of_lt hqpos), Real.rpow_one, one_div]
  rw [h3] at hsq
  have hinj := (Real.rpow_right_inj hqpos hqne1).mp hsq
  linarith

private lemma normSq_eq_of_re_eq_half (q : ℕ) (hq : 2 ≤ q) (s u : ℂ)
    (hu : u = (q : ℂ) ^ (-s)) (hs : s.re = 1 / 2) : ‖u‖ ^ 2 = 1 / (q : ℝ) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := natCast_pos_of_two_le hq
  have hnorm : ‖u‖ = (q : ℝ) ^ (-s.re) := by
    rw [hu, norm_cpow_natCast q hq, Complex.neg_re]
  rw [hs] at hnorm
  rw [hnorm]
  have h2 : ((q : ℝ) ^ (-((1 : ℝ) / 2))) ^ 2 = (q : ℝ) ^ (-1 : ℝ) := by
    rw [pow_two, ← Real.rpow_add hqpos]
    congr 1
    ring
  rw [h2, Real.rpow_neg (le_of_lt hqpos), Real.rpow_one, one_div]

private lemma re_eq_half_of_mul_normSq (q : ℕ) (hq : 2 ≤ q) (s u : ℂ)
    (hu : u = (q : ℂ) ^ (-s)) (hsq : (q : ℝ) * ‖u‖ ^ 2 = 1) : s.re = 1 / 2 := by
  have hqpos : (0 : ℝ) < (q : ℝ) := natCast_pos_of_two_le hq
  have hfinal : ‖u‖ ^ 2 = 1 / (q : ℝ) := by
    rw [eq_div_iff (ne_of_gt hqpos)]
    linear_combination hsq
  exact re_eq_half_of_normSq q hq s u hu hfinal

private lemma im_eq_zero_of_mem_aroots {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A.IsSymm) (μ : ℂ) (hμ : μ ∈ A.charpoly.aroots ℂ) : μ.im = 0 := by
  have hBherm : (A.map (algebraMap ℤ ℂ)).IsHermitian := by
    have hA' : A.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hA
    refine hA'.map _ fun x => ?_
    rw [star_trivial, eq_intCast, star_intCast]
  have haroots :
      A.charpoly.aroots ℂ = (A.map (algebraMap ℤ ℂ)).charpoly.roots := by
    rw [Polynomial.aroots_def, ← Matrix.charpoly_map]
  rw [haroots, hBherm.roots_charpoly_eq_eigenvalues, Multiset.mem_map] at hμ
  obtain ⟨i, -, hi⟩ := hμ
  rw [← hi]
  simp

open scoped ComplexConjugate in
private lemma forward_of_quadratic (q : ℕ) (hq : 2 ≤ q) (μ u : ℂ) (hμ : μ.im = 0)
    (hbound : ‖μ‖ ≤ 2 * Real.sqrt q)
    (heq : 1 - μ * u + (q : ℂ) * u ^ 2 = 0) (s : ℂ) (hu : u = (q : ℂ) ^ (-s)) :
    s.re = 1 / 2 := by
  have hμstar : star μ = μ := by
    rw [Complex.star_def]
    exact Complex.conj_eq_iff_im.mpr hμ
  have hconj := congrArg star heq
  simp only [star_add, star_sub, star_mul, star_pow, star_one, star_zero, hμstar,
    star_natCast] at hconj
  have hdiff : (u - star u) * (-μ + (q : ℂ) * (u + star u)) = 0 := by
    linear_combination heq - hconj
  rcases mul_eq_zero.mp hdiff with hcase | hcase
  · have hu_eq : star u = u := by linear_combination -hcase
    have hu_star : conj u = u := by
      rw [← Complex.star_def]
      exact hu_eq
    have hu_ofReal : ((u.re : ℝ) : ℂ) = u := Complex.conj_eq_iff_re.mp hu_star
    have hμ_ofReal : ((μ.re : ℝ) : ℂ) = μ :=
      Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr hμ)
    rw [pow_two, ← hu_ofReal, ← hμ_ofReal] at heq
    have heqR : 1 - μ.re * u.re + (q : ℝ) * (u.re * u.re) = 0 := by
      have h5 := congrArg Complex.re heq
      simpa [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
        Complex.zero_re, mul_zero, zero_mul, sub_zero] using h5
    have hqpos : (0 : ℝ) < (q : ℝ) := natCast_pos_of_two_le hq
    have hmbound : μ.re ^ 2 ≤ 4 * (q : ℝ) := by
      have hμnorm : ‖μ‖ = |μ.re| := (Complex.abs_re_eq_norm.mpr hμ).symm
      have h1 : |μ.re| ≤ 2 * Real.sqrt (q : ℝ) := by
        rw [← hμnorm]
        exact hbound
      obtain ⟨hlo, hhi⟩ := abs_le.mp h1
      have h2 : μ.re ^ 2 ≤ (2 * Real.sqrt (q : ℝ)) ^ 2 := sq_le_sq' hlo hhi
      have hsqrt : (2 * Real.sqrt (q : ℝ)) ^ 2 = 4 * (q : ℝ) := by
        rw [mul_pow, Real.sq_sqrt (le_of_lt hqpos)]
        norm_num
      rw [hsqrt] at h2
      exact h2
    have htsq : (2 * (q : ℝ) * u.re - μ.re) ^ 2 = μ.re ^ 2 - 4 * (q : ℝ) := by
      linear_combination 4 * (q : ℝ) * heqR
    have hsq0 : (2 * (q : ℝ) * u.re - μ.re) ^ 2 = 0 := by
      have hle : (2 * (q : ℝ) * u.re - μ.re) ^ 2 ≤ 0 := by
        rw [htsq]
        linarith [hmbound]
      have hnn : (0 : ℝ) ≤ (2 * (q : ℝ) * u.re - μ.re) ^ 2 := sq_nonneg _
      exact le_antisymm hle hnn
    have ht0 : 2 * (q : ℝ) * u.re - μ.re = 0 := sq_eq_zero_iff.mp hsq0
    have htx : 2 * (q : ℝ) * u.re = μ.re := by linarith [ht0]
    have hm2 : μ.re ^ 2 = 4 * (q : ℝ) := by linarith [htsq, hsq0]
    have h4 : (2 * (q : ℝ) * u.re) ^ 2 = 4 * (q : ℝ) := by rw [htx, hm2]
    have h5 : 4 * (q : ℝ) * ((q : ℝ) * u.re ^ 2) = 4 * (q : ℝ) * 1 := by
      linear_combination h4
    have hcancel : 4 * (q : ℝ) ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hqpos)
    have hqx : (q : ℝ) * u.re ^ 2 = 1 := mul_left_cancel₀ hcancel h5
    have huim : u.im = 0 := Complex.conj_eq_iff_im.mp hu_star
    have hunorm : ‖u‖ = |u.re| := (Complex.abs_re_eq_norm.mpr huim).symm
    have hsq : (q : ℝ) * ‖u‖ ^ 2 = 1 := by
      rw [hunorm, sq_abs]
      exact hqx
    exact re_eq_half_of_mul_normSq q hq s u hu hsq
  · have hμeq : μ = (q : ℂ) * (u + star u) := by linear_combination -hcase
    rw [hμeq] at heq
    have heq' : 1 - (q : ℂ) * (u * star u) = 0 := by linear_combination heq
    have hstar : u * star u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hstar] at heq'
    have hsq : (q : ℝ) * ‖u‖ ^ 2 = 1 := by
      have h5 := congrArg Complex.re heq'
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.natCast_re,
        Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
        mul_zero, sub_zero] at h5
      linarith
    exact re_eq_half_of_mul_normSq q hq s u hu hsq

private lemma exists_cpow_neg_eq (q : ℕ) (hq : 2 ≤ q) (u : ℂ) (hu0 : u ≠ 0) :
    ∃ s : ℂ, (q : ℂ) ^ (-s) = u := by
  have hq0 : (q : ℂ) ≠ 0 := natCast_ne_zero_complex hq
  have hq1 : (1 : ℝ) < (q : ℝ) := by
    have h1 : 1 < q := by omega
    exact_mod_cast h1
  have hpos : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hlog : Complex.log (q : ℂ) = ((Real.log (q : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast]
    exact (Complex.ofReal_log (Nat.cast_nonneg q)).symm
  have hlogq : Complex.log (q : ℂ) ≠ 0 := by
    rw [hlog, ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hpos
  refine ⟨-(Complex.log u / Complex.log (q : ℂ)), ?_⟩
  rw [Complex.cpow_def_of_ne_zero hq0]
  have hcancel :
      Complex.log (q : ℂ) * -(-(Complex.log u / Complex.log (q : ℂ))) =
        Complex.log u := by
    rw [neg_neg, mul_div_cancel₀ _ hlogq]
  rw [hcancel, Complex.exp_log hu0]

private lemma false_of_bad_root (q : ℕ) (hq : 2 ≤ q) (μ u : ℂ)
    (hP : ∀ s : ℂ,
      1 - μ * (q : ℂ) ^ (-s) + (q : ℂ) ^ (1 - 2 * s) = 0 → s.re = 1 / 2)
    (heq : 1 - μ * u + (q : ℂ) * u ^ 2 = 0) (hne : ‖u‖ ^ 2 ≠ 1 / (q : ℝ)) :
    False := by
  have hu0 : u ≠ 0 := by
    intro hzero
    rw [hzero] at heq
    simp at heq
  obtain ⟨s, hs⟩ := exists_cpow_neg_eq q hq u hu0
  have heq' : 1 - μ * (q : ℂ) ^ (-s) + (q : ℂ) ^ (1 - 2 * s) = 0 := by
    rw [hs, cpow_one_sub_two_mul q hq s, hs]
    exact heq
  have hre := hP s heq'
  exact hne (normSq_eq_of_re_eq_half q hq s u hs.symm hre)

private lemma bound_of_re_property (q : ℕ) (hq : 2 ≤ q) (μ : ℂ)
    (hP : ∀ s : ℂ,
      1 - μ * (q : ℂ) ^ (-s) + (q : ℂ) ^ (1 - 2 * s) = 0 → s.re = 1 / 2) :
    ‖μ‖ ≤ 2 * Real.sqrt q := by
  by_contra hcon
  rw [not_le] at hcon
  have hq0 : (q : ℂ) ≠ 0 := natCast_ne_zero_complex hq
  obtain ⟨d, hd⟩ := Complex.isSquare (μ ^ 2 - 4 * (q : ℂ))
  have hdisc : discrim (q : ℂ) (-μ) 1 = d * d := by
    simp only [discrim]
    linear_combination hd
  have hroots := quadratic_eq_zero_iff (a := (q : ℂ)) (b := -μ) (c := 1) hq0 hdisc
  simp only [neg_neg] at hroots
  have heq_of_root : ∀ x : ℂ, (q : ℂ) * (x * x) + -μ * x + 1 = 0 →
      1 - μ * x + (q : ℂ) * x ^ 2 = 0 := by
    intro x hx
    linear_combination hx
  have hroot₁ : 1 - μ * ((μ + d) / (2 * (q : ℂ))) +
      (q : ℂ) * ((μ + d) / (2 * (q : ℂ))) ^ 2 = 0 :=
    heq_of_root _ ((hroots ((μ + d) / (2 * (q : ℂ)))).mpr (Or.inl rfl))
  have hroot₂ : 1 - μ * ((μ - d) / (2 * (q : ℂ))) +
      (q : ℂ) * ((μ - d) / (2 * (q : ℂ))) ^ 2 = 0 :=
    heq_of_root _ ((hroots ((μ - d) / (2 * (q : ℂ)))).mpr (Or.inr rfl))
  have h2q : (2 : ℂ) * (q : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hq0
  have hsum : (μ + d) / (2 * (q : ℂ)) + (μ - d) / (2 * (q : ℂ)) = μ / (q : ℂ) := by
    field_simp
    ring
  have hμeq : μ = (q : ℂ) * ((μ + d) / (2 * (q : ℂ)) + (μ - d) / (2 * (q : ℂ))) := by
    rw [hsum, mul_div_cancel₀ _ hq0]
  have hqnorm : ‖(q : ℂ)‖ = (q : ℝ) := by
    rw [← Complex.ofReal_natCast, Complex.norm_real,
      Real.norm_of_nonneg (Nat.cast_nonneg q)]
  have hnorm_le : ‖μ‖ ≤ (q : ℝ) *
      (‖(μ + d) / (2 * (q : ℂ))‖ + ‖(μ - d) / (2 * (q : ℂ))‖) := by
    have h := congrArg (‖·‖) hμeq
    rw [h, norm_mul, hqnorm]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Nat.cast_nonneg q)
  have hnot : ¬ (‖(μ + d) / (2 * (q : ℂ))‖ ^ 2 = 1 / (q : ℝ) ∧
      ‖(μ - d) / (2 * (q : ℂ))‖ ^ 2 = 1 / (q : ℝ)) := by
    rintro ⟨h1, h2⟩
    have hqpos : (0 : ℝ) < (q : ℝ) := natCast_pos_of_two_le hq
    have hsqrt2 : (1 / Real.sqrt (q : ℝ)) ^ 2 = 1 / (q : ℝ) := by
      rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hqpos)]
    have hu₁ : ‖(μ + d) / (2 * (q : ℂ))‖ = 1 / Real.sqrt (q : ℝ) := by
      have h := h1
      rw [← hsqrt2] at h
      exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp h
    have hu₂ : ‖(μ - d) / (2 * (q : ℂ))‖ = 1 / Real.sqrt (q : ℝ) := by
      have h := h2
      rw [← hsqrt2] at h
      exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp h
    have hle : ‖μ‖ ≤ 2 * Real.sqrt (q : ℝ) := by
      calc ‖μ‖ ≤ (q : ℝ) *
            (‖(μ + d) / (2 * (q : ℂ))‖ + ‖(μ - d) / (2 * (q : ℂ))‖) := hnorm_le
        _ = (q : ℝ) * (2 / Real.sqrt (q : ℝ)) := by rw [hu₁, hu₂]; ring
        _ = 2 * Real.sqrt (q : ℝ) := by
            have hfactor : (q : ℝ) * (2 / Real.sqrt (q : ℝ)) =
              2 * ((q : ℝ) / Real.sqrt (q : ℝ)) := by ring
            rw [hfactor, Real.div_sqrt]
    linarith [hcon, hle]
  have hcases : ‖(μ + d) / (2 * (q : ℂ))‖ ^ 2 ≠ 1 / (q : ℝ) ∨
      ‖(μ - d) / (2 * (q : ℂ))‖ ^ 2 ≠ 1 / (q : ℝ) := by
    by_contra hcon2
    simp only [not_or, not_not] at hcon2
    exact hnot hcon2
  rcases hcases with hne | hne
  · exact false_of_bad_root q hq μ _ hP hroot₁ hne
  · exact false_of_bad_root q hq μ _ hP hroot₂ hne

/-- **Ihara's criterion for Ramanujan graphs.** Let $q \ge 2$ be a natural number and let $A$ be a
symmetric $n \times n$ matrix with integer entries. Every complex root $\mu \ne q + 1$ of the
characteristic polynomial of $A$ satisfies $|\mu| \le 2\sqrt{q}$ if and only if, for every such
root $\mu \ne q + 1$, every complex number $s$ with $1 - \mu q^{-s} + q^{1 - 2s} = 0$ has real
part $1/2$.

The source (Section 2.1.3 and Theorem 2) takes $X$ to be a connected $(q + 1)$-regular graph with
at least two vertices. Then $q + 1$ is an eigenvalue of the adjacency matrix $A$ of $X$ of
multiplicity one, and $X$ is called Ramanujan when every eigenvalue $\mu \ne q + 1$ of $A$
satisfies $|\mu| \le 2\sqrt{q}$. This convention excludes only the endpoint $+(q + 1)$: the
eigenvalue $-(q + 1)$ of a bipartite graph is retained. For example, $K_{3,3}$ ($q = 2$) has the
eigenvalue $-3$ with $|-3| = 3 > 2\sqrt{2}$, so it is not Ramanujan in the source's sense, and
its factor $1 + 3q^{-s} + q^{1 - 2s}$ has zeros on $\mathrm{Re}(s) = 0$ and $\mathrm{Re}(s) = 1$;
it is Ramanujan under the convention that excludes both endpoints $\pm(q + 1)$. Under the source's
hypotheses and convention, the left side above says that $X$ is Ramanujan, and, writing
$\zeta_X$ for the Ihara zeta function of $X$, the numbers $s$ on the right are the non-trivial
zeros of $Q_X(s) = \zeta_X(q^{-s})^{-1}$, that is, the zeros of
$P_X(q^{-s}) = \prod_{\mu \ne q + 1} (1 - \mu q^{-s} + q^{1 - 2s})$; this recovers Theorem 2.

The theorem itself is a statement about matrices, proved root by root: it needs no graph
hypotheses, and it treats a root $-(q + 1)$ like every other root $\mu \ne q + 1$. The roots
$\mu$ are real because $A$ is symmetric.

Source: Daniel Vallières, *Elliptic Curves over Finite Fields and Ramanujan Graphs on Two
Vertices*, INTEGERS 24 (2024), Article A8, Theorem 2 (`integers-2024-A8-thm-2`). -/
public theorem ramanujan_iff_nontrivial_zeros_re_eq_half {n q : ℕ} (hq : 2 ≤ q)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.IsSymm) :
    (∀ μ ∈ A.charpoly.aroots ℂ, μ ≠ (q : ℂ) + 1 → ‖μ‖ ≤ 2 * Real.sqrt q) ↔
      ∀ μ ∈ A.charpoly.aroots ℂ, μ ≠ (q : ℂ) + 1 → ∀ s : ℂ,
        1 - μ * (q : ℂ) ^ (-s) + (q : ℂ) ^ (1 - 2 * s) = 0 → s.re = 1 / 2 := by
  constructor
  · intro hbound μ hμ hμq s heq
    have him : μ.im = 0 := im_eq_zero_of_mem_aroots A hA μ hμ
    have hsplit : (q : ℂ) ^ (1 - 2 * s) = (q : ℂ) * ((q : ℂ) ^ (-s)) ^ 2 :=
      cpow_one_sub_two_mul q hq s
    rw [hsplit] at heq
    exact forward_of_quadratic q hq μ _ him (hbound μ hμ hμq) heq s rfl
  · intro hP μ hμ hμq
    exact bound_of_re_property q hq μ (hP μ hμ hμq)

end

end MetaMathlibExt
