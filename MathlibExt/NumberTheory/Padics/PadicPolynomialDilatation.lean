/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Padic polynomial dilatation

Source: W. A. Zuniga-Galindo, *Computing Igusa's Local Zeta Functions of
Univariate Polynomials, and Linear Feedback Shift Registers*, Journal of
Integer Sequences 6 (2003), Article 03.3.6,
<https://cs.uwaterloo.ca/journals/JIS/VOL6/Zuniga/zuniga51.tex>,
p-adic stationary phase setup and dilatation definition, lines 314-324
(`f_{x_0}(x) = p^{-e} f(x_0 + px)` with `e` the minimum p-order,
calling `f_{x_0}` the dilatation of `f` at `x_0`).

Atomic claim: for a polynomial over the p-adic integers with at least one
unit coefficient, and every p-adic integer point, the scaled translate by
`x0 + p * X` divided by the minimal uniform power of `p` stays integral
with at least one unit coefficient.
-/

@[expose] public section

/-- **Dilatation of a p-adic polynomial at a point.** Let $p$ be a prime, $f \in \mathbb{Z}_p[X]$
and $x_0 \in \mathbb{Z}_p$. Dilatation data for $f$ at $x_0$ consist of a natural number $e$ and a
polynomial $g \in \mathbb{Z}_p[X]$ such that $g(X) = p^{-e} f(x_0 + pX)$ as polynomials over
$\mathbb{Q}_p$, and the reduction of $g$ modulo $p$ is nonzero. -/
structure PadicPolynomialDilatation (p : ℕ) [Fact p.Prime]
    (f : Polynomial (PadicInt p)) (x0 : PadicInt p) where
  exp : ℕ
  poly : Polynomial (PadicInt p)
  dilat_eq :
    Polynomial.map (algebraMap (PadicInt p) (Padic p)) poly =
      Polynomial.C (((p : Padic p) ^ exp)⁻¹) *
        Polynomial.map (algebraMap (PadicInt p) (Padic p))
          (f.comp (Polynomial.C x0 + Polynomial.C (p : PadicInt p) * Polynomial.X))
  red_ne_zero : Polynomial.map PadicInt.toZMod poly ≠ 0

/-- **Dilatation of the constant polynomial one at zero.** For every prime $p$, the exponent
$e = 0$ and the polynomial $g = 1$ form dilatation data for the constant polynomial
$1 \in \mathbb{Z}_p[X]$ at the point $x_0 = 0$. -/
noncomputable def padicPolynomialDilatation_one_zero (p : ℕ) [Fact p.Prime] :
    PadicPolynomialDilatation p 1 0 where
  exp := 0
  poly := 1
  dilat_eq := by
    simp only [Polynomial.one_comp, Polynomial.map_one, pow_zero, inv_one,
      Polynomial.C_1, mul_one]
  red_ne_zero := by
    simp only [Polynomial.map_one]
    exact one_ne_zero

/-- **Existence of dilatations of p-adic polynomials.** Let $p$ be a prime and let
$f \in \mathbb{Z}_p[X]$ have nonzero reduction modulo $p$. Then for every $x_0 \in \mathbb{Z}_p$
there are a natural number $e$ and a polynomial $g \in \mathbb{Z}_p[X]$ with nonzero reduction
modulo $p$ such that $g(X) = p^{-e} f(x_0 + pX)$ as polynomials over $\mathbb{Q}_p$; that is,
dilatation data for $f$ at $x_0$ exist.

Proves `Wanted` entry `padicPolynomialDilatation_exists`.
-/
theorem padicPolynomialDilatation_exists (p : ℕ) [Fact p.Prime]
    (f : Polynomial (PadicInt p)) (x0 : PadicInt p)
    (hf : Polynomial.map PadicInt.toZMod f ≠ 0) :
    Nonempty (PadicPolynomialDilatation p f x0) := by
  classical
  have hp0 : (p : PadicInt p) ≠ 0 := by
    refine ne_of_apply_ne PadicInt.valuation ?_
    rw [PadicInt.valuation_p, PadicInt.valuation_zero]
    exact one_ne_zero
  have hf0 : f ≠ 0 := by
    intro hcon
    subst hcon
    simp at hf
  have hC0 : ∀ (a : PadicInt p), (Polynomial.C a).coeff 1 = 0 := by
    intro a
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (by rw [Polynomial.natDegree_C]; exact one_pos)
  set q : Polynomial (PadicInt p) :=
    Polynomial.C x0 + Polynomial.C (p : PadicInt p) * Polynomial.X with hqdef
  have hq1 : q.coeff 1 = (p : PadicInt p) := by
    rw [hqdef, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_one,
      mul_one, hC0 x0, zero_add]
  set g0 : Polynomial (PadicInt p) := f.comp q with hg0def
  have hg00 : g0 ≠ 0 := by
    intro hcon
    rw [hg0def] at hcon
    rw [Polynomial.comp_eq_zero_iff] at hcon
    rcases hcon with h | ⟨_, hqq⟩
    · exact hf0 h
    · have h2 : q.coeff 1 = 0 := by
        rw [hqq]
        exact hC0 _
      rw [hq1] at h2
      exact hp0 h2
  set T : Finset ℕ :=
    (Finset.range (g0.natDegree + 1)).filter (fun i => g0.coeff i ≠ 0) with hTdef
  obtain ⟨i0, hi0⟩ : ∃ i, g0.coeff i ≠ 0 := by
    by_contra hcon
    rw [not_exists] at hcon
    apply hg00
    ext i
    simp [not_not.mp (hcon i)]
  have hi0lt : i0 < g0.natDegree + 1 := by
    by_contra hcon
    exact hi0 (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
  have hTne : T.Nonempty := by
    refine ⟨i0, ?_⟩
    rw [hTdef]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi0lt, hi0⟩
  set S : Finset ℕ := T.image (fun i => PadicInt.valuation (g0.coeff i)) with hSdef
  have hSne : S.Nonempty := hTne.image _
  set e : ℕ := S.min' hSne with hedef
  have he_mem : e ∈ S := Finset.min'_mem S hSne
  rw [hSdef] at he_mem
  obtain ⟨j, hjT, hje⟩ := Finset.mem_image.mp he_mem
  have hje' : PadicInt.valuation (g0.coeff j) = e := hje
  have hj_ne : g0.coeff j ≠ 0 := by
    rw [hTdef] at hjT
    exact (Finset.mem_filter.mp hjT).2
  have hmem : ∀ i : ℕ, g0.coeff i ≠ 0 → PadicInt.valuation (g0.coeff i) ∈ S := by
    intro i hi
    have hir : i ∈ Finset.range (g0.natDegree + 1) := by
      rw [Finset.mem_range]
      by_contra hcon
      exact hi (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
    have hiT : i ∈ T := by
      rw [hTdef]
      exact Finset.mem_filter.mpr ⟨hir, hi⟩
    rw [hSdef]
    exact Finset.mem_image.mpr ⟨i, hiT, rfl⟩
  have hle : ∀ i : ℕ, g0.coeff i ≠ 0 → e ≤ PadicInt.valuation (g0.coeff i) := by
    intro i hi
    rw [hedef]
    exact Finset.min'_le S _ (hmem i hi)
  have hdiv : ∀ i : ℕ, (p : PadicInt p) ^ e ∣ g0.coeff i := by
    intro i
    by_cases hi : g0.coeff i = 0
    · rw [hi]
      exact dvd_zero _
    · have hspan :=
        (PadicInt.mem_span_pow_iff_le_valuation (g0.coeff i) hi e).mpr (hle i hi)
      exact Ideal.mem_span_singleton.mp hspan
  obtain ⟨g, hg⟩ : Polynomial.C ((p : PadicInt p) ^ e) ∣ g0 :=
    (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hdiv
  have hA : (p : Padic p) ^ e ≠ 0 := by
    apply pow_ne_zero
    refine ne_of_apply_ne Padic.valuation ?_
    rw [Padic.valuation_p, Padic.valuation_zero]
    exact one_ne_zero
  have hpe_ne : (p : PadicInt p) ^ e ≠ 0 := pow_ne_zero _ hp0
  have hmap : Polynomial.map (algebraMap (PadicInt p) (Padic p)) g0
      = Polynomial.C ((p : Padic p) ^ e)
        * Polynomial.map (algebraMap (PadicInt p) (Padic p)) g := by
    rw [hg, Polynomial.map_mul, Polynomial.map_C, map_pow, map_natCast]
  have hgj : g0.coeff j = (p : PadicInt p) ^ e * g.coeff j := by
    rw [hg]
    exact Polynomial.coeff_C_mul g
  have hgj_ne : g.coeff j ≠ 0 := by
    intro hcon
    exact hj_ne (by rw [hgj, hcon, mul_zero])
  have hval_g : PadicInt.valuation (g.coeff j) = 0 := by
    have h1 : PadicInt.valuation (g0.coeff j)
        = PadicInt.valuation ((p : PadicInt p) ^ e)
          + PadicInt.valuation (g.coeff j) := by
      rw [hgj]
      exact PadicInt.valuation_mul hpe_ne hgj_ne
    have hpe_val : PadicInt.valuation ((p : PadicInt p) ^ e) = e := by
      rw [PadicInt.valuation_pow, PadicInt.valuation_p, mul_one]
    rw [hje', hpe_val] at h1
    omega
  have hunit : IsUnit (g.coeff j) := by
    rw [PadicInt.unitCoeff_spec hgj_ne, hval_g, pow_zero, mul_one]
    exact Units.isUnit _
  have hredj : PadicInt.toZMod (g.coeff j) ≠ 0 := (hunit.map PadicInt.toZMod).ne_zero
  have hred : Polynomial.map PadicInt.toZMod g ≠ 0 := by
    intro hcon
    apply hredj
    have hcc := congrArg (fun r => Polynomial.coeff r j) hcon
    simpa [Polynomial.coeff_map] using hcc
  have hmap' : Polynomial.map (algebraMap (PadicInt p) (Padic p)) g
      = Polynomial.C (((p : Padic p) ^ e)⁻¹)
        * Polynomial.map (algebraMap (PadicInt p) (Padic p)) g0 := by
    rw [hmap, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hA, Polynomial.C_1,
      one_mul]
  exact ⟨{ exp := e, poly := g, dilat_eq := hmap', red_ne_zero := hred }⟩

end
