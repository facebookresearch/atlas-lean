/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Modular
public import MathlibExt.Analysis.SpecialFunctions.Elliptic.ComplexMultiplication
public import MathlibExt.Analysis.SpecialFunctions.Elliptic.Homothety
public import MathlibExt.NumberTheory.QuadraticForms.Reduced
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Roots of binary quadratic forms and their lattices

For an integer triple $(a, b, c)$ standing for the binary quadratic form $ax^2 + bxy + cy^2$, a
root of the form is a complex number $\tau$ with $a\tau^2 + b\tau + c = 0$. This file relates the
forms to the lattices $\mathbb{Z} + \mathbb{Z}\tau$ of their roots and to the action of
$\mathrm{SL}_2(\mathbb{Z})$ on the upper half-plane:

* `BinaryQuadraticForm.endomorphismRing_ofTau`: for a primitive form of negative discriminant, the
  endomorphism ring of $\mathbb{Z} + \mathbb{Z}\tau$ is $\mathbb{Z} + \mathbb{Z}a\tau$, an order of
  discriminant $b^2 - 4ac$;
* `PeriodPair.isHomothetic_ofTau_iff`: for $\tau, \tau'$ in the upper half-plane, the lattices
  $\mathbb{Z} + \mathbb{Z}\tau$ and $\mathbb{Z} + \mathbb{Z}\tau'$ are homothetic exactly when
  $\tau' = \gamma\tau$ for some $\gamma \in \mathrm{SL}_2(\mathbb{Z})$;
* `BinaryQuadraticForm.substitute` and `BinaryQuadraticForm.ProperlyEquivalent`: the substitution
  $f(px + qy, rx + sy)$ and proper equivalence of forms;
* `BinaryQuadraticForm.substitute_root`, `BinaryQuadraticForm.eq_of_root` and
  `BinaryQuadraticForm.properlyEquivalent_iff_exists_smul`: a substitution moves the root of a form
  by $\gamma^{-1}$, a primitive form with positive leading coefficient is determined by its root in
  the upper half-plane, and two such forms are properly equivalent exactly when their roots lie in
  one $\mathrm{SL}_2(\mathbb{Z})$-orbit;
* `BinaryQuadraticForm.isGaussReduced_iff_root_mem`: a positive definite form is Gauss reduced
  exactly when its root lies in the standard half-open fundamental domain, and
  `BinaryQuadraticForm.root_mem_fd_iff` describes membership in Mathlib's closed domain
  `ModularGroup.fd`.

The sources are Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare,
Fall 2025, Lectures 15 and 17, and David Cox, John McKay and Peter Stevenhagen, *Principal moduli
and class fields*, Bull. London Math. Soc. 36 (2004), 3–12, §2.
-/

@[expose] public section

open Complex UpperHalfPlane
open scoped Pointwise MatrixGroups ComplexConjugate

namespace BinaryQuadraticForm

/-- Two integers `α` and `β` with `α z + β = 0` for a non-real `z` both vanish. -/
theorem int_eq_zero_of_mul_add_eq_zero {z : ℂ} (hz : z.im ≠ 0) {α β : ℤ}
    (h : (α : ℂ) * z + β = 0) : α = 0 ∧ β = 0 := by
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero, zero_im, mul_eq_zero,
    Int.cast_eq_zero, add_re, mul_re, sub_zero, zero_re] at him hre
  rcases him with him | him
  · subst him
    simpa using hre
  · exact absurd him hz

/-- For integers `r` and `s`, not both zero, and a non-real `z`, `r z + s ≠ 0`. -/
theorem int_mul_add_ne_zero {z : ℂ} (hz : z.im ≠ 0) {r s : ℤ} (h : r ≠ 0 ∨ s ≠ 0) :
    (r : ℂ) * z + s ≠ 0 := by
  intro h'
  obtain ⟨hr, hs⟩ := int_eq_zero_of_mul_add_eq_zero hz h'
  tauto

/-- If `k` divides `n a`, `n b` and `n c` for a primitive triple `(a, b, c)`, then `k ∣ n`. -/
theorem dvd_of_dvd_mul_of_primitive {a b c : ℤ} (hprim : Int.gcd (Int.gcd a b : ℤ) c = 1)
    {k n : ℤ} (ha : k ∣ n * a) (hb : k ∣ n * b) (hc : k ∣ n * c) : k ∣ n := by
  have h1 := Int.gcd_eq_gcd_ab (Int.gcd a b : ℤ) c
  have h2 := Int.gcd_eq_gcd_ab a b
  rw [hprim] at h1
  have e : n = n * a * (a.gcdA b * (Int.gcd a b : ℤ).gcdA c) +
      n * b * (a.gcdB b * (Int.gcd a b : ℤ).gcdA c) + n * c * (Int.gcd a b : ℤ).gcdB c := by
    have h1' : (1 : ℤ) = (Int.gcd a b : ℤ) * (Int.gcd a b : ℤ).gcdA c +
        c * (Int.gcd a b : ℤ).gcdB c := by exact_mod_cast h1
    linear_combination n * h1' + (n * (Int.gcd a b : ℤ).gcdA c) * h2
  rw [e]
  exact dvd_add (dvd_add (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_left hb _))
    (dvd_mul_of_dvd_left hc _)

section Root

variable {a b c : ℤ} {τ : ℂ}

/-- A root `τ` of `a τ² + b τ + c` satisfies `(2 a τ + b)² = b² - 4ac`. -/
theorem two_mul_root_add_sq (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) :
    (2 * (a : ℂ) * τ + b) ^ 2 = (discrim a b c : ℤ) := by
  push_cast [discrim]
  linear_combination 4 * (a : ℂ) * hτ

/-- A complex root of `a τ² + b τ + c` with `b² - 4ac < 0` is not real. -/
theorem im_ne_zero_of_root (hD : discrim a b c < 0) (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) :
    τ.im ≠ 0 := by
  intro h0
  have h := congrArg Complex.re (two_mul_root_add_sq hτ)
  simp [sq, h0] at h
  have hD' : ((discrim a b c : ℤ) : ℝ) < 0 := by exact_mod_cast hD
  nlinarith [mul_self_nonneg (2 * (a : ℝ) * τ.re + b)]

/-- The complex conjugate of a root of an integer quadratic is a root. -/
theorem conj_root (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) :
    (a : ℂ) * conj τ ^ 2 + b * conj τ + c = 0 := by
  have := congrArg conj hτ
  simpa using this

/-- For a non-real root `τ` of `a τ² + b τ + c`, `a (τ + τ̄) = -b`. -/
theorem mul_root_add_conj (hτ0 : τ.im ≠ 0) (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) :
    (a : ℂ) * (τ + conj τ) = -b := by
  have h := conj_root hτ
  have hne : τ - conj τ ≠ 0 := by
    intro h'
    have := congrArg Complex.im h'
    simp at this
    exact hτ0 (by linarith)
  have : (τ - conj τ) * ((a : ℂ) * (τ + conj τ) + b) = 0 := by
    linear_combination hτ - h
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 hne
  · linear_combination h1

/-- For a non-real root `τ` of `a τ² + b τ + c`, `a τ τ̄ = c`. -/
theorem mul_root_mul_conj (hτ0 : τ.im ≠ 0) (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) :
    (a : ℂ) * τ * conj τ = c := by
  have h := mul_root_add_conj hτ0 hτ
  linear_combination -hτ + τ * h

/-- For a non-real root `τ` of `a τ² + b τ + c`, `2 a re(τ) = -b`. -/
theorem two_mul_mul_re_root (hτ0 : τ.im ≠ 0) (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) :
    2 * (a : ℝ) * τ.re = -b := by
  have h := congrArg Complex.re (mul_root_add_conj hτ0 hτ)
  simp at h
  linarith

/-- For a non-real root `τ` of `a τ² + b τ + c`, `a |τ|² = c`. -/
theorem mul_normSq_root (hτ0 : τ.im ≠ 0) (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) :
    (a : ℝ) * normSq τ = c := by
  have h := mul_root_mul_conj hτ0 hτ
  rw [mul_assoc, mul_conj] at h
  exact_mod_cast h

/-- Two roots in the upper half-plane of `a τ² + b τ + c` with `a ≠ 0` are equal. -/
theorem root_unique (ha : a ≠ 0) {τ₁ τ₂ : ℍ}
    (h₁ : (a : ℂ) * (τ₁ : ℂ) ^ 2 + b * τ₁ + c = 0) (h₂ : (a : ℂ) * (τ₂ : ℂ) ^ 2 + b * τ₂ + c = 0) :
    τ₁ = τ₂ := by
  have : ((τ₁ : ℂ) - τ₂) * ((a : ℂ) * (τ₁ + τ₂) + b) = 0 := by linear_combination h₁ - h₂
  rcases mul_eq_zero.mp this with h | h
  · exact UpperHalfPlane.ext (sub_eq_zero.mp h)
  · have him := congrArg Complex.im h
    simp only [add_im, mul_im, intCast_re, coe_im, intCast_im, add_re, coe_re, zero_mul, add_zero,
      zero_im, mul_eq_zero, Int.cast_eq_zero] at him
    rcases him with him | him
    · exact absurd him ha
    · have := τ₁.im_pos
      have := τ₂.im_pos
      linarith

end Root

end BinaryQuadraticForm

namespace PeriodPair

/-- **The lattice of a non-real complex number.** For $\tau \in \mathbb{C}$ with
$\mathrm{im}(\tau) \ne 0$, the period pair $(1, \tau)$, whose lattice is
$\mathbb{Z} + \mathbb{Z}\tau$. -/
def ofTau (τ : ℂ) (hτ : τ.im ≠ 0) : PeriodPair where
  ω₁ := 1
  ω₂ := τ
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp only [real_smul, mul_one, add_im, ofReal_im, mul_im, ofReal_re, zero_mul, add_zero,
      zero_add, zero_im, mul_eq_zero, add_re, mul_re, sub_zero, zero_re] at him hre
    rcases him with him | him
    · subst him
      simpa using hre
    · exact absurd him hτ

@[simp] theorem ofTau_ω₁ (τ : ℂ) (hτ : τ.im ≠ 0) : (ofTau τ hτ).ω₁ = 1 := rfl

@[simp] theorem ofTau_ω₂ (τ : ℂ) (hτ : τ.im ≠ 0) : (ofTau τ hτ).ω₂ = τ := rfl

theorem mem_lattice_ofTau {τ : ℂ} {hτ : τ.im ≠ 0} {z : ℂ} :
    z ∈ (ofTau τ hτ).lattice ↔ ∃ m n : ℤ, z = m + n * τ := by
  rw [mem_lattice]
  simp only [ofTau_ω₁, ofTau_ω₂, mul_one]
  exact ⟨fun ⟨m, n, h⟩ ↦ ⟨m, n, h.symm⟩, fun ⟨m, n, h⟩ ↦ ⟨m, n, h.symm⟩⟩

/-- **Homothety of the lattices of two points of the upper half-plane.** For $\tau$ and $\tau'$ in
the upper half-plane $\mathbb{H}$, the lattices $\mathbb{Z} + \mathbb{Z}\tau$ and
$\mathbb{Z} + \mathbb{Z}\tau'$ are homothetic if and only if
$\tau' = \gamma\tau = \frac{p\tau + q}{r\tau + s}$ for some
$\gamma = \begin{pmatrix} p & q \\ r & s \end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare, Fall
2025, Lecture 15, Lemma 15.9 and its proof, which derives $\tau' = \gamma\tau$ with
$\det\gamma = 1$ from the homothety; the converse, by a change of basis of $[1, \tau]$, is written
out here. -/
theorem isHomothetic_ofTau_iff (τ τ' : ℍ) :
    (ofTau τ τ.im_pos.ne').IsHomothetic (ofTau τ' τ'.im_pos.ne') ↔
      ∃ γ : SL(2, ℤ), τ' = γ • τ := by
  have hτ0 : (τ : ℂ).im ≠ 0 := τ.im_pos.ne'
  constructor
  · rintro ⟨l, hl, hL⟩
    have mem' : ∀ z, z ∈ ((ofTau τ' τ'.im_pos.ne').lattice : Set ℂ) ↔
        ∃ y ∈ ((ofTau τ τ.im_pos.ne').lattice : Set ℂ), l * y = z := by
      intro z
      rw [hL, Set.mem_smul_set]
      rfl
    obtain ⟨y₁, hy₁, e₁⟩ := (mem' 1).mp (ofTau (τ' : ℂ) τ'.im_pos.ne').ω₁_mem_lattice
    obtain ⟨y₂, hy₂, e₂⟩ := (mem' τ').mp (ofTau (τ' : ℂ) τ'.im_pos.ne').ω₂_mem_lattice
    obtain ⟨s, r, rfl⟩ := mem_lattice_ofTau.mp hy₁
    obtain ⟨q, p, rfl⟩ := mem_lattice_ofTau.mp hy₂
    obtain ⟨u, v, ev⟩ := mem_lattice_ofTau.mp ((mem' l).mpr
      ⟨1, (ofTau (τ : ℂ) τ.im_pos.ne').ω₁_mem_lattice, mul_one l⟩)
    obtain ⟨x, y, ey⟩ := mem_lattice_ofTau.mp ((mem' (l * τ)).mpr
      ⟨τ, (ofTau (τ : ℂ) τ.im_pos.ne').ω₂_mem_lattice, rfl⟩)
    -- `1 = u (rτ + s) + v (pτ + q)` and `τ = x (rτ + s) + y (pτ + q)`
    have k₁ : ((u * r + v * p : ℤ) : ℂ) * τ + ((u * s + v * q - 1 : ℤ) : ℂ) = 0 := by
      have : l * (((u * r + v * p : ℤ) : ℂ) * τ + ((u * s + v * q - 1 : ℤ) : ℂ)) = 0 := by
        push_cast
        linear_combination (-1 : ℂ) * ev + u * e₁ + v * e₂
      simpa [hl] using this
    have k₂ : ((x * r + y * p - 1 : ℤ) : ℂ) * τ + ((x * s + y * q : ℤ) : ℂ) = 0 := by
      have : l * (((x * r + y * p - 1 : ℤ) : ℂ) * τ + ((x * s + y * q : ℤ) : ℂ)) = 0 := by
        push_cast
        linear_combination (-1 : ℂ) * ey + x * e₁ + y * e₂
      simpa [hl] using this
    obtain ⟨hA, hB⟩ := BinaryQuadraticForm.int_eq_zero_of_mul_add_eq_zero hτ0 k₁
    obtain ⟨hC, hD⟩ := BinaryQuadraticForm.int_eq_zero_of_mul_add_eq_zero hτ0 k₂
    have hdet : (y * u - x * v) * (p * s - q * r) = 1 := by
      linear_combination (v * q + u * s) * hC + hB - (v * p + u * r) * hD
    -- the sign of the determinant, from the imaginary parts
    have hrel : (τ' : ℂ) * ((r : ℂ) * τ + s) = (p : ℂ) * τ + q := by
      linear_combination ((p : ℂ) * τ + q) * e₁ - ((r : ℂ) * τ + s) * e₂
    have hre := congrArg Complex.re hrel
    have him := congrArg Complex.im hrel
    simp only [mul_re, coe_re, add_re, intCast_re, intCast_im, coe_im, zero_mul, sub_zero, add_im,
      mul_im, add_zero] at hre him
    have key : τ'.im * ((r * τ.re + s) ^ 2 + (r * τ.im) ^ 2) = (p * s - q * r) * τ.im := by
      linear_combination (r * τ.re + s) * him - (r * τ.im) * hre
    have hpos : 0 < p * s - q * r := by
      have h1 := τ.im_pos
      have h2 := τ'.im_pos
      have h3 : (0 : ℝ) ≤ τ'.im * ((r * τ.re + s) ^ 2 + (r * τ.im) ^ 2) := by positivity
      have h4 : (0 : ℝ) < ((p * s - q * r : ℤ) : ℝ) := by
        rcases (Int.eq_one_or_neg_one_of_mul_eq_one (by linear_combination hdet :
          (p * s - q * r) * (y * u - x * v) = 1)) with h | h
        · rw [h]; norm_num
        · exfalso
          have h5 : ((p * s - q * r : ℤ) : ℝ) = -1 := by exact_mod_cast h
          push_cast at h5
          rw [h5] at key
          nlinarith
      exact_mod_cast h4
    have hdet1 : p * s - q * r = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one (by linear_combination hdet :
          (p * s - q * r) * (y * u - x * v) = 1) with h | h
      · exact h
      · omega
    let γ : SL(2, ℤ) := ⟨!![p, q; r, s], by rw [Matrix.det_fin_two_of]; exact hdet1⟩
    have hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![p, q; r, s] := rfl
    refine ⟨γ, ?_⟩
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [hγ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, algebraMap_int_eq,
      eq_intCast, ofReal_intCast]
    have hden : (r : ℂ) * τ + s ≠ 0 := by
      intro h0
      have h1 : l * ((r : ℂ) * τ + s) = 1 := by linear_combination e₁
      rw [h0, mul_zero] at h1
      exact zero_ne_one h1
    rw [eq_div_iff hden, hrel]
  · rintro ⟨γ, rfl⟩
    set p := γ 0 0
    set q := γ 0 1
    set r := γ 1 0
    set s := γ 1 1
    have hdet : p * s - q * r = 1 := by
      have := γ.det_coe
      rw [Matrix.det_fin_two] at this
      exact this
    have hden : (r : ℂ) * τ + s ≠ 0 :=
      BinaryQuadraticForm.int_mul_add_ne_zero hτ0 (by
        by_contra! h
        rw [h.1, h.2] at hdet
        simp at hdet)
    have hcoe : ((γ • τ : ℍ) : ℂ) = ((p : ℂ) * τ + q) / ((r : ℂ) * τ + s) := by
      rw [UpperHalfPlane.coe_specialLinearGroup_apply]
      simp [p, q, r, s]
    refine ⟨((r : ℂ) * τ + s)⁻¹, inv_ne_zero hden, ?_⟩
    ext z
    rw [Set.mem_smul_set]
    constructor
    · intro hz
      obtain ⟨m, n, rfl⟩ := mem_lattice_ofTau.mp hz
      refine ⟨_, mem_lattice_ofTau.mpr ⟨m * s + n * q, m * r + n * p, rfl⟩, ?_⟩
      rw [smul_eq_mul, hcoe]
      field_simp
      push_cast
      ring
    · rintro ⟨_, hy, rfl⟩
      obtain ⟨u, v, rfl⟩ := mem_lattice_ofTau.mp hy
      refine mem_lattice_ofTau.mpr ⟨u * p - v * q, v * s - u * r, ?_⟩
      rw [smul_eq_mul, hcoe]
      have hdet' : (p : ℂ) * s - q * r = 1 := by exact_mod_cast hdet
      field_simp
      push_cast
      linear_combination (-(u : ℂ) - v * τ) * hdet'

end PeriodPair

namespace BinaryQuadraticForm

/-- **Endomorphism ring of the lattice of a quadratic irrationality.** Let $a, b, c \in \mathbb{Z}$
with $\gcd(a, b, c) = 1$ and $D = b^2 - 4ac < 0$, and let $\tau \in \mathbb{C}$ be a root of
$a\tau^2 + b\tau + c = 0$ (so $a \neq 0$ and $\tau \notin \mathbb{R}$). Then the endomorphism ring
$\{\lambda \in \mathbb{C} : \lambda\Lambda \subseteq \Lambda\}$ of the lattice
$\Lambda = \mathbb{Z} + \mathbb{Z}\tau$ is $\mathbb{Z} + \mathbb{Z}\,a\tau$, and $a\tau$ is a root
of $X^2 + bX + ac$, so this order has discriminant
$(a\tau - \overline{a\tau})^2 = b^2 - 4ac = D$.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare, Fall
2025, Lecture 17, proof of Theorem 17.10 (for $\mathfrak{a} = \alpha[1, \tau]$ proper,
$\mathcal{O} = [1, a\tau]$, with the minimal polynomial $ax^2 + bx + c$ of $\tau$ made integral)
and Definition 17.16 (the discriminant $(\tau - \bar\tau)^2$ of an order $[1, \tau]$). -/
theorem endomorphismRing_ofTau {a b c : ℤ} (hprim : Int.gcd (Int.gcd a b : ℤ) c = 1)
    (hD : discrim a b c < 0) {τ : ℂ} (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) :
    ((PeriodPair.ofTau τ (im_ne_zero_of_root hD hτ)).endomorphismRing : Set ℂ) =
        {z | ∃ m n : ℤ, z = m + n * (a * τ)} ∧
      ((a : ℂ) * τ) ^ 2 + b * ((a : ℂ) * τ) + (a * c : ℤ) = 0 ∧
      ((a : ℂ) * τ - conj ((a : ℂ) * τ)) ^ 2 = (discrim a b c : ℤ) := by
  have hτ0 := im_ne_zero_of_root hD hτ
  refine ⟨?_, ?_, ?_⟩
  · ext z
    simp only [SetLike.mem_coe, PeriodPair.mem_endomorphismRing, PeriodPair.mem_lattice_ofTau,
      Set.mem_ofPred_eq]
    constructor
    · intro hz
      obtain ⟨m, n, hmn⟩ := hz 1 ⟨1, 0, by simp⟩
      rw [mul_one] at hmn
      obtain ⟨u, v, huv⟩ := hz τ ⟨0, 1, by simp⟩
      -- `(a m - n b - a v) τ = a u + n c`
      have k : ((a * m - n * b - a * v : ℤ) : ℂ) * τ + ((-(a * u) - n * c : ℤ) : ℂ) = 0 := by
        push_cast
        rw [hmn] at huv
        linear_combination (a : ℂ) * huv - n * hτ
      obtain ⟨k₁, k₂⟩ := int_eq_zero_of_mul_add_eq_zero hτ0 k
      have hdvd : a ∣ n := dvd_of_dvd_mul_of_primitive hprim (dvd_mul_left a n)
        ⟨m - v, by linear_combination -k₁⟩ ⟨-u, by linear_combination -k₂⟩
      obtain ⟨t, rfl⟩ := hdvd
      exact ⟨m, t, by rw [hmn]; push_cast; ring⟩
    · rintro ⟨m, n, rfl⟩ w ⟨u, v, rfl⟩
      refine ⟨m * u - n * v * c, m * v + n * a * u - n * v * b, ?_⟩
      push_cast
      linear_combination (n : ℂ) * v * hτ
  · push_cast
    linear_combination (a : ℂ) * hτ
  · have h := mul_root_add_conj hτ0 hτ
    have h2 := two_mul_root_add_sq hτ
    simp only [map_mul, map_intCast]
    linear_combination h2 - (3 * (a : ℂ) * τ - a * conj τ + b) * h

/-- **Substitution of a matrix into a binary quadratic form.** For an integer triple $(a, b, c)$,
standing for $f(x, y) = ax^2 + bxy + cy^2$, and
$\gamma = \begin{pmatrix} p & q \\ r & s \end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$, the triple of
coefficients of the substituted form $(f \cdot \gamma)(x, y) = f(px + qy, rx + sy)$, namely
$(ap^2 + bpr + cr^2,\ 2apq + b(ps + qr) + 2crs,\ aq^2 + bqs + cs^2)$.

Source: David Cox, John McKay and Peter Stevenhagen, *Principal moduli and class fields*, Bull.
London Math. Soc. 36 (2004), 3–12, §2, which works with the $\mathrm{SL}_2(\mathbb{Z})$-orbits of
forms; the substitution is written out here. -/
def substitute (f : ℤ × ℤ × ℤ) (γ : SL(2, ℤ)) : ℤ × ℤ × ℤ :=
  (f.1 * γ 0 0 ^ 2 + f.2.1 * γ 0 0 * γ 1 0 + f.2.2 * γ 1 0 ^ 2,
    2 * f.1 * γ 0 0 * γ 0 1 + f.2.1 * (γ 0 0 * γ 1 1 + γ 0 1 * γ 1 0) + 2 * f.2.2 * γ 1 0 * γ 1 1,
    f.1 * γ 0 1 ^ 2 + f.2.1 * γ 0 1 * γ 1 1 + f.2.2 * γ 1 1 ^ 2)

/-- The substituted form takes the value `f(px + qy, rx + sy)` at `(x, y)`, in any commutative
ring. -/
theorem substitute_eval {R : Type*} [CommRing R] (f : ℤ × ℤ × ℤ) (γ : SL(2, ℤ)) (x y : R) :
    ((substitute f γ).1 : R) * x ^ 2 + (substitute f γ).2.1 * x * y + (substitute f γ).2.2 * y ^ 2 =
      f.1 * (γ 0 0 * x + γ 0 1 * y) ^ 2 +
        f.2.1 * (γ 0 0 * x + γ 0 1 * y) * (γ 1 0 * x + γ 1 1 * y) +
        f.2.2 * (γ 1 0 * x + γ 1 1 * y) ^ 2 := by
  simp only [substitute]
  push_cast
  ring

@[simp] theorem substitute_one (f : ℤ × ℤ × ℤ) : substitute f 1 = f := by
  obtain ⟨a, b, c⟩ := f
  simp [substitute]

theorem substitute_mul (f : ℤ × ℤ × ℤ) (γ δ : SL(2, ℤ)) :
    substitute (substitute f γ) δ = substitute f (γ * δ) := by
  simp only [substitute, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

/-- Substitution by `γ ∈ SL₂(ℤ)` preserves the discriminant `b² - 4ac`. -/
theorem discrim_substitute (f : ℤ × ℤ × ℤ) (γ : SL(2, ℤ)) :
    discrim (substitute f γ).1 (substitute f γ).2.1 (substitute f γ).2.2 =
      discrim f.1 f.2.1 f.2.2 := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rwa [Matrix.det_fin_two] at this
  simp only [substitute, discrim]
  linear_combination (f.2.1 ^ 2 - 4 * f.1 * f.2.2) *
    (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 + 1) * hdet

/-- Substitution by `γ ∈ SL₂(ℤ)` preserves primitivity, `gcd(a, b, c) = 1`. -/
theorem gcd_substitute {f : ℤ × ℤ × ℤ} (hf : Int.gcd (Int.gcd f.1 f.2.1 : ℤ) f.2.2 = 1)
    (γ : SL(2, ℤ)) :
    Int.gcd (Int.gcd (substitute f γ).1 (substitute f γ).2.1 : ℤ) (substitute f γ).2.2 = 1 := by
  set g := substitute f γ
  have hback : substitute g γ⁻¹ = f := by simp [g, substitute_mul]
  set d : ℕ := Int.gcd (Int.gcd g.1 g.2.1 : ℤ) g.2.2 with hd
  have h3 : (d : ℤ) ∣ g.2.2 := Int.gcd_dvd_right _ _
  have h12 : (d : ℤ) ∣ (Int.gcd g.1 g.2.1 : ℤ) := Int.gcd_dvd_left _ _
  have h1 : (d : ℤ) ∣ g.1 := h12.trans (Int.gcd_dvd_left _ _)
  have h2 : (d : ℤ) ∣ g.2.1 := h12.trans (Int.gcd_dvd_right _ _)
  have hcoef : (d : ℤ) ∣ (substitute g γ⁻¹).1 ∧ (d : ℤ) ∣ (substitute g γ⁻¹).2.1 ∧
      (d : ℤ) ∣ (substitute g γ⁻¹).2.2 := by
    simp only [substitute]
    exact ⟨dvd_add (dvd_add (h1.mul_right _) ((h2.mul_right _).mul_right _)) (h3.mul_right _),
      dvd_add (dvd_add (((h1.mul_left 2).mul_right _).mul_right _) (h2.mul_right _))
        (((h3.mul_left 2).mul_right _).mul_right _),
      dvd_add (dvd_add (h1.mul_right _) ((h2.mul_right _).mul_right _)) (h3.mul_right _)⟩
  rw [hback] at hcoef
  have k1 : d ∣ Int.gcd f.1 f.2.1 := Int.dvd_gcd hcoef.1 hcoef.2.1
  have k2 : d ∣ Int.gcd (Int.gcd f.1 f.2.1 : ℤ) f.2.2 :=
    Int.dvd_gcd (Int.natCast_dvd_natCast.mpr k1) hcoef.2.2
  rw [hf] at k2
  exact Nat.dvd_one.mp k2

/-- The leading coefficient `f(p, r)` of a substituted positive definite form is positive. -/
theorem substitute_fst_pos {f : ℤ × ℤ × ℤ} (ha : 0 < f.1) (hD : discrim f.1 f.2.1 f.2.2 < 0)
    (γ : SL(2, ℤ)) : 0 < (substitute f γ).1 := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rwa [Matrix.det_fin_two] at this
  simp only [substitute]
  set p := γ 0 0
  set r := γ 1 0
  have e : 4 * f.1 * (f.1 * p ^ 2 + f.2.1 * p * r + f.2.2 * r ^ 2) =
      (2 * f.1 * p + f.2.1 * r) ^ 2 + (-discrim f.1 f.2.1 f.2.2) * r ^ 2 := by
    simp only [discrim]; ring
  have hpos : 0 < 4 * f.1 * (f.1 * p ^ 2 + f.2.1 * p * r + f.2.2 * r ^ 2) := by
    rw [e]
    rcases eq_or_ne r 0 with hr | hr
    · have hp : p ≠ 0 := by
        rintro hp
        rw [hp, hr] at hdet
        simp at hdet
      rw [hr]
      have h0 : 2 * f.1 * p ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero ha.ne') hp
      have : 0 < (2 * f.1 * p) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0))
      simpa using this
    · have : 0 < r ^ 2 := by positivity
      nlinarith [sq_nonneg (2 * f.1 * p + f.2.1 * r)]
  have h4 : 0 < 4 * f.1 := by omega
  exact pos_of_mul_pos_right hpos h4.le

/-- **Proper equivalence of binary quadratic forms.** Two integer triples $f$ and $g$, standing for
binary quadratic forms, are properly equivalent if $g = f \cdot \gamma$, that is
$g(x, y) = f(px + qy, rx + sy)$, for some
$\gamma = \begin{pmatrix} p & q \\ r & s \end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$; the proper
equivalence classes are the $\mathrm{SL}_2(\mathbb{Z})$-orbits of forms.

Source: David Cox, John McKay and Peter Stevenhagen, *Principal moduli and class fields*, Bull.
London Math. Soc. 36 (2004), 3–12, §2, which works with the $\mathrm{SL}_2(\mathbb{Z})$-orbits of
primitive positive definite binary quadratic forms. -/
def ProperlyEquivalent (f g : ℤ × ℤ × ℤ) : Prop :=
  ∃ γ : SL(2, ℤ), g = substitute f γ

theorem ProperlyEquivalent.refl (f : ℤ × ℤ × ℤ) : ProperlyEquivalent f f :=
  ⟨1, (substitute_one f).symm⟩

theorem ProperlyEquivalent.symm {f g : ℤ × ℤ × ℤ} (h : ProperlyEquivalent f g) :
    ProperlyEquivalent g f := by
  obtain ⟨γ, rfl⟩ := h
  exact ⟨γ⁻¹, by simp [substitute_mul]⟩

theorem ProperlyEquivalent.trans {f g h : ℤ × ℤ × ℤ} (h₁ : ProperlyEquivalent f g)
    (h₂ : ProperlyEquivalent g h) : ProperlyEquivalent f h := by
  obtain ⟨γ, rfl⟩ := h₁
  obtain ⟨δ, rfl⟩ := h₂
  exact ⟨γ * δ, substitute_mul f γ δ⟩

theorem properlyEquivalent_equivalence : Equivalence ProperlyEquivalent :=
  ⟨ProperlyEquivalent.refl, ProperlyEquivalent.symm, ProperlyEquivalent.trans⟩

theorem ProperlyEquivalent.discrim_eq {f g : ℤ × ℤ × ℤ} (h : ProperlyEquivalent f g) :
    discrim g.1 g.2.1 g.2.2 = discrim f.1 f.2.1 f.2.2 := by
  obtain ⟨γ, rfl⟩ := h
  exact discrim_substitute f γ

/-- **A substitution in $\mathrm{SL}_2(\mathbb{Z})$ moves the root of a form.** Let
$f(x, y) = ax^2 + bxy + cy^2$ with $a, b, c \in \mathbb{Z}$, $a > 0$, $\gcd(a, b, c) = 1$ and
$D = b^2 - 4ac < 0$, let $\tau_f \in \mathbb{H}$ be a root of $f(\tau, 1) = 0$ in the upper
half-plane, and for
$\gamma = \begin{pmatrix} p & q \\ r & s \end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$ let
$g(x, y) = f(px + qy, rx + sy)$. Then $g$ is primitive, has discriminant $D$ and leading
coefficient $f(p, r) > 0$, and $\gamma^{-1}\tau_f \in \mathbb{H}$ is a root of $g(\tau, 1) = 0$.

Source: David Cox, John McKay and Peter Stevenhagen, *Principal moduli and class fields*, Bull.
London Math. Soc. 36 (2004), 3–12, §2; the computation
$f(p\tau' + q, r\tau' + s) = (r\tau' + s)^2 f(\gamma\tau', 1)$ is written out here. -/
theorem substitute_root {f : ℤ × ℤ × ℤ} (hprim : Int.gcd (Int.gcd f.1 f.2.1 : ℤ) f.2.2 = 1)
    (ha : 0 < f.1) (hD : discrim f.1 f.2.1 f.2.2 < 0) {τ : ℍ}
    (hτ : (f.1 : ℂ) * (τ : ℂ) ^ 2 + f.2.1 * τ + f.2.2 = 0) (γ : SL(2, ℤ)) :
    Int.gcd (Int.gcd (substitute f γ).1 (substitute f γ).2.1 : ℤ) (substitute f γ).2.2 = 1 ∧
      discrim (substitute f γ).1 (substitute f γ).2.1 (substitute f γ).2.2 =
        discrim f.1 f.2.1 f.2.2 ∧
      (substitute f γ).1 = f.1 * γ 0 0 ^ 2 + f.2.1 * γ 0 0 * γ 1 0 + f.2.2 * γ 1 0 ^ 2 ∧
      0 < (substitute f γ).1 ∧
      ((substitute f γ).1 : ℂ) * ((γ⁻¹ • τ : ℍ) : ℂ) ^ 2 +
        (substitute f γ).2.1 * ((γ⁻¹ • τ : ℍ) : ℂ) + (substitute f γ).2.2 = 0 := by
  refine ⟨gcd_substitute hprim γ, discrim_substitute f γ, rfl, substitute_fst_pos ha hD γ, ?_⟩
  set τ' : ℍ := γ⁻¹ • τ
  have hγ : γ • τ' = τ := smul_inv_smul γ τ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rwa [Matrix.det_fin_two] at this
  have hden : ((γ 1 0 : ℤ) : ℂ) * τ' + (γ 1 1 : ℤ) ≠ 0 :=
    int_mul_add_ne_zero τ'.im_pos.ne' (by
      by_contra! h
      rw [h.1, h.2] at hdet
      simp at hdet)
  have hcoe : (τ : ℂ) =
      (((γ 0 0 : ℤ) : ℂ) * τ' + (γ 0 1 : ℤ)) / (((γ 1 0 : ℤ) : ℂ) * τ' + (γ 1 1 : ℤ)) := by
    rw [← hγ, UpperHalfPlane.coe_specialLinearGroup_apply]
    simp
  have hnum : ((γ 0 0 : ℤ) : ℂ) * τ' + (γ 0 1 : ℤ) =
      (τ : ℂ) * (((γ 1 0 : ℤ) : ℂ) * τ' + (γ 1 1 : ℤ)) := by
    rw [hcoe, div_mul_cancel₀ _ hden]
  have e := substitute_eval (R := ℂ) f γ (τ' : ℂ) 1
  simp only [one_pow, mul_one] at e
  rw [e, hnum]
  linear_combination (((γ 1 0 : ℤ) : ℂ) * τ' + (γ 1 1 : ℤ)) ^ 2 * hτ

/-- **A primitive form with positive leading coefficient is determined by its root.** Let
$f = (a, b, c)$ and $g = (a', b', c')$ be integer triples with
$\gcd(a, b, c) = \gcd(a', b', c') = 1$,
$a > 0$ and $a' > 0$. If some $\tau$ in the upper half-plane is a root of both
$a\tau^2 + b\tau + c$ and $a'\tau^2 + b'\tau + c'$, then $f = g$.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare, Fall
2025, Lecture 17, proof of Theorem 17.10 (by Gauss's lemma, the integer polynomials vanishing at
$\tau$ are the multiples of the primitive $ax^2 + bx + c$). -/
theorem eq_of_root {f g : ℤ × ℤ × ℤ} (hf : Int.gcd (Int.gcd f.1 f.2.1 : ℤ) f.2.2 = 1)
    (hg : Int.gcd (Int.gcd g.1 g.2.1 : ℤ) g.2.2 = 1) (hfa : 0 < f.1) (hga : 0 < g.1) {τ : ℍ}
    (hτf : (f.1 : ℂ) * (τ : ℂ) ^ 2 + f.2.1 * τ + f.2.2 = 0)
    (hτg : (g.1 : ℂ) * (τ : ℂ) ^ 2 + g.2.1 * τ + g.2.2 = 0) : f = g := by
  obtain ⟨a, b, c⟩ := f
  obtain ⟨a', b', c'⟩ := g
  simp only at hf hg hfa hga hτf hτg ⊢
  have k : ((a' * b - a * b' : ℤ) : ℂ) * τ + ((a' * c - a * c' : ℤ) : ℂ) = 0 := by
    push_cast
    linear_combination (a' : ℂ) * hτf - a * hτg
  obtain ⟨k₁, k₂⟩ := int_eq_zero_of_mul_add_eq_zero τ.im_pos.ne' k
  have h1 : a ∣ a' := dvd_of_dvd_mul_of_primitive hf (dvd_mul_left a a')
    ⟨b', by linear_combination k₁⟩ ⟨c', by linear_combination k₂⟩
  have h2 : a' ∣ a := dvd_of_dvd_mul_of_primitive hg (dvd_mul_left a' a)
    ⟨b, by linear_combination -k₁⟩ ⟨c, by linear_combination -k₂⟩
  have haa : a = a' := Int.dvd_antisymm hfa.le hga.le h1 h2
  subst haa
  have hb : b = b' := by
    have : a * (b - b') = 0 := by linear_combination k₁
    rcases mul_eq_zero.mp this with h | h
    · omega
    · omega
  have hc : c = c' := by
    have : a * (c - c') = 0 := by linear_combination k₂
    rcases mul_eq_zero.mp this with h | h
    · omega
    · omega
  rw [hb, hc]

/-- **Proper equivalence and the orbits of roots.** Let $f$ and $g$ be primitive integral binary
quadratic forms with positive leading coefficients, with roots $\tau_f$ and $\tau_g$ in the upper
half-plane, and suppose $f$ has negative discriminant. Then $g(x, y) = f(px + qy, rx + sy)$ for
some $\begin{pmatrix} p & q \\ r & s \end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$ if and only if
$\tau_g$ lies in the $\mathrm{SL}_2(\mathbb{Z})$-orbit of $\tau_f$.

Source: David Cox, John McKay and Peter Stevenhagen, *Principal moduli and class fields*, Bull.
London Math. Soc. 36 (2004), 3–12, §2; the deduction from `substitute_root` and `eq_of_root` is
written out here. -/
theorem properlyEquivalent_iff_exists_smul {f g : ℤ × ℤ × ℤ}
    (hf : Int.gcd (Int.gcd f.1 f.2.1 : ℤ) f.2.2 = 1)
    (hg : Int.gcd (Int.gcd g.1 g.2.1 : ℤ) g.2.2 = 1)
    (hfa : 0 < f.1) (hga : 0 < g.1) (hD : discrim f.1 f.2.1 f.2.2 < 0) {τf τg : ℍ}
    (hτf : (f.1 : ℂ) * (τf : ℂ) ^ 2 + f.2.1 * τf + f.2.2 = 0)
    (hτg : (g.1 : ℂ) * (τg : ℂ) ^ 2 + g.2.1 * τg + g.2.2 = 0) :
    ProperlyEquivalent f g ↔ ∃ γ : SL(2, ℤ), τg = γ • τf := by
  constructor
  · rintro ⟨γ, rfl⟩
    obtain ⟨-, -, -, -, h⟩ := substitute_root hf hfa hD hτf γ
    exact ⟨γ⁻¹, root_unique hga.ne' hτg h⟩
  · rintro ⟨γ, rfl⟩
    obtain ⟨h₁, -, -, h₄, h₅⟩ := substitute_root hf hfa hD hτf γ⁻¹
    rw [inv_inv] at h₅
    exact ⟨γ⁻¹, (eq_of_root h₁ hg h₄ hga h₅ hτg).symm⟩

/-- **Reduced forms and the fundamental domain.** Let $a, b, c \in \mathbb{Z}$ with $a > 0$ and
$D = b^2 - 4ac < 0$, and let $\tau$ be the root of $a\tau^2 + b\tau + c = 0$ in the upper
half-plane. Then $\tau$ lies in the fundamental domain
$F = \{\tau \in \mathbb{H} : \mathrm{re}(\tau) \in [-1/2, 1/2),\ |\tau| \ge 1,\ |\tau| > 1
\text{ if } \mathrm{re}(\tau) > 0\}$ if and only if the form $ax^2 + bxy + cy^2$ is Gauss reduced:
$|b| \le a \le c$, with $b \ge 0$ whenever $|b| = a$ or $a = c$.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare, Fall
2025, Lecture 15, the set $F$ defined before Lemma 15.10. The computation
$\mathrm{re}(\tau) = -b/(2a)$, $|\tau|^2 = c/a$ is written out here. -/
theorem isGaussReduced_iff_root_mem {a b c : ℤ} (ha : 0 < a) (hD : discrim a b c < 0) {τ : ℍ}
    (hτ : (a : ℂ) * (τ : ℂ) ^ 2 + b * τ + c = 0) :
    IsGaussReduced a b c ↔
      τ.re ∈ Set.Ico (-(1 / 2) : ℝ) (1 / 2) ∧ 1 ≤ ‖(τ : ℂ)‖ ∧ (0 < τ.re → 1 < ‖(τ : ℂ)‖) := by
  have hτ0 : (τ : ℂ).im ≠ 0 := τ.im_pos.ne'
  have hre := two_mul_mul_re_root hτ0 hτ
  have hns := mul_normSq_root hτ0 hτ
  simp only [UpperHalfPlane.coe_re] at hre
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hn : normSq (τ : ℂ) = ‖(τ : ℂ)‖ ^ 2 := Complex.normSq_eq_norm_sq _
  have e1 : -(1 / 2 : ℝ) ≤ τ.re ↔ b ≤ a := by
    constructor
    · intro h
      have : (b : ℝ) ≤ a := by nlinarith
      exact_mod_cast this
    · intro h
      have : (b : ℝ) ≤ a := by exact_mod_cast h
      nlinarith
  have e2 : τ.re < 1 / 2 ↔ -a < b := by
    constructor
    · intro h
      have : -(a : ℝ) < b := by nlinarith
      exact_mod_cast this
    · intro h
      have : -(a : ℝ) < b := by exact_mod_cast h
      nlinarith
  have e3 : 0 < τ.re ↔ b < 0 := by
    constructor
    · intro h
      have : (b : ℝ) < 0 := by nlinarith
      exact_mod_cast this
    · intro h
      have : (b : ℝ) < 0 := by exact_mod_cast h
      nlinarith
  have e4 : 1 ≤ ‖(τ : ℂ)‖ ↔ a ≤ c := by
    rw [← one_le_sq_iff₀ (norm_nonneg _), ← hn]
    constructor
    · intro h
      have : (a : ℝ) ≤ c := by nlinarith
      exact_mod_cast this
    · intro h
      have : (a : ℝ) ≤ c := by exact_mod_cast h
      nlinarith
  have e5 : 1 < ‖(τ : ℂ)‖ ↔ a < c := by
    rw [← one_lt_sq_iff₀ (norm_nonneg _), ← hn]
    constructor
    · intro h
      have : (a : ℝ) < c := by nlinarith
      exact_mod_cast this
    · intro h
      have : (a : ℝ) < c := by exact_mod_cast h
      nlinarith
  rw [Set.mem_Ico, e1, e2, e3, e4, e5, IsGaussReduced_iff]
  constructor
  · rintro ⟨-, -, h1, h2, h3⟩
    rw [abs_le] at h1
    refine ⟨⟨h1.2, ?_⟩, h2, fun hb ↦ ?_⟩
    · by_contra h
      have : |b| = a := by rw [abs_of_neg (by omega)]; omega
      have := h3 (Or.inl this)
      omega
    · by_contra h
      have := h3 (Or.inr (by omega))
      omega
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨ha, hD, abs_le.mpr ⟨by omega, h1⟩, h3, ?_⟩
    rintro (h | h)
    · rcases abs_cases b with ⟨hb, -⟩ | ⟨hb, -⟩ <;> omega
    · by_contra hb
      have := h4 (by omega)
      omega

/-- **Roots in Mathlib's closed fundamental domain.** Let $a, b, c \in \mathbb{Z}$ with $a > 0$,
and let $\tau$ be a root of $a\tau^2 + b\tau + c = 0$ in the upper half-plane.
Then $\tau$ lies in the closed fundamental domain `ModularGroup.fd`,
$\{\tau \in \mathbb{H} : |\tau|^2 \ge 1,\ |\mathrm{re}(\tau)| \le 1/2\}$, if and only if
$|b| \le a \le c$.

The computation $\mathrm{re}(\tau) = -b/(2a)$, $|\tau|^2 = c/a$ is written out here; compare the
half-open domain $F$ of Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT
OpenCourseWare, Fall 2025, Lecture 15, before Lemma 15.10. -/
theorem root_mem_fd_iff {a b c : ℤ} (ha : 0 < a) {τ : ℍ}
    (hτ : (a : ℂ) * (τ : ℂ) ^ 2 + b * τ + c = 0) :
    τ ∈ ModularGroup.fd ↔ |b| ≤ a ∧ a ≤ c := by
  have hτ0 : (τ : ℂ).im ≠ 0 := τ.im_pos.ne'
  have hre := two_mul_mul_re_root hτ0 hτ
  have hns := mul_normSq_root hτ0 hτ
  simp only [UpperHalfPlane.coe_re] at hre
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  change 1 ≤ normSq (τ : ℂ) ∧ |τ.re| ≤ 1 / 2 ↔ _
  have e1 : |τ.re| ≤ 1 / 2 ↔ |b| ≤ a := by
    rw [abs_le, abs_le]
    constructor
    · rintro ⟨h1, h2⟩
      have : -(a : ℝ) ≤ b ∧ (b : ℝ) ≤ a := ⟨by nlinarith, by nlinarith⟩
      exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
    · rintro ⟨h1, h2⟩
      have h1' : -(a : ℝ) ≤ b := by exact_mod_cast h1
      have h2' : (b : ℝ) ≤ a := by exact_mod_cast h2
      exact ⟨by nlinarith, by nlinarith⟩
  have e2 : 1 ≤ normSq (τ : ℂ) ↔ a ≤ c := by
    constructor
    · intro h
      have : (a : ℝ) ≤ c := by nlinarith
      exact_mod_cast this
    · intro h
      have : (a : ℝ) ≤ c := by exact_mod_cast h
      nlinarith
  rw [e1, e2, and_comm]

end BinaryQuadraticForm
