/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticForms.RootLattice
public import MathlibExt.NumberTheory.ImaginaryQuadraticDiscriminant
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The order of a given discriminant

An order $\mathbb{Z} + \mathbb{Z}\omega$ in an imaginary quadratic field, with
$\omega \in \mathbb{C}$ not real, has discriminant $(\omega - \bar\omega)^2$. We show that this
number does not depend on the basis, and that for an imaginary quadratic discriminant $D$ there is
exactly one such order of discriminant $D$, namely $\mathbb{Z} + \mathbb{Z}\,\frac{D + \sqrt{D}}{2}$
with $\sqrt{D} = i\sqrt{|D|}$:

* `PeriodPair.lattice_ofTau_eq_iff`:
  $\mathbb{Z} + \mathbb{Z}\omega = \mathbb{Z} + \mathbb{Z}\omega'$ exactly when
  $\omega' = \pm\omega + k$ for an integer $k$;
* `PeriodPair.sq_sub_conj_eq_of_lattice_ofTau_eq`: equal lattices give equal discriminants;
* `PeriodPair.order_of_discriminant`: the order of a given discriminant exists and is unique.

The source is Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare,
Fall 2025, Lecture 17, Definitions 17.16 and 17.17, Theorem 17.18 and Lemma 17.19.
-/

@[expose] public section

open Complex

open scoped ComplexConjugate

namespace PeriodPair

/-- **A lattice $\mathbb{Z} + \mathbb{Z}\omega$ determines $\omega$ up to sign and translation.**
For non-real complex numbers $\omega$ and $\omega'$, the lattices $\mathbb{Z} + \mathbb{Z}\omega$
and $\mathbb{Z} + \mathbb{Z}\omega'$ are equal if and only if $\omega' = \omega + k$ or
$\omega' = -\omega + k$ for some integer $k$. -/
theorem lattice_ofTau_eq_iff {ω ω' : ℂ} (hω : ω.im ≠ 0) (hω' : ω'.im ≠ 0) :
    ((ofTau ω hω).lattice : Set ℂ) = (ofTau ω' hω').lattice ↔
      ∃ k : ℤ, ω' = ω + k ∨ ω' = -ω + k := by
  constructor
  · intro h
    have h1 : ω' ∈ ((ofTau ω hω).lattice : Set ℂ) := by
      rw [h]; exact mem_lattice_ofTau.mpr ⟨0, 1, by simp⟩
    have h2 : ω ∈ ((ofTau ω' hω').lattice : Set ℂ) := by
      rw [← h]; exact mem_lattice_ofTau.mpr ⟨0, 1, by simp⟩
    obtain ⟨m, n, hmn⟩ := mem_lattice_ofTau.mp h1
    obtain ⟨m', n', hmn'⟩ := mem_lattice_ofTau.mp h2
    -- `ω = m' + n' (m + n ω)`, so `(1 - n' n) ω = m' + n' m`
    have k : (((1 - n' * n : ℤ) : ℂ)) * ω + ((-(m' + n' * m) : ℤ) : ℂ) = 0 := by
      push_cast
      linear_combination hmn' + (n' : ℂ) * hmn
    obtain ⟨k₁, -⟩ := BinaryQuadraticForm.int_eq_zero_of_mul_add_eq_zero hω k
    have hn : n = 1 ∨ n = -1 := by
      have : n' * n = 1 := by omega
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' this with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    refine ⟨m, ?_⟩
    rcases hn with rfl | rfl
    · left; rw [hmn]; push_cast; ring
    · right; rw [hmn]; push_cast; ring
  · rintro ⟨k, hk | hk⟩
    · ext z
      simp only [SetLike.mem_coe, mem_lattice_ofTau]
      constructor
      · rintro ⟨m, n, rfl⟩
        exact ⟨m - n * k, n, by rw [hk]; push_cast; ring⟩
      · rintro ⟨m, n, rfl⟩
        exact ⟨m + n * k, n, by rw [hk]; push_cast; ring⟩
    · ext z
      simp only [SetLike.mem_coe, mem_lattice_ofTau]
      constructor
      · rintro ⟨m, n, rfl⟩
        exact ⟨m + n * k, -n, by rw [hk]; push_cast; ring⟩
      · rintro ⟨m, n, rfl⟩
        exact ⟨m + n * k, -n, by rw [hk]; push_cast; ring⟩

/-- **The discriminant of an order does not depend on the basis.** For non-real complex numbers
$\omega$ and $\omega'$ with $\mathbb{Z} + \mathbb{Z}\omega = \mathbb{Z} + \mathbb{Z}\omega'$, the
discriminants agree: $(\omega - \bar\omega)^2 = (\omega' - \bar\omega')^2$. -/
theorem sq_sub_conj_eq_of_lattice_ofTau_eq {ω ω' : ℂ} (hω : ω.im ≠ 0) (hω' : ω'.im ≠ 0)
    (h : ((ofTau ω hω).lattice : Set ℂ) = (ofTau ω' hω').lattice) :
    (ω - conj ω) ^ 2 = (ω' - conj ω') ^ 2 := by
  obtain ⟨k, hk | hk⟩ := (lattice_ofTau_eq_iff hω hω').mp h <;>
  · rw [hk]; simp only [map_add, map_neg, map_intCast]; ring

/-- **The discriminant of an order is a negative integer.** For a non-real $\omega \in \mathbb{C}$
with $\omega^2 \in \mathbb{Z} + \mathbb{Z}\omega$, the discriminant $(\omega - \bar\omega)^2$ of the
order $\mathbb{Z} + \mathbb{Z}\omega$ is a negative integer $D$: writing $\omega^2 = m + n\omega$,
$D = n^2 + 4m$. -/
theorem exists_sq_sub_conj_eq_intCast {ω : ℂ} (hω : ω.im ≠ 0)
    (hmul : ω * ω ∈ (ofTau ω hω).lattice) : ∃ D : ℤ, D < 0 ∧ (ω - conj ω) ^ 2 = D := by
  obtain ⟨m, n, hmn⟩ := mem_lattice_ofTau.mp hmul
  have hc : conj ω * conj ω = m + n * conj ω := by
    have := congrArg conj hmn
    simpa using this
  have hne : ω - conj ω ≠ 0 := by
    intro h0
    apply hω
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hsum : ω + conj ω = n := by
    have hsub : (ω - conj ω) * (ω + conj ω - n) = 0 := by linear_combination hmn - hc
    linear_combination (mul_eq_zero.mp hsub).resolve_left hne
  refine ⟨n ^ 2 + 4 * m, ?_, ?_⟩
  · have h1 : ω - conj ω = I * (2 * ω.im : ℝ) := by
      apply Complex.ext <;> simp; ring
    have h2 : (ω - conj ω) ^ 2 = ((n ^ 2 + 4 * m : ℤ) : ℂ) := by
      push_cast
      linear_combination (ω + conj ω + n - 4 * ω) * hsum + 4 * hmn
    rw [h1, mul_pow, I_sq, ← ofReal_pow] at h2
    have h3 : ((-(2 * ω.im) ^ 2 : ℝ) : ℂ) = (((n ^ 2 + 4 * m : ℤ) : ℝ) : ℂ) := by
      push_cast at h2 ⊢; linear_combination h2
    have h4 : (-(2 * ω.im) ^ 2 : ℝ) = ((n ^ 2 + 4 * m : ℤ) : ℝ) := by exact_mod_cast h3
    have h5 : ((n ^ 2 + 4 * m : ℤ) : ℝ) < 0 := by
      rw [← h4]; nlinarith [sq_pos_of_ne_zero (mul_ne_zero two_ne_zero hω)]
    exact_mod_cast h5
  · push_cast
    linear_combination (ω + conj ω + n - 4 * ω) * hsum + 4 * hmn

/-- The square of `i √|D|` is `D` for `D ≤ 0`. -/
private theorem I_mul_sqrt_sq {D : ℤ} (hD : D ≤ 0) :
    (I * (Real.sqrt |(D : ℝ)| : ℂ)) ^ 2 = D := by
  rw [mul_pow, I_sq, ← ofReal_pow, Real.sq_sqrt (abs_nonneg _),
    abs_of_nonpos (by exact_mod_cast hD)]
  push_cast
  ring

/-- **The order of a given discriminant.** Let $D$ be an imaginary quadratic discriminant
($D < 0$ and $D \equiv 0, 1 \pmod 4$), let $\sqrt{D} = i\sqrt{|D|}$ and
$\omega_D = \frac{D + \sqrt{D}}{2}$. Then $\omega_D$ is not real, the lattice
$\mathcal{O}_D = \mathbb{Z} + \mathbb{Z}\omega_D$ is closed under multiplication (so it is an order
of $\mathbb{Q}(\sqrt{D})$), and its discriminant is $(\omega_D - \bar\omega_D)^2 = D$. Moreover,
for every non-real $\omega \in \mathbb{C}$ whose lattice $\mathbb{Z} + \mathbb{Z}\omega$ is closed
under multiplication and has discriminant $(\omega - \bar\omega)^2 = D$, the lattice
$\mathbb{Z} + \mathbb{Z}\omega$ equals $\mathcal{O}_D$.

No imaginary quadratic field $K$ is fixed in advance: a non-real $\omega$ whose lattice is a ring
is a quadratic integer, and the uniqueness holds among all of them.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare,
Fall 2025, Lecture 17, Theorem 17.18 and its proof (the order of discriminant $D$, written there
as $[1, u\tau_K]$), with Definitions 17.16 and 17.17 and Lemma 17.19; the computation with
$\omega^2 = m + n\omega$ is written out here. -/
theorem order_of_discriminant {D : ℤ}
    (hD : ImaginaryQuadraticDiscriminant.IsImaginaryQuadraticDiscriminant D) :
    ∃ hωD : ((D + I * (Real.sqrt |(D : ℝ)| : ℂ)) / 2).im ≠ 0,
      (∀ x ∈ (ofTau _ hωD).lattice, ∀ y ∈ (ofTau _ hωD).lattice, x * y ∈ (ofTau _ hωD).lattice) ∧
      ((D + I * (Real.sqrt |(D : ℝ)| : ℂ)) / 2 -
          conj ((D + I * (Real.sqrt |(D : ℝ)| : ℂ)) / 2)) ^ 2 = D ∧
      ∀ (ω : ℂ) (hω : ω.im ≠ 0),
        (∀ x ∈ (ofTau ω hω).lattice, ∀ y ∈ (ofTau ω hω).lattice, x * y ∈ (ofTau ω hω).lattice) →
        (ω - conj ω) ^ 2 = D →
        ((ofTau ω hω).lattice : Set ℂ) = (ofTau _ hωD).lattice := by
  obtain ⟨hneg, hmod⟩ := hD
  set s : ℝ := Real.sqrt |(D : ℝ)| with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast hneg.ne))
  have hs2 : s ^ 2 = -(D : ℝ) := by
    rw [hs, Real.sq_sqrt (abs_nonneg _), abs_of_neg (by exact_mod_cast hneg)]
  set ωD : ℂ := (D + I * (s : ℂ)) / 2 with hωD
  have him : ωD.im = s / 2 := by simp [ωD]
  have hre : ωD.re = D / 2 := by simp [ωD]
  have hωD0 : ωD.im ≠ 0 := by rw [him]; positivity
  -- `ωD ^ 2 = D ωD - (D ^ 2 - D) / 4`, an integer relation as `D ≡ 0, 1 (mod 4)`
  obtain ⟨e, he⟩ : ∃ e : ℤ, D ^ 2 - D = 4 * e := by
    rcases hmod with h | h
    · obtain ⟨q, rfl⟩ : ∃ q, D = 4 * q := ⟨D / 4, by omega⟩
      exact ⟨q * (4 * q - 1), by ring⟩
    · obtain ⟨q, rfl⟩ : ∃ q, D = 4 * q + 1 := ⟨D / 4, by omega⟩
      exact ⟨q * (4 * q + 1), by ring⟩
  have hsq : ωD * ωD = D * ωD - e := by
    have : ((s : ℂ)) ^ 2 = -(D : ℂ) := by exact_mod_cast hs2
    have he' : ((D : ℂ) ^ 2 - D) = 4 * e := by exact_mod_cast he
    have hI : I ^ 2 = -1 := I_sq
    simp only [ωD]
    linear_combination (1 / 4 : ℂ) * I ^ 2 * this - ((D : ℂ) / 4) * hI - (1 / 4 : ℂ) * he'
  refine ⟨hωD0, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨m, n, rfl⟩ := mem_lattice_ofTau.mp hx
    obtain ⟨u, v, rfl⟩ := mem_lattice_ofTau.mp hy
    refine mem_lattice_ofTau.mpr ⟨m * u - n * v * e, m * v + n * u + n * v * D, ?_⟩
    push_cast
    linear_combination (n : ℂ) * v * hsq
  · have hc : conj ωD = (D - I * s) / 2 := by
      simp only [ωD, map_div₀, map_add, map_mul, conj_ofReal, conj_I, map_intCast, map_ofNat]
      ring
    have : ωD - conj ωD = I * s := by rw [hc]; simp only [ωD]; ring
    rw [this, mul_pow, I_sq, ← ofReal_pow, hs2]
    push_cast; ring
  · intro ω hω hmul hdisc
    -- `ω ^ 2 = m + n ω`
    obtain ⟨m, n, hmn⟩ := mem_lattice_ofTau.mp
      (hmul ω (mem_lattice_ofTau.mpr ⟨0, 1, by simp⟩) ω (mem_lattice_ofTau.mpr ⟨0, 1, by simp⟩))
    have hc : conj ω * conj ω = m + n * conj ω := by
      have := congrArg conj hmn
      simpa using this
    -- `ω + ω̄ = n`
    have hsum : ω + conj ω = n := by
      have hsub : (ω - conj ω) * (ω + conj ω - n) = 0 := by linear_combination hmn - hc
      have hne : ω - conj ω ≠ 0 := by
        intro h0
        apply hω
        have := congrArg Complex.im h0
        simp at this
        linarith
      have := (mul_eq_zero.mp hsub).resolve_left hne
      linear_combination this
    have hre2 : 2 * ω.re = n := by
      have := congrArg Complex.re hsum
      simp at this
      linarith
    have him2 : (2 * ω.im) ^ 2 = s ^ 2 := by
      have h1 : ω - conj ω = I * (2 * ω.im : ℝ) := by
        apply Complex.ext <;> simp; ring
      rw [h1, mul_pow, I_sq, ← ofReal_pow] at hdisc
      have : ((2 * ω.im) ^ 2 : ℝ) = -(D : ℝ) := by
        have h' : (((2 * ω.im) ^ 2 : ℝ) : ℂ) = ((-(D : ℝ) : ℝ) : ℂ) := by
          push_cast at hdisc ⊢; linear_combination -hdisc
        exact_mod_cast h'
      rw [this, hs2]
    -- `D ≡ n (mod 2)`, so `(D - n) / 2` and `(D + n) / 2` are integers
    have hDn : ∃ k : ℤ, D = n + 2 * k := by
      have hdisc' : (D : ℂ) = n ^ 2 + 4 * m := by
        rw [← hdisc]
        linear_combination (ω + conj ω + n - 4 * ω) * hsum + 4 * hmn
      have : D = n ^ 2 + 4 * m := by exact_mod_cast hdisc'
      refine ⟨(D - n) / 2, ?_⟩
      have : (D - n) % 2 = 0 := by
        rw [this]
        rcases Int.emod_two_eq_zero_or_one n with h | h <;>
          simp [Int.sub_emod, Int.add_emod, pow_two, Int.mul_emod, h]
      omega
    obtain ⟨k, hk⟩ := hDn
    have h2 : 2 * ω.im = s ∨ 2 * ω.im = -s := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp him2 with h | h
      · exact Or.inl h
      · exact Or.inr h
    rw [lattice_ofTau_eq_iff hω hωD0]
    rcases h2 with h | h
    · refine ⟨k, Or.inl ?_⟩
      apply Complex.ext
      · rw [hre]; simp only [add_re, intCast_re]; push_cast [hk] at hre2 ⊢; linarith
      · rw [him]; simp; linarith
    · refine ⟨n + k, Or.inr ?_⟩
      apply Complex.ext
      · rw [hre]; simp only [Int.cast_add, add_re, neg_re, intCast_re]
        push_cast [hk] at hre2 ⊢; linarith
      · rw [him]; simp; linarith

end PeriodPair
