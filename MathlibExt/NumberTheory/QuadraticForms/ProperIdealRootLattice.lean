/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticForms.OrderDiscriminant
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Proper ideals are homothetic to lattices of roots of forms

Let $\mathcal{O} = \mathbb{Z} + \mathbb{Z}\omega$ be an order of discriminant
$D = (\omega - \bar\omega)^2$ in $\mathbb{C}$. Every lattice whose endomorphism ring is
$\mathcal{O}$ is homothetic to $\mathbb{Z} + \mathbb{Z}\tau$ for a root $\tau$ in the upper
half-plane of a primitive positive definite form of discriminant $D$:

* `PeriodPair.IsHomothetic.endomorphismRing_eq`: homothetic lattices have the same endomorphism
  ring;
* `PeriodPair.exists_isHomothetic_ofTau`: every lattice is homothetic to
  $\mathbb{Z} + \mathbb{Z}\tau$ for some $\tau$ in the upper half-plane;
* `PeriodPair.exists_root_of_isProperIdeal`: the main result.

The source is Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare,
Fall 2025, Lecture 17, proof of Theorem 17.10, Lemma 17.9 and Definition 17.16.
-/

@[expose] public section

open Complex UpperHalfPlane

open scoped ComplexConjugate Pointwise

namespace PeriodPair

/-- **Homothetic lattices have the same endomorphism ring.** If the lattice of a period pair $L'$
is $c\Lambda$ for the lattice $\Lambda$ of $L$ and a nonzero $c \in \mathbb{C}$, then
$\{a \in \mathbb{C} : a\Lambda' \subseteq \Lambda'\} =
\{a \in \mathbb{C} : a\Lambda \subseteq \Lambda\}$.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare,
Fall 2025, Lecture 17, Lemma 17.9 (properness depends only on the homothety class). -/
theorem IsHomothetic.endomorphismRing_eq {L L' : PeriodPair} (h : L.IsHomothetic L') :
    L'.endomorphismRing = L.endomorphismRing := by
  obtain ⟨c, hc, hL⟩ := h
  have key : ∀ a : ℂ, (∀ z ∈ L.lattice, a * z ∈ L.lattice) →
      ∀ z ∈ L'.lattice, a * z ∈ L'.lattice := by
    intro a ha z hz
    rw [← SetLike.mem_coe, hL] at hz ⊢
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨a * w, ha w hw, by simp only [smul_eq_mul]; ring⟩
  have key' : ∀ a : ℂ, (∀ z ∈ L'.lattice, a * z ∈ L'.lattice) →
      ∀ z ∈ L.lattice, a * z ∈ L.lattice := by
    intro a ha z hz
    have hz' : c * z ∈ L'.lattice := by
      rw [← SetLike.mem_coe, hL]; exact ⟨z, hz, rfl⟩
    have := ha _ hz'
    rw [← SetLike.mem_coe, hL] at this
    obtain ⟨w, hw, hw'⟩ := this
    simp only [smul_eq_mul] at hw'
    have : w = a * z := by
      have := mul_left_cancel₀ hc (hw'.trans (by ring : a * (c * z) = c * (a * z)))
      exact this
    exact this ▸ hw
  ext a
  simp only [mem_endomorphismRing]
  exact ⟨key' a, key a⟩

/-- **Every lattice is homothetic to the lattice of a point of the upper half-plane.** For every
period pair $L$ there is $\tau$ in the upper half-plane such that the lattice of $L$ is homothetic
to $\mathbb{Z} + \mathbb{Z}\tau$; one may take $\tau = \pm\omega_2/\omega_1$. -/
theorem exists_isHomothetic_ofTau (L : PeriodPair) :
    ∃ τ : ℍ, (ofTau τ τ.im_pos.ne').IsHomothetic L := by
  have hind := LinearIndependent.pair_iff.mp L.indep
  have h1 : L.ω₁ ≠ 0 := by
    intro h
    have := hind 1 0 (by simp [h])
    simp at this
  set t := L.ω₂ / L.ω₁ with ht
  have hω₂ : L.ω₂ = t * L.ω₁ := by rw [ht]; field_simp
  have htim : t.im ≠ 0 := by
    intro h
    have ht' : t = (t.re : ℂ) := Complex.ext (by simp) (by simp [h])
    have e : (t.re : ℂ) * L.ω₁ = L.ω₂ := by rw [hω₂, ← ht']
    have := hind t.re (-1) (by rw [real_smul, real_smul, ← e]; push_cast; ring)
    simp at this
  have hlat : ((L.lattice : Set ℂ)) = L.ω₁ • ((ofTau t htim).lattice : Set ℂ) := by
    ext z
    simp only [SetLike.mem_coe, Set.mem_smul_set, mem_lattice, smul_eq_mul, ofTau_ω₁, ofTau_ω₂]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m + n * t, ⟨m, n, by ring⟩, by rw [hω₂]; ring⟩
    · rintro ⟨_, ⟨m, n, rfl⟩, rfl⟩
      exact ⟨m, n, by rw [hω₂]; ring⟩
  rcases lt_or_gt_of_ne htim with hneg | hpos
  · have hpos' : 0 < (-t).im := by simpa using hneg
    refine ⟨⟨-t, hpos'⟩, L.ω₁, h1, ?_⟩
    rw [hlat]
    congr 1
    exact (lattice_ofTau_eq_iff (ω' := -t) htim hpos'.ne').mpr ⟨0, Or.inr (by simp)⟩
  · exact ⟨⟨t, hpos⟩, L.ω₁, h1, hlat⟩

/-- A quadratic with integer coefficients, nonzero leading coefficient and a non-real root has
negative discriminant. -/
private theorem discrim_neg_of_root {a b c : ℤ} (ha : a ≠ 0) {τ : ℂ} (hτ0 : τ.im ≠ 0)
    (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) : discrim a b c < 0 := by
  have h := BinaryQuadraticForm.two_mul_root_add_sq hτ
  set z : ℂ := 2 * a * τ + b with hz
  have hzim : z.im ≠ 0 := by
    have e : z.im = 2 * a * τ.im := by simp [hz]
    rw [e]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast ha)) hτ0
  have him : (z ^ 2).im = 0 := by rw [h]; simp
  have hre : z.re = 0 := by
    rw [pow_two, mul_im] at him
    have : 2 * z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · exact absurd h1 hzim
  have : ((discrim a b c : ℤ) : ℝ) = -z.im ^ 2 := by
    have := congrArg Complex.re h
    rw [pow_two, mul_re, hre] at this
    simp only [intCast_re] at this
    linarith
  have : ((discrim a b c : ℤ) : ℝ) < 0 := by rw [this]; nlinarith [sq_pos_of_ne_zero hzim]
  exact_mod_cast this

/-- From a nonzero integer triple vanishing at `τ`, a primitive one with positive first entry. -/
private theorem exists_primitive_root {A B C : ℤ} (hA : A ≠ 0) {τ : ℂ}
    (hτ : (A : ℂ) * τ ^ 2 + B * τ + C = 0) :
    ∃ a b c : ℤ, Int.gcd (Int.gcd a b : ℤ) c = 1 ∧ 0 < a ∧ (a : ℂ) * τ ^ 2 + b * τ + c = 0 := by
  wlog hpos : 0 < A generalizing A B C
  · refine this (A := -A) (B := -B) (C := -C) (neg_ne_zero.mpr hA) ?_ (by omega)
    push_cast
    linear_combination -hτ
  set g : ℕ := Int.gcd (Int.gcd A B : ℤ) C with hg
  have hg0 : 0 < g := Int.gcd_pos_of_ne_zero_left _ (by
    exact_mod_cast (Int.gcd_pos_of_ne_zero_left B hA).ne')
  have hgA : (g : ℤ) ∣ A := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _)
  have hgB : (g : ℤ) ∣ B := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right _ _)
  have hgC : (g : ℤ) ∣ C := Int.gcd_dvd_right _ _
  obtain ⟨a, ha⟩ := hgA
  obtain ⟨b, hb⟩ := hgB
  obtain ⟨c, hc⟩ := hgC
  have hg' : (g : ℤ) ≠ 0 := by exact_mod_cast hg0.ne'
  refine ⟨a, b, c, ?_, ?_, ?_⟩
  · have h1 : Int.gcd ((g : ℤ) * a) ((g : ℤ) * b) = g * Int.gcd a b := by
      rw [Int.gcd_mul_left]; simp
    have h2 : g = g * Int.gcd (Int.gcd a b : ℤ) c := by
      conv_lhs => rw [hg, ha, hb, hc, h1]
      push_cast
      rw [Int.gcd_mul_left]; simp
    have : g * 1 = g * Int.gcd (Int.gcd a b : ℤ) c := by rw [mul_one]; exact h2
    exact (Nat.eq_of_mul_eq_mul_left hg0 this).symm
  · rw [ha] at hpos; exact pos_of_mul_pos_right hpos (by positivity)
  · have : ((g : ℤ) : ℂ) * ((a : ℂ) * τ ^ 2 + b * τ + c) = 0 := by
      rw [ha, hb, hc] at hτ; push_cast at hτ ⊢; linear_combination hτ
    exact (mul_eq_zero.mp this).resolve_left (by exact_mod_cast hg')

/-- **Proper ideals are homothetic to lattices of roots of forms.** Let $\omega \in \mathbb{C}$ be
non-real, and let $\mathcal{O} \subseteq \mathbb{C}$ be a subring whose underlying set is
$\mathbb{Z} + \mathbb{Z}\omega$, an order of discriminant
$D = (\omega - \bar\omega)^2 \in \mathbb{Z}$. Let $\Lambda$ be the lattice of a period pair $L$ that
is a proper ideal of $\mathcal{O}$: its endomorphism ring
$\{a \in \mathbb{C} : a\Lambda \subseteq \Lambda\}$ is $\mathcal{O}$. Then there are integers
$a, b, c$ with $\gcd(a, b, c) = 1$, $a > 0$ and $b^2 - 4ac = D$, and $\tau$ in the upper half-plane
with $a\tau^2 + b\tau + c = 0$, such that $\Lambda$ is homothetic to $\mathbb{Z} + \mathbb{Z}\tau$
and $\mathcal{O} = \mathbb{Z} + \mathbb{Z}a\tau$.

No imaginary quadratic field containing $\Lambda$ is assumed: the conclusion shows that $\Lambda$
lies in one up to homothety.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare,
Fall 2025, Lecture 17, proof of Theorem 17.10 ($\mathfrak{a} = \alpha[1, \tau]$, the integral
minimal polynomial $ax^2 + bx + c$ of $\tau$ with $a > 0$, and $\mathcal{O} = [1, a\tau]$), with
Lemma 17.9 and Definition 17.16; the choice of $\tau$ in the upper half-plane and the comparison of
discriminants are written out here. -/
theorem exists_root_of_isProperIdeal {L : PeriodPair} {𝒪 : Subring ℂ} {ω : ℂ} (hω : ω.im ≠ 0)
    (h𝒪 : (𝒪 : Set ℂ) = (ofTau ω hω).lattice) {D : ℤ} (hD : (ω - conj ω) ^ 2 = D)
    (hL : L.IsProperIdeal 𝒪) :
    ∃ (a b c : ℤ) (τ : ℍ), Int.gcd (Int.gcd a b : ℤ) c = 1 ∧ 0 < a ∧ discrim a b c = D ∧
      (a : ℂ) * (τ : ℂ) ^ 2 + b * τ + c = 0 ∧ (ofTau τ τ.im_pos.ne').IsHomothetic L ∧
      (𝒪 : Set ℂ) = {z | ∃ m n : ℤ, z = m + n * ((a : ℂ) * τ)} := by
  obtain ⟨τ, hhom⟩ := exists_isHomothetic_ofTau L
  have hτ0 : (τ : ℂ).im ≠ 0 := τ.im_pos.ne'
  have hEnd : (ofTau τ hτ0).endomorphismRing = 𝒪 := by
    have hL' : L.endomorphismRing = 𝒪 := hL
    rw [← hL']; exact hhom.endomorphismRing_eq.symm
  have hωO : ω ∈ (ofTau τ hτ0).endomorphismRing := by
    rw [hEnd, ← SetLike.mem_coe, h𝒪]; exact mem_lattice_ofTau.mpr ⟨0, 1, by simp⟩
  obtain ⟨m, n, hmn⟩ := mem_lattice_ofTau.mp
    (hωO 1 (mem_lattice_ofTau.mpr ⟨1, 0, by simp⟩))
  obtain ⟨u, v, huv⟩ := mem_lattice_ofTau.mp
    (hωO τ (mem_lattice_ofTau.mpr ⟨0, 1, by simp⟩))
  rw [mul_one] at hmn
  have hn : n ≠ 0 := by
    rintro rfl
    apply hω
    rw [hmn]; simp
  have hquad : (n : ℂ) * (τ : ℂ) ^ 2 + ((m - v : ℤ) : ℂ) * τ + ((-u : ℤ) : ℂ) = 0 := by
    rw [hmn] at huv
    push_cast
    linear_combination huv
  obtain ⟨a, b, c, hprim, ha, hroot⟩ := exists_primitive_root hn hquad
  have hdisc : discrim a b c < 0 := discrim_neg_of_root ha.ne' hτ0 hroot
  obtain ⟨hE, -, hEdisc⟩ := BinaryQuadraticForm.endomorphismRing_ofTau hprim hdisc hroot
  have haτ : ((a : ℂ) * τ).im ≠ 0 := by
    simp only [mul_im, intCast_re, intCast_im, zero_mul, add_zero]
    exact mul_ne_zero (by exact_mod_cast ha.ne') hτ0
  have hset : (𝒪 : Set ℂ) = {z | ∃ m n : ℤ, z = m + n * ((a : ℂ) * τ)} := by
    rw [← hEnd]; exact hE
  have hlat : ((ofTau ((a : ℂ) * τ) haτ).lattice : Set ℂ) = (ofTau ω hω).lattice := by
    rw [← h𝒪, hset]
    ext z
    simp only [SetLike.mem_coe, mem_lattice_ofTau, Set.mem_ofPred_eq]
  have := sq_sub_conj_eq_of_lattice_ofTau_eq haτ hω hlat
  refine ⟨a, b, c, τ, hprim, ha, ?_, hroot, hhom, hset⟩
  have : ((discrim a b c : ℤ) : ℂ) = D := by rw [← hEdisc, this, hD]
  exact_mod_cast this

end PeriodPair
