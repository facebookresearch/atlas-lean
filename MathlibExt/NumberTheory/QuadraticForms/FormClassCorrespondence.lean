/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticForms.ProperIdealRootLattice
public import MathlibExt.NumberTheory.QuadraticForms.GaussClassNumber
public import MathlibExt.NumberTheory.Modular.HalfOpenFundamentalDomain
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Form classes and proper ideal classes of an imaginary quadratic order

Let $D$ be an imaginary quadratic discriminant and $\mathcal{O}$ the order
$\mathbb{Z} + \mathbb{Z}\frac{D + \sqrt{D}}{2}$ of discriminant $D$. For a primitive positive
definite form $f = (a, b, c)$ of discriminant $D$, the lattice
$\mathfrak{a}_f = \mathbb{Z}a + \mathbb{Z}\frac{-b + \sqrt{D}}{2}$ is a proper ideal of
$\mathcal{O}$, and $f \mapsto [\mathfrak{a}_f]$ is a bijection from the proper equivalence classes
of such forms onto the homothety classes of proper ideals of $\mathcal{O}$, whose number is
therefore the Gauss class number $h(D)$
(`BinaryQuadraticForm.formClasses_equiv_properIdealClasses`).

The sources are David A. Cox, *Primes of the form* $x^2 + ny^2$, Theorem 7.7, as used by David Cox,
John McKay and Peter Stevenhagen, *Principal moduli and class fields*, Bull. London Math. Soc. 36
(2004), 3–12, §2, and Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT
OpenCourseWare, Fall 2025, Lectures 15–17.
-/

@[expose] public section

open Complex PeriodPair

open scoped ComplexConjugate MatrixGroups UpperHalfPlane

namespace BinaryQuadraticForm

section Aux

variable {D : ℤ}

private theorem sqrt_sq_eq (hD : D < 0) : (Real.sqrt |(D : ℝ)|) ^ 2 = -(D : ℝ) := by
  rw [Real.sq_sqrt (abs_nonneg _), abs_of_neg (by exact_mod_cast hD)]

private theorem sqrt_pos' (hD : D < 0) : 0 < Real.sqrt |(D : ℝ)| :=
  Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast hD.ne))

/-- The root `(-b + i √|D|) / (2a)` of `(a, b, c)` lies in the upper half-plane. -/
private theorem root_im_pos {a b : ℤ} (ha : 0 < a) (hD : D < 0) :
    0 < ((-b + I * (Real.sqrt |(D : ℝ)| : ℂ)) / (2 * a)).im := by
  have : ((-b + I * (Real.sqrt |(D : ℝ)| : ℂ)) / (2 * a)) =
      ((-b / (2 * a) : ℝ) : ℂ) + I * ((Real.sqrt |(D : ℝ)| / (2 * a) : ℝ) : ℂ) := by
    push_cast; field_simp
  rw [this]
  simp only [add_im, ofReal_im, mul_im, I_re, ofReal_re, zero_mul, I_im, one_mul, zero_add]
  exact div_pos (sqrt_pos' hD) (by positivity)

/-- The root of a form of discriminant `D` in the upper half-plane. -/
private noncomputable def rootH {a b : ℤ} (ha : 0 < a) (hD : D < 0) : ℍ :=
  UpperHalfPlane.mk ((-b + I * (Real.sqrt |(D : ℝ)| : ℂ)) / (2 * a)) (root_im_pos ha hD)

private theorem rootH_coe {a b : ℤ} (ha : 0 < a) (hD : D < 0) :
    ((rootH (b := b) ha hD : ℍ) : ℂ) = (-b + I * (Real.sqrt |(D : ℝ)| : ℂ)) / (2 * a) :=
  UpperHalfPlane.coe_mk _ _

private theorem rootH_root {a b c : ℤ} (ha : 0 < a) (hD : D < 0) (hdisc : discrim a b c = D) :
    (a : ℂ) * ((rootH (b := b) ha hD : ℍ) : ℂ) ^ 2 + b * ((rootH (b := b) ha hD : ℍ) : ℂ) + c =
      0 := by
  rw [rootH_coe]
  have hs : ((Real.sqrt |(D : ℝ)| : ℝ) : ℂ) ^ 2 = -(D : ℂ) := by
    exact_mod_cast sqrt_sq_eq hD
  have hd : (D : ℂ) = b ^ 2 - 4 * a * c := by rw [← hdisc]; push_cast [discrim]; ring
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  set τ : ℂ := (-b + I * (Real.sqrt |(D : ℝ)| : ℂ)) / (2 * a) with hτ
  have h2 : 2 * a * τ = -b + I * (Real.sqrt |(D : ℝ)| : ℂ) := by rw [hτ]; field_simp
  have hI : I ^ 2 = -1 := I_sq
  have key : (4 * a : ℂ) * ((a : ℂ) * τ ^ 2 + b * τ + c) = 0 := by
    linear_combination (2 * a * τ + (-b + I * (Real.sqrt |(D : ℝ)| : ℂ)) + 2 * b) * h2 +
      I ^ 2 * hs - (D : ℂ) * hI + hd
  exact (mul_eq_zero.mp key).resolve_left (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) ha')

/-- A period pair with periods `a` and `aτ` is homothetic to `ℤ + ℤτ`. -/
private theorem isHomothetic_of_periods {L : PeriodPair} {a : ℤ} (ha : 0 < a) {τ : ℂ}
    (hτ : τ.im ≠ 0) (h1 : L.ω₁ = a) (h2 : L.ω₂ = a * τ) : (ofTau τ hτ).IsHomothetic L := by
  refine ⟨a, by exact_mod_cast ha.ne', ?_⟩
  ext z
  simp only [SetLike.mem_coe, Set.mem_smul_set, mem_lattice, smul_eq_mul, ofTau_ω₁, ofTau_ω₂,
    h1, h2]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨m + n * τ, ⟨m, n, by ring⟩, by ring⟩
  · rintro ⟨_, ⟨m, n, rfl⟩, rfl⟩
    exact ⟨m, n, by ring⟩

/-- Period pairs with the same periods are equal. -/
private theorem periodPair_eq {L L' : PeriodPair} (h1 : L.ω₁ = L'.ω₁) (h2 : L.ω₂ = L'.ω₂) :
    L = L' := by
  cases L; cases L'; simp only at h1 h2; subst h1; subst h2; rfl

/-- The lattice `ℤa + ℤ(-b + √D)/2` of a form, as a period pair. -/
private noncomputable def formLattice {a b : ℤ} (ha : 0 < a) (hD : D < 0) : PeriodPair :=
  (ofTau ((rootH (b := b) ha hD : ℍ) : ℂ) (rootH ha hD).im_pos.ne').scale
    (Units.mk0 (a : ℂ) (by exact_mod_cast ha.ne'))

private theorem formLattice_ω₁ {a b : ℤ} (ha : 0 < a) (hD : D < 0) :
    (formLattice (b := b) ha hD).ω₁ = a := by
  change (a : ℂ) * 1 = a
  ring

private theorem formLattice_ω₂ {a b : ℤ} (ha : 0 < a) (hD : D < 0) :
    (formLattice (b := b) ha hD).ω₂ = (-b + I * (Real.sqrt |(D : ℝ)| : ℂ)) / 2 := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  simp only [formLattice, scale_ω₂, Units.val_mk0, ofTau_ω₂, rootH_coe]
  field_simp

/-- The order `ℤ + ℤ(D + √D)/2` as the lattice of a period pair. -/
private theorem order_set_eq {D : ℤ} {𝒪 : Subring ℂ}
    (h𝒪 : (𝒪 : Set ℂ) = {z | ∃ m n : ℤ, z = m + n * ((D + I * (Real.sqrt |(D : ℝ)| : ℂ)) / 2)})
    (hω : ((D + I * (Real.sqrt |(D : ℝ)| : ℂ)) / 2).im ≠ 0) :
    (𝒪 : Set ℂ) = (ofTau _ hω).lattice := by
  rw [h𝒪]; ext z; simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_lattice_ofTau]

/-- The lattice of a primitive positive definite form of discriminant `D` is a proper ideal of the
order of discriminant `D`. -/
private theorem isProperIdeal_of_form {D : ℤ} (hD : D < 0) {𝒪 : Subring ℂ}
    (h𝒪 : (𝒪 : Set ℂ) = {z | ∃ m n : ℤ, z = m + n * ((D + I * (Real.sqrt |(D : ℝ)| : ℂ)) / 2)})
    {a b c : ℤ} (hprim : Int.gcd (Int.gcd a b : ℤ) c = 1) (ha : 0 < a) (hdisc : discrim a b c = D)
    {L : PeriodPair} (h1 : L.ω₁ = a) (h2 : L.ω₂ = (-b + I * (Real.sqrt |(D : ℝ)| : ℂ)) / 2) :
    L.IsProperIdeal 𝒪 := by
  set τ : ℍ := rootH (b := b) ha hD
  have hτ0 : (τ : ℂ).im ≠ 0 := τ.im_pos.ne'
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have haτ : (a : ℂ) * τ = (-b + I * (Real.sqrt |(D : ℝ)| : ℂ)) / 2 := by
    rw [rootH_coe]; field_simp
  have hhom : (ofTau τ hτ0).IsHomothetic L :=
    isHomothetic_of_periods ha hτ0 h1 (by rw [h2, haτ])
  obtain ⟨hE, -, -⟩ := endomorphismRing_ofTau hprim (hdisc ▸ hD) (rootH_root ha hD hdisc)
  -- `D + b` is even
  obtain ⟨k, hk⟩ : ∃ k : ℤ, D + b = 2 * k := by
    refine ⟨(D + b) / 2, ?_⟩
    have : (D + b) % 2 = 0 := by
      rw [← hdisc, discrim]
      rcases Int.emod_two_eq_zero_or_one b with h | h <;>
        simp [Int.add_emod, Int.sub_emod, pow_two, Int.mul_emod, h]
    omega
  have hshift : (a : ℂ) * τ = (D + I * (Real.sqrt |(D : ℝ)| : ℂ)) / 2 - k := by
    rw [haτ]
    have : (D : ℂ) + b = 2 * k := by exact_mod_cast hk
    linear_combination (-1 / 2 : ℂ) * this
  have hEnd : L.endomorphismRing = (ofTau τ hτ0).endomorphismRing := hhom.endomorphismRing_eq
  refine SetLike.coe_injective (?_ : (L.endomorphismRing : Set ℂ) = 𝒪)
  rw [hEnd, hE, h𝒪]
  ext z
  have hs' : (a : ℂ) * ((rootH (b := b) ha hD : ℍ) : ℂ) =
      (D + I * (Real.sqrt |(D : ℝ)| : ℂ)) / 2 - k := hshift
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨m - n * k, n, by push_cast; linear_combination (n : ℂ) * hs'⟩
  · rintro ⟨m, n, rfl⟩
    exact ⟨m + n * k, n, by push_cast; linear_combination (-(n : ℂ)) * hs'⟩

private theorem formLattice_isHomothetic {a b : ℤ} (ha : 0 < a) (hD : D < 0) :
    (ofTau ((rootH (b := b) ha hD : ℍ) : ℂ) (rootH ha hD).im_pos.ne').IsHomothetic
      (formLattice (b := b) ha hD) := by
  refine isHomothetic_of_periods ha _ (formLattice_ω₁ ha hD) ?_
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [formLattice_ω₂, rootH_coe]; field_simp

/-- Two primitive positive definite forms of discriminant `D` are properly equivalent exactly when
their lattices are homothetic. -/
private theorem properlyEquivalent_iff_isHomothetic (hD : D < 0) {f g : ℤ × ℤ × ℤ}
    (hf : Int.gcd (Int.gcd f.1 f.2.1 : ℤ) f.2.2 = 1)
    (hg : Int.gcd (Int.gcd g.1 g.2.1 : ℤ) g.2.2 = 1)
    (hfa : 0 < f.1) (hga : 0 < g.1) (hfd : discrim f.1 f.2.1 f.2.2 = D)
    (hgd : discrim g.1 g.2.1 g.2.2 = D) {L L' : PeriodPair} (h1 : L.ω₁ = f.1)
    (h2 : L.ω₂ = (-f.2.1 + I * (Real.sqrt |(D : ℝ)| : ℂ)) / 2) (h1' : L'.ω₁ = g.1)
    (h2' : L'.ω₂ = (-g.2.1 + I * (Real.sqrt |(D : ℝ)| : ℂ)) / 2) :
    ProperlyEquivalent f g ↔ L.IsHomothetic L' := by
  set τf : ℍ := rootH (b := f.2.1) hfa hD
  set τg : ℍ := rootH (b := g.2.1) hga hD
  have hfa' : (f.1 : ℂ) ≠ 0 := by exact_mod_cast hfa.ne'
  have hga' : (g.1 : ℂ) ≠ 0 := by exact_mod_cast hga.ne'
  have hLf : (ofTau τf τf.im_pos.ne').IsHomothetic L :=
    isHomothetic_of_periods hfa _ h1 (by rw [h2, rootH_coe]; field_simp)
  have hLg : (ofTau τg τg.im_pos.ne').IsHomothetic L' :=
    isHomothetic_of_periods hga _ h1' (by rw [h2', rootH_coe]; field_simp)
  rw [properlyEquivalent_iff_exists_smul hf hg hfa hga (hfd ▸ hD) (rootH_root hfa hD hfd)
    (rootH_root hga hD hgd), ← isHomothetic_ofTau_iff]
  constructor
  · intro h; exact hLf.symm.trans (h.trans hLg)
  · intro h; exact hLf.trans (h.trans hLg.symm)

/-- Every proper ideal of the order of discriminant `D` is homothetic to the lattice of a primitive
positive definite form of discriminant `D`. -/
private theorem exists_form_of_isProperIdeal
    (hD : ImaginaryQuadraticDiscriminant.IsImaginaryQuadraticDiscriminant D) {𝒪 : Subring ℂ}
    (h𝒪 : (𝒪 : Set ℂ) = {z | ∃ m n : ℤ, z = m + n * ((D + I * (Real.sqrt |(D : ℝ)| : ℂ)) / 2)})
    {L : PeriodPair} (hL : L.IsProperIdeal 𝒪) :
    ∃ (f : ℤ × ℤ × ℤ) (hfa : 0 < f.1), Int.gcd (Int.gcd f.1 f.2.1 : ℤ) f.2.2 = 1 ∧
      discrim f.1 f.2.1 f.2.2 = D ∧ (formLattice (b := f.2.1) hfa hD.1).IsHomothetic L := by
  obtain ⟨hω, -, hdisc, -⟩ := order_of_discriminant hD
  obtain ⟨a, b, c, τ, hprim, ha, hd, hroot, hhom, -⟩ :=
    exists_root_of_isProperIdeal hω (order_set_eq h𝒪 hω) hdisc hL
  have hτ : τ = rootH (b := b) ha hD.1 := root_unique ha.ne' hroot (rootH_root ha hD.1 hd)
  subst hτ
  exact ⟨(a, b, c), ha, hprim, hd, (formLattice_isHomothetic ha hD.1).symm.trans hhom⟩

/-- Each primitive positive definite form is properly equivalent to a Gauss-reduced form. -/
private theorem exists_reduced (hD : D < 0) {f : ℤ × ℤ × ℤ}
    (hf : Int.gcd (Int.gcd f.1 f.2.1 : ℤ) f.2.2 = 1) (hfa : 0 < f.1)
    (hfd : discrim f.1 f.2.1 f.2.2 = D) :
    ∃ g : ℤ × ℤ × ℤ, ProperlyEquivalent f g ∧ IsGaussReduced g.1 g.2.1 g.2.2 ∧
      Int.gcd (Int.gcd g.1 g.2.1 : ℤ) g.2.2 = 1 ∧ discrim g.1 g.2.1 g.2.2 = D := by
  obtain ⟨⟨γ, hγ⟩, -⟩ := ModularGroup.exists_smul_mem_halfOpen_and_eq (rootH (b := f.2.1) hfa hD)
  obtain ⟨hgp, hgd, -, hga, hgr⟩ :=
    substitute_root hf hfa (hfd ▸ hD) (rootH_root hfa hD hfd) γ⁻¹
  rw [inv_inv] at hgr
  refine ⟨substitute f γ⁻¹, ⟨γ⁻¹, rfl⟩, ?_, hgp, hgd.trans hfd⟩
  exact (isGaussReduced_iff_root_mem hga (hgd.trans hfd ▸ hD) hgr).mpr hγ

/-- Two properly equivalent primitive Gauss-reduced forms are equal. -/
private theorem eq_of_reduced (hD : D < 0) {f g : ℤ × ℤ × ℤ}
    (hf : Int.gcd (Int.gcd f.1 f.2.1 : ℤ) f.2.2 = 1)
    (hg : Int.gcd (Int.gcd g.1 g.2.1 : ℤ) g.2.2 = 1)
    (hfr : IsGaussReduced f.1 f.2.1 f.2.2) (hgr : IsGaussReduced g.1 g.2.1 g.2.2)
    (hfd : discrim f.1 f.2.1 f.2.2 = D) (hgd : discrim g.1 g.2.1 g.2.2 = D)
    (h : ProperlyEquivalent f g) : f = g := by
  have hfa := hfr.pos
  have hga := hgr.pos
  have rf := rootH_root hfa hD hfd
  have rg := rootH_root hga hD hgd
  have hFf := (isGaussReduced_iff_root_mem hfa (hfd ▸ hD) rf).mp hfr
  have hFg := (isGaussReduced_iff_root_mem hga (hgd ▸ hD) rg).mp hgr
  obtain ⟨γ, hγ⟩ := (properlyEquivalent_iff_exists_smul hf hg hfa hga (hfd ▸ hD) rf rg).mp h
  have hfix := (ModularGroup.exists_smul_mem_halfOpen_and_eq (rootH (b := f.2.1) hfa hD)).2 γ hFf
    (hγ ▸ hFg)
  rw [hfix] at hγ
  exact eq_of_root hf hg hfa hga rf (hγ ▸ rg)

/-- Gauss reducedness is decidable, as in the definition of `reducedFormsOfDiscriminant`. -/
private local instance decidableIsGaussReducedAux (a b c : ℤ) : Decidable (IsGaussReduced a b c) :=
  inferInstanceAs (Decidable (0 < a ∧ discrim a b c < 0 ∧ |b| ≤ a ∧ a ≤ c ∧
    ((|b| = a ∨ a = c) → 0 ≤ b)))

/-- Membership in the finite set of reduced forms of discriminant `D`. -/
private theorem mem_reducedForms {q : ℤ × ℤ × ℤ} :
    q ∈ MetaMathlibExt.reducedFormsOfDiscriminant D ↔
      IsGaussReduced q.1 q.2.1 q.2.2 ∧ discrim q.1 q.2.1 q.2.2 = D := by
  unfold MetaMathlibExt.reducedFormsOfDiscriminant
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨hred, hd⟩ := h
  obtain ⟨a, b, c⟩ := q
  simp only at hred hd ⊢
  have ha := hred.pos
  have hb := hred.abs_le
  have hac := hred.le
  have hbl := (abs_le.mp hb).1
  have hbu := (abs_le.mp hb).2
  have hb2 : b ^ 2 ≤ a ^ 2 := by nlinarith [sq_abs b, abs_nonneg b]
  have h3 : 3 * a ^ 2 ≤ -D := by rw [← hd]; unfold discrim; nlinarith
  rw [Finset.mem_biUnion]
  refine ⟨a, ?_, ?_⟩
  · rw [Finset.mem_Icc]
    refine ⟨ha, ?_⟩
    have hle : a.toNat * a.toNat ≤ (-D).toNat := by
      have : (a.toNat : ℤ) * a.toNat ≤ ((-D).toNat : ℤ) := by
        rw [Int.toNat_of_nonneg ha.le, Int.toNat_of_nonneg (by nlinarith)]; nlinarith
      exact_mod_cast this
    have := Nat.le_sqrt.mpr hle
    have e : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha.le
    omega
  · rw [Finset.mem_image]
    refine ⟨b, Finset.mem_Icc.mpr ⟨hbl, hbu⟩, ?_⟩
    have : b ^ 2 - D = 4 * a * c := by rw [← hd]; unfold discrim; ring
    rw [this, Int.mul_ediv_cancel_left _ (by positivity)]

end Aux

/-- **Form classes and proper ideal classes of an imaginary quadratic order.** Let $D$ be an
imaginary quadratic discriminant ($D < 0$, $D \equiv 0, 1 \pmod 4$), let $\sqrt{D} = i\sqrt{|D|}$,
and let $\mathcal{O} \subseteq \mathbb{C}$ be a subring whose underlying set is the order
$\mathbb{Z} + \mathbb{Z}\,\frac{D + \sqrt{D}}{2}$ of discriminant $D$. Write $S_D$ for the set of
integer triples $f = (a, b, c)$, standing for $ax^2 + bxy + cy^2$, with $\gcd(a, b, c) = 1$, $a > 0$
and $b^2 - 4ac = D$ (the primitive positive definite forms of discriminant $D$). Then:

1. for $f = (a, b, c) \in S_D$, every period pair with periods $a$ and
   $\frac{-b + \sqrt{D}}{2}$, whose lattice is
   $\mathfrak{a}_f = \mathbb{Z}a + \mathbb{Z}\,\frac{-b + \sqrt{D}}{2}$, is a proper ideal of
   $\mathcal{O}$: its endomorphism ring is $\mathcal{O}$;
2. there is a bijection from the classes of $S_D$ under proper equivalence (equivalence under
   $\mathrm{SL}_2(\mathbb{Z})$) onto the classes, under homothety, of the period pairs that are
   proper ideals of $\mathcal{O}$, sending the class of $f$ to the class of $\mathfrak{a}_f$;
3. the number of these homothety classes is the Gauss class number $h(D)$, the number of reduced
   primitive positive definite forms of discriminant $D$.

The homothety classes of proper ideals are the classes of proper fractional $\mathcal{O}$-ideals
modulo principal ideals, so (3) is $h(\mathcal{O}) = h(D)$; no lattice is required to lie in
$\mathbb{Q}(\sqrt{D})$, as every proper ideal of $\mathcal{O}$ is homothetic to one that does.

Source: David A. Cox, *Primes of the form* $x^2 + ny^2$, Wiley, New York, 1989, Theorem 7.7, as
used by David Cox, John McKay and Peter Stevenhagen, *Principal moduli and class fields*, Bull.
London Math. Soc. 36 (2004), 3–12, §2, and by Yuri Bilu, Florian Luca and Amalia
Pizarro-Madariaga, *Rational products of singular moduli*, J. Number Theory 158 (2016), 397–410,
proof of Proposition 2.5; the proof follows Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture
notes, MIT OpenCourseWare, Fall 2025, Lectures 15–17 (Lemmas 15.9 and 15.10, Theorems 17.10 and
17.18), and the deduction is written out here. -/
theorem formClasses_equiv_properIdealClasses {D : ℤ}
    (hD : ImaginaryQuadraticDiscriminant.IsImaginaryQuadraticDiscriminant D) {𝒪 : Subring ℂ}
    (h𝒪 : (𝒪 : Set ℂ) = {z | ∃ m n : ℤ, z = m + n * ((D + I * (Real.sqrt |(D : ℝ)| : ℂ)) / 2)}) :
    (∀ (f : ℤ × ℤ × ℤ) (L : PeriodPair), Int.gcd (Int.gcd f.1 f.2.1 : ℤ) f.2.2 = 1 → 0 < f.1 →
      discrim f.1 f.2.1 f.2.2 = D → L.ω₁ = f.1 →
      L.ω₂ = (-f.2.1 + I * (Real.sqrt |(D : ℝ)| : ℂ)) / 2 → L.IsProperIdeal 𝒪) ∧
    (∃ e : Quot (fun f g : {f : ℤ × ℤ × ℤ // Int.gcd (Int.gcd f.1 f.2.1 : ℤ) f.2.2 = 1 ∧
          0 < f.1 ∧ discrim f.1 f.2.1 f.2.2 = D} => ProperlyEquivalent f.1 g.1) ≃
        Quot (fun L L' : {L : PeriodPair // L.IsProperIdeal 𝒪} => L.1.IsHomothetic L'.1),
      ∀ f L (hL : L.IsProperIdeal 𝒪), L.ω₁ = f.1.1 →
        L.ω₂ = (-f.1.2.1 + I * (Real.sqrt |(D : ℝ)| : ℂ)) / 2 →
          e (Quot.mk _ f) = Quot.mk _ ⟨L, hL⟩) ∧
    Nat.card (Quot (fun L L' : {L : PeriodPair // L.IsProperIdeal 𝒪} => L.1.IsHomothetic L'.1)) =
      MetaMathlibExt.gaussClassNumber D := by
  have hD0 : D < 0 := hD.1
  -- the two relations are equivalences
  have eqvF : Equivalence (fun f g : {f : ℤ × ℤ × ℤ // Int.gcd (Int.gcd f.1 f.2.1 : ℤ) f.2.2 = 1 ∧
      0 < f.1 ∧ discrim f.1 f.2.1 f.2.2 = D} => ProperlyEquivalent f.1 g.1) :=
    ⟨fun f => ProperlyEquivalent.refl _, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
  have eqvL : Equivalence
      (fun L L' : {L : PeriodPair // L.IsProperIdeal 𝒪} => L.1.IsHomothetic L'.1) :=
    ⟨fun L => IsHomothetic.refl _, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
  have hprop : ∀ (f : ℤ × ℤ × ℤ) (L : PeriodPair), Int.gcd (Int.gcd f.1 f.2.1 : ℤ) f.2.2 = 1 →
      0 < f.1 → discrim f.1 f.2.1 f.2.2 = D → L.ω₁ = f.1 →
      L.ω₂ = (-f.2.1 + I * (Real.sqrt |(D : ℝ)| : ℂ)) / 2 → L.IsProperIdeal 𝒪 :=
    fun f L hf hfa hfd h1 h2 => isProperIdeal_of_form hD0 h𝒪 hf hfa hfd h1 h2
  -- the map on classes
  let Φ : {f : ℤ × ℤ × ℤ // Int.gcd (Int.gcd f.1 f.2.1 : ℤ) f.2.2 = 1 ∧ 0 < f.1 ∧
      discrim f.1 f.2.1 f.2.2 = D} → {L : PeriodPair // L.IsProperIdeal 𝒪} := fun f =>
    ⟨formLattice (b := f.1.2.1) f.2.2.1 hD0, hprop f.1 _ f.2.1 f.2.2.1 f.2.2.2
      (formLattice_ω₁ _ _) (formLattice_ω₂ _ _)⟩
  have hΦ : ∀ f g, ProperlyEquivalent f.1 g.1 ↔ (Φ f).1.IsHomothetic (Φ g).1 := fun f g =>
    properlyEquivalent_iff_isHomothetic hD0 f.2.1 g.2.1 f.2.2.1 g.2.2.1 f.2.2.2 g.2.2.2
      (formLattice_ω₁ _ _) (formLattice_ω₂ _ _) (formLattice_ω₁ _ _) (formLattice_ω₂ _ _)
  let F : Quot (fun f g : {f : ℤ × ℤ × ℤ // Int.gcd (Int.gcd f.1 f.2.1 : ℤ) f.2.2 = 1 ∧
        0 < f.1 ∧ discrim f.1 f.2.1 f.2.2 = D} => ProperlyEquivalent f.1 g.1) →
      Quot (fun L L' : {L : PeriodPair // L.IsProperIdeal 𝒪} => L.1.IsHomothetic L'.1) :=
    Quot.lift (fun f => Quot.mk _ (Φ f)) (fun f g h => Quot.sound ((hΦ f g).mp h))
  have hFinj : Function.Injective F := by
    intro x y hxy
    induction x using Quot.ind with | mk f => ?_
    induction y using Quot.ind with | mk g => ?_
    have h : (Φ f).1.IsHomothetic (Φ g).1 := (eqvL.eqvGen_iff).mp (Quot.eqvGen_exact hxy)
    exact Quot.sound ((hΦ f g).mpr h)
  have hFsurj : Function.Surjective F := by
    intro y
    induction y using Quot.ind with | mk L => ?_
    obtain ⟨f, hfa, hf, hfd, hhom⟩ := exists_form_of_isProperIdeal hD h𝒪 L.2
    exact ⟨Quot.mk _ ⟨f, hf, hfa, hfd⟩, Quot.sound hhom⟩
  let e := Equiv.ofBijective F ⟨hFinj, hFsurj⟩
  refine ⟨hprop, ⟨e, fun f L hL h1 h2 => ?_⟩, ?_⟩
  · change Quot.mk _ (Φ f) = Quot.mk _ ⟨L, hL⟩
    congr 1
    apply Subtype.ext
    exact periodPair_eq ((formLattice_ω₁ _ _).trans h1.symm) ((formLattice_ω₂ _ _).trans h2.symm)
  · rw [← Nat.card_congr e]
    -- the reduced primitive forms of discriminant `D` represent the classes once each
    let T := (MetaMathlibExt.reducedFormsOfDiscriminant D).filter
      fun q => Int.gcd (Int.gcd q.1 q.2.1 : ℤ) q.2.2 = 1
    have hmemT : ∀ q, q ∈ T ↔ (IsGaussReduced q.1 q.2.1 q.2.2 ∧ discrim q.1 q.2.1 q.2.2 = D) ∧
        Int.gcd (Int.gcd q.1 q.2.1 : ℤ) q.2.2 = 1 := fun q => by
      rw [Finset.mem_filter, mem_reducedForms]
    let G : T → Quot (fun f g : {f : ℤ × ℤ × ℤ // Int.gcd (Int.gcd f.1 f.2.1 : ℤ) f.2.2 = 1 ∧
        0 < f.1 ∧ discrim f.1 f.2.1 f.2.2 = D} => ProperlyEquivalent f.1 g.1) := fun q =>
      Quot.mk _ ⟨q.1, ((hmemT q.1).mp q.2).2, ((hmemT q.1).mp q.2).1.1.pos,
        ((hmemT q.1).mp q.2).1.2⟩
    have hGinj : Function.Injective G := by
      intro q r hqr
      have h := (eqvF.eqvGen_iff).mp (Quot.eqvGen_exact hqr)
      obtain ⟨⟨hqr', hqd⟩, hqp⟩ := (hmemT q.1).mp q.2
      obtain ⟨⟨hrr, hrd⟩, hrp⟩ := (hmemT r.1).mp r.2
      exact Subtype.ext (eq_of_reduced hD0 hqp hrp hqr' hrr hqd hrd h)
    have hGsurj : Function.Surjective G := by
      intro x
      induction x using Quot.ind with | mk f => ?_
      obtain ⟨g, hfg, hgr, hgp, hgd⟩ := exists_reduced hD0 f.2.1 f.2.2.1 f.2.2.2
      exact ⟨⟨g, (hmemT g).mpr ⟨⟨hgr, hgd⟩, hgp⟩⟩, Quot.sound hfg.symm⟩
    rw [← Nat.card_congr (Equiv.ofBijective G ⟨hGinj, hGsurj⟩), Nat.card_eq_finsetCard]
    rfl

end BinaryQuadraticForm
