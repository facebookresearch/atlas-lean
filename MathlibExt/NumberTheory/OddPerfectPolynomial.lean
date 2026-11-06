/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization

@[expose] public section

namespace MetaMathlibExt

/-! # Odd perfect polynomials over F₂ are squares
-/

/-- A polynomial over `F₂` coprime to `X` takes value `1` at `0`. -/
private theorem eval_zero_eq_one_of_isCoprime_X
    (p : Polynomial (ZMod 2))
    (h : IsCoprime p Polynomial.X) :
    p.eval 0 = 1 := by
  have hmap := h.map (Polynomial.evalRingHom (0 : ZMod 2))
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_X] at hmap
  have hu : IsUnit (p.eval 0) := isCoprime_zero_right.mp hmap
  have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h2 (p.eval 0) with h0 | h1
  · exfalso
    rw [h0] at hu
    exact not_isUnit_zero hu
  · exact h1

/--
**Odd perfect polynomials over $\mathbb{F}_2$ are squares (Canaday).** Let $A$ be a polynomial
over $\mathbb{F}_2$ that is coprime to both $X$ and $X + 1$ (that is, odd: $A$ has no linear
factor) and that equals the sum of its monic divisors (that is, perfect). Then $A$ is a square:
$A = B^2$ for some polynomial $B$ over $\mathbb{F}_2$.

Since every nonzero polynomial over $\mathbb{F}_2$ is monic, the sum over monic divisors is the
full divisor sum.

Source: Luis H. Gallardo and Olivier Rahavandrainy, "A Polynomial Variant of
Perfect Numbers," Journal of Integer Sequences 23 (2020), Article 20.8.6,
Lemma `oddperfect`, lines 155–158 (odd and perfect defined lines 96–108),
https://cs.uwaterloo.ca/journals/JIS/VOL23/Gallardo/gallardo7.tex
attributed there to Canaday.
Proves `Wanted` entry `odd_perfect_polynomial_is_square`.
-/
theorem odd_perfect_polynomial_is_square
    (A : Polynomial (ZMod 2))
    (hodd : IsCoprime A Polynomial.X ∧ IsCoprime A (Polynomial.X + 1))
    (hperfect : (finsum fun d : {d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A} =>
      (d : Polynomial (ZMod 2))) = A) :
    IsSquare A := by
  obtain ⟨hoddX, -⟩ := hodd
  have hAeval : A.eval 0 = 1 := eval_zero_eq_one_of_isCoprime_X A hoddX
  have hA0 : A ≠ 0 := by
    rintro rfl
    simp at hAeval
  have hAmonic : A.Monic := by
    have hlc : A.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hA0
    have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rcases h2 A.leadingCoeff with h | h
    · exact absurd h hlc
    · exact h
  haveI : Fintype { d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A } :=
    Polynomial.fintypeSubtypeMonicDvd A hA0
  rw [finsum_eq_sum_of_fintype] at hperfect
  have hterm : ∀ d : { d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A }, d.val.eval 0 = 1 :=
    fun d => eval_zero_eq_one_of_isCoprime_X d.val
      (hoddX.of_isCoprime_of_dvd_left d.2.2)
  have hsum0 : (∑ _x : { d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A }, (1 : ZMod 2)) = 1 := by
    have hcongr := congrArg ⇑(Polynomial.evalRingHom (0 : ZMod 2)) hperfect
    rw [map_sum] at hcongr
    simp only [Polynomial.coe_evalRingHom] at hcongr
    rw [hAeval] at hcongr
    simpa only [hterm] using hcongr
  have hφmonic : ∀ d : { d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A }, (A / d.val).Monic := by
    intro d
    have hd0 : d.val ≠ 0 := d.2.1.ne_zero
    have hmul : d.val * (A / d.val) = A := EuclideanDomain.mul_div_cancel' hd0 d.2.2
    have hAm : (d.val * (A / d.val)).Monic := by
      rw [hmul]
      exact hAmonic
    exact d.2.1.of_mul_monic_left hAm
  have hφdvd : ∀ d : { d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A }, (A / d.val) ∣ A := by
    intro d
    have hd0 : d.val ≠ 0 := d.2.1.ne_zero
    have hmul : d.val * (A / d.val) = A := EuclideanDomain.mul_div_cancel' hd0 d.2.2
    have heq : A = A / d.val * d.val := hmul.symm.trans (mul_comm d.val (A / d.val))
    exact ⟨d.val, heq⟩
  have hdivinv : ∀ d : { d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A },
      A / (A / d.val) = d.val := by
    intro d
    have hd0 : d.val ≠ 0 := d.2.1.ne_zero
    have he0 : A / d.val ≠ 0 := (hφmonic d).ne_zero
    rw [EuclideanDomain.div_eq_iff_eq_mul_of_dvd _ _ _ he0 (hφdvd d)]
    have hmul : d.val * (A / d.val) = A := EuclideanDomain.mul_div_cancel' hd0 d.2.2
    exact hmul.symm.trans (mul_comm d.val (A / d.val))
  have hex : ∃ d : { d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A }, A / d.val = d.val := by
    by_contra hcon
    have hcon' : ∀ d : { d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A }, A / d.val ≠ d.val :=
      fun d h => hcon ⟨d, h⟩
    have hzero : (∑ _x : { d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A }, (1 : ZMod 2)) = 0 := by
      refine Finset.sum_involution
        (fun (a : { d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A }) (_ : a ∈ Finset.univ) =>
          (⟨A / a.val, hφmonic a, hφdvd a⟩ :
            { d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A })) ?_ ?_ ?_ ?_
      · intro a ha
        show (1 : ZMod 2) + 1 = 0
        decide
      · intro a ha _ hcontra
        have hcontra' : A / a.val = a.val := congrArg Subtype.val hcontra
        exact hcon' a hcontra'
      · intro a ha
        exact Finset.mem_univ _
      · intro a ha
        have hsub : A / (A / a.val) = a.val := hdivinv a
        apply Subtype.ext
        exact hsub
    rw [hsum0] at hzero
    exact one_ne_zero hzero
  obtain ⟨d, hd⟩ := hex
  have hd0 : d.val ≠ 0 := d.2.1.ne_zero
  have hdsq : A = d.val * d.val := by
    rw [EuclideanDomain.div_eq_iff_eq_mul_of_dvd _ _ _ hd0 d.2.2] at hd
    exact hd
  exact isSquare_iff_exists_mul_self A |>.mpr ⟨d.val, hdsq⟩

end MetaMathlibExt
