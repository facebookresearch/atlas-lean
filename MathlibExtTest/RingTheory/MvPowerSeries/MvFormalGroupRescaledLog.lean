/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPowerSeries.MvFormalGroupRescaledLog

import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

noncomputable section

namespace MetaMathlibExt

open MvPowerSeries

universe u

/-- Consumer with the original binders, restated verbatim. -/
private theorem exactSource {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm] :
    ∃ (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞) (φ : Fin d → MvPowerSeries (Fin d) 𝓞),
      (∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
        (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m) ∧
      (∀ i, (Fp i).constantCoeff = 0) ∧
      (∀ i, (φ i).constantCoeff = 0) ∧
      MvFormalGroup.linearPart φ = 1 ∧
      (∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite,
        (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N}) ∧
      (∀ i, subst Fp (φ i) =
        subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
          subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i)) :=
  MvFormalGroup.exists_rescaledLog_of_isAdicComplete p hp F

/-- The statement also applies in a higher universe. -/
example {𝓞 : Type (u + 1)} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm] :
    ∃ φ : Fin d → MvPowerSeries (Fin d) 𝓞, MvFormalGroup.linearPart φ = 1 := by
  obtain ⟨-, φ, -, -, -, h, -⟩ := MvFormalGroup.exists_rescaledLog_of_isAdicComplete p hp F
  exact ⟨φ, h⟩

/-- The additive formal group law is commutative, so it has such a logarithm. -/
example {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] (d : ℕ) :
    ∃ φ : Fin d → MvPowerSeries (Fin d) 𝓞,
      (∀ i, (φ i).constantCoeff = 0) ∧ MvFormalGroup.linearPart φ = 1 := by
  obtain ⟨-, φ, -, -, h0, h1, -⟩ :=
    MvFormalGroup.exists_rescaledLog_of_isAdicComplete p hp (MvFormalGroup.addMv d 𝓞)
  exact ⟨φ, h0, h1⟩

/-- The rescaling of the additive formal group law is itself: it has no terms of degree `≥ 2`,
and the degree-one terms are multiplied by `a ^ 0`. -/
example {R : Type*} [CommRing R] {a : R} (ha : a ∈ nonZeroDivisors R) (d : ℕ) :
    (MvFormalGroup.addMv d R).rescale ha = MvFormalGroup.addMv d R := by
  apply MvFormalGroup.ext
  funext i
  ext m
  rw [MvFormalGroup.coeff_rescale]
  change (if m = 0 then 0 else a ^ (m.degree - 1) *
    coeff m (X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) =
      coeff m (X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)
  by_cases h : m = Finsupp.single (Sum.inl i) 1 ∨ m = Finsupp.single (Sum.inr i) 1
  · rcases h with rfl | rfl <;> simp
  · simp only [not_or] at h
    simp [coeff_X, h.1, h.2]

/-- The coefficients of total degree `n ≥ 1` of `F.rescale ha`, multiplied by `a`, are those of
`F` multiplied by `a ^ n`. -/
example {R : Type*} [CommRing R] {a : R} (ha : a ∈ nonZeroDivisors R) {d : ℕ}
    (F : MvFormalGroup d R) (i : Fin d) (m : Fin d ⊕ Fin d →₀ ℕ) (hm : m ≠ 0) :
    coeff m ((F.rescale ha).toPowerSeries i) * a = a ^ m.degree * coeff m (F.toPowerSeries i) := by
  obtain ⟨t, ht⟩ : ∃ t, m.degree = t + 1 :=
    ⟨m.degree - 1, by have := (Finsupp.degree_eq_zero_iff m).not.mpr hm; omega⟩
  rw [MvFormalGroup.coeff_rescale, ite_eq_right hm, ht, Nat.add_sub_cancel, pow_succ]
  ring

/-- The rescaling of a commutative formal group law is commutative, so its endomorphisms form a
semiring. -/
example {R : Type*} [CommRing R] {a : R} (ha : a ∈ nonZeroDivisors R) {d : ℕ}
    (F : MvFormalGroup d R) [F.IsComm] : Semiring (MvFormalGroup.End (F.rescale ha)) :=
  inferInstance

/-- The logarithm of `MvFormalGroup.exists_log_rescale_of_isAdicComplete` is a homomorphism from
`F.rescale hp` to the additive formal group law with identity linear part. -/
example {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm] :
    ∃ φ : MvFormalGroup.Hom (F.rescale hp) (MvFormalGroup.addMv d 𝓞),
      MvFormalGroup.linearPart φ.toPowerSeries = 1 := by
  obtain ⟨φ, h0, h1, -, hlog⟩ := MvFormalGroup.exists_log_rescale_of_isAdicComplete p hp F
  refine ⟨⟨φ, h0, fun i => ?_⟩, h1⟩
  have hX : ∀ s : Fin d ⊕ Fin d, constantCoeff (X s : MvPowerSeries (Fin d ⊕ Fin d) 𝓞) = 0 :=
    fun s => constantCoeff_X s
  rw [hlog i]
  change _ = subst _ (X (Sum.inl i) + X (Sum.inr i))
  rw [MvFormalGroup.subst_X_add_X (by
    rintro (j | j)
    exacts [constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun l => hX _)
        (fun l => hX _) (h0 j),
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun l => hX _)
        (fun l => hX _) (h0 j)])]
  rfl

/-! ### Base change and `n`-series of the additive formal group law -/

section AddMv

open MvFormalGroup

variable {g : ℕ} {R S : Type*} [CommRing R] [CommRing S]

/-- Base change of the additive formal group law is the additive formal group law. -/
private theorem map_addMv (f : R →+* S) : (addMv g R).map f = addMv g S := by
  apply MvFormalGroup.ext
  funext i
  change MvPowerSeries.map f (X (Sum.inl i) + X (Sum.inr i)) =
    (X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin g ⊕ Fin g) S)
  rw [map_add, map_X, map_X]

/-- The `n`-series of the additive formal group law is `n • X`. -/
private theorem nthSeries_addMv (n : ℕ) (i : Fin g) :
    (addMv g R).nthSeries n i = n • (X i : MvPowerSeries (Fin g) R) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [nthSeries_succ]
    change subst (Sum.elim ((addMv g R).nthSeries n) fun j => X j)
        (X (Sum.inl i) + X (Sum.inr i)) = _
    rw [subst_X_add_X (by
      rintro (j | j)
      exacts [constantCoeff_nthSeries _ n j, constantCoeff_X j])]
    simp only [Sum.elim_inl, Sum.elim_inr, ih, succ_nsmul]

/-- The doubled variable `2 • X` is not the `1`-series of the additive law. -/
example : (addMv 1 ℤ).nthSeries 1 0 ≠ 2 • (X 0 : MvPowerSeries (Fin 1) ℤ) := by
  rw [nthSeries_addMv, one_smul, two_nsmul]
  intro h
  have := congrArg (coeff (Finsupp.single 0 1)) h
  simp [coeff_X] at this

end AddMv

/-! ### Homomorphisms of additive formal group laws given by matrices

A matrix `A` gives a homomorphism `linHom A` of additive formal group laws. `Hom.id`, `Hom.comp`,
the zero homomorphism and the sum of homomorphisms act on these as the identity matrix, the matrix
product (in this order), the zero matrix and the matrix sum, and `linearPart` recovers `A`. -/

section Hom

open MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R]

/-- Substitution into a linear form. -/
private theorem subst_sum_smul_X {τ : Type*} {n : ℕ} {b : Fin n → MvPowerSeries τ R}
    (hb : HasSubst b) (c : Fin n → R) :
    subst b (∑ j, c j • (X j : MvPowerSeries (Fin n) R)) = ∑ j, c j • b j := by
  rw [← coe_substAlgHom hb, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, coe_substAlgHom hb, subst_X hb]

/-- The homomorphism of additive formal group laws given by a matrix. -/
private def linHom (A : Matrix (Fin h) (Fin g) R) : Hom (addMv g R) (addMv h R) where
  toPowerSeries i := ∑ j, A i j • X j
  constantCoeff_eq_zero i := by simp
  subst_eq i := by
    have hXl : HasSubst (fun l : Fin g => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    have hXr : HasSubst (fun l : Fin g => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    change subst (fun j => (X (Sum.inl j) + X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (∑ j, A i j • X j) =
      subst (Sum.elim
          (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (∑ l, A j l • X l))
          fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (∑ l, A j l • X l))
        (X (Sum.inl i) + X (Sum.inr i))
    rw [subst_sum_smul_X (hasSubst_of_constantCoeff_zero fun j => by simp),
      subst_X_add_X (by rintro (j | j) <;> simp [subst_sum_smul_X hXl, subst_sum_smul_X hXr])]
    simp only [Sum.elim_inl, Sum.elim_inr, subst_sum_smul_X hXl, subst_sum_smul_X hXr, smul_add,
      Finset.sum_add_distrib]

@[simp]
private theorem toPowerSeries_linHom (A : Matrix (Fin h) (Fin g) R) (i : Fin h) :
    (linHom A).toPowerSeries i = ∑ j, A i j • (X j : MvPowerSeries (Fin g) R) :=
  rfl

/-- `linearPart` reads off the matrix, with rows indexed by the target coordinates. -/
private theorem linearPart_linHom (A : Matrix (Fin h) (Fin g) R) :
    linearPart (linHom A).toPowerSeries = A := by
  ext i j
  simp [linearPart, coeff_X, Finsupp.single_left_inj one_ne_zero]

/-- `Hom.id` is the homomorphism of the identity matrix. -/
private theorem id_eq_linHom : Hom.id (addMv g R) = linHom 1 := by
  apply Hom.ext
  funext i
  change (X i : MvPowerSeries (Fin g) R) = ∑ j, (1 : Matrix (Fin g) (Fin g) R) i j • X j
  simp [Matrix.one_apply]

/-- `Hom.comp ψ φ` is `ψ ∘ φ`: it multiplies the matrices in this order. -/
private theorem comp_linHom (A : Matrix (Fin k) (Fin h) R) (B : Matrix (Fin h) (Fin g) R) :
    (linHom A).comp (linHom B) = linHom (A * B) := by
  apply Hom.ext
  funext i
  change subst (linHom B).toPowerSeries (∑ j, A i j • (X j : MvPowerSeries (Fin h) R)) = _
  rw [subst_sum_smul_X (linHom B).hasSubst_toPowerSeries, toPowerSeries_linHom]
  simp only [toPowerSeries_linHom, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

/-- The zero homomorphism is the homomorphism of the zero matrix. -/
private theorem zero_eq_linHom : (0 : Hom (addMv g R) (addMv h R)) = linHom 0 := by
  apply Hom.ext
  funext i
  simp

/-- The sum of homomorphisms into the additive law adds the matrices. -/
private theorem linHom_add (A A' : Matrix (Fin h) (Fin g) R) :
    linHom A + linHom A' = linHom (A + A') := by
  apply Hom.ext
  funext i
  change subst (Sum.elim (linHom A).toPowerSeries (linHom A').toPowerSeries)
      (X (Sum.inl i) + X (Sum.inr i)) = _
  rw [subst_X_add_X (by rintro (j | j) <;> exact Hom.constantCoeff_eq_zero _ j)]
  simp [Matrix.add_apply, add_smul, Finset.sum_add_distrib]

/-- The homomorphisms into a commutative law form an additive commutative monoid. -/
example : AddCommMonoid (Hom (addMv g R) (addMv h R)) := inferInstance

example (A : Matrix (Fin h) (Fin g) R) : 2 • linHom A = linHom (2 • A) := by
  rw [two_nsmul, linHom_add, two_nsmul]

/-- Composition and sums together: `(A + A') * B`. -/
example (A A' : Matrix (Fin k) (Fin h) R) (B : Matrix (Fin h) (Fin g) R) :
    linearPart ((linHom A + linHom A').comp (linHom B)).toPowerSeries = (A + A') * B := by
  rw [linHom_add, comp_linHom, linearPart_linHom]

/-- `comp_linHom` pins the order of the factors: swapping them changes the composite. -/
example : (linHom (R := ℤ) !![1, 1; 0, 1]).comp (linHom !![1, 0; 1, 1]) ≠
    linHom (!![1, 0; 1, 1] * !![1, 1; 0, 1]) := by
  rw [comp_linHom]
  intro hc
  have := congrFun (congrFun (congrArg (fun φ => linearPart (Hom.toPowerSeries φ)) hc) 0) 0
  simp [linearPart_linHom] at this

end Hom

/-! ### Endomorphisms of the additive formal group law -/

section End

open MvFormalGroup

variable {g : ℕ} {R : Type*} [CommRing R]

/-- The endomorphisms of a commutative formal group law form a semiring. -/
example (F : MvFormalGroup g R) [F.IsComm] : Semiring (End F) := inferInstance

/-- The endomorphism of the additive formal group law given by a square matrix. -/
private abbrev linEnd (A : Matrix (Fin g) (Fin g) R) : End (addMv g R) := linHom A

/-- Multiplication in `End` is composition `φ * ψ = φ ∘ ψ`: it multiplies the matrices in this
order. -/
private theorem linEnd_mul (A B : Matrix (Fin g) (Fin g) R) :
    linEnd A * linEnd B = linEnd (A * B) :=
  comp_linHom A B

private theorem linEnd_add (A B : Matrix (Fin g) (Fin g) R) :
    linEnd A + linEnd B = linEnd (A + B) :=
  linHom_add A B

private theorem linEnd_one : (1 : End (addMv g R)) = linEnd 1 :=
  id_eq_linHom

/-- In `End (addMv g R)`, the natural number `n` is `n` times the identity matrix. -/
private theorem natCast_eq_linEnd (n : ℕ) :
    (n : End (addMv g R)) = linEnd (n : Matrix (Fin g) (Fin g) R) := by
  apply Hom.ext
  funext i
  rw [End.toPowerSeries_natCast, nthSeries_addMv, toPowerSeries_linHom]
  simp [Matrix.natCast_apply, Nat.cast_smul_eq_nsmul]

/-- The semiring operations of `End` match those of matrices on a polynomial expression. -/
example (A B : Matrix (Fin g) (Fin g) R) :
    linEnd A * (linEnd B + 2) = linEnd (A * (B + 2)) := by
  rw [show (2 : End (addMv g R)) = ((2 : ℕ) : End (addMv g R)) by norm_cast,
    natCast_eq_linEnd, linEnd_add, linEnd_mul]
  norm_cast

/-- `linearPartHom` sends `linEnd A` to `A`. -/
private theorem linearPartHom_linEnd (A : Matrix (Fin g) (Fin g) R) :
    linearPartHom (addMv g R) (linEnd A) = A :=
  linearPart_linHom A

example (A B : Matrix (Fin g) (Fin g) R) :
    linearPartHom (addMv g R) (linEnd A * linEnd B + 3) = A * B + 3 := by
  rw [map_add, map_mul, map_ofNat, linearPartHom_linEnd, linearPartHom_linEnd]

/-- `End (addMv 2 ℤ)` is not commutative: the order of the factors matters. -/
example : linEnd (R := ℤ) !![1, 1; 0, 1] * linEnd !![1, 0; 1, 1] ≠
    linEnd !![1, 0; 1, 1] * linEnd !![1, 1; 0, 1] := by
  intro hc
  have h := congrArg (linearPartHom (addMv 2 ℤ)) hc
  simp only [map_mul, linearPartHom_linEnd] at h
  have := congrFun (congrFun h 0) 0
  simp at this

end End

end MetaMathlibExt
