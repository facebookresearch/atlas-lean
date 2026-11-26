/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.SpecialFormalFunctor

import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public noncomputable section

namespace SpecialFormalFunctorTest

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

variable (p : ℕ) [Fact p.Prime]

/-- Consumer with the original binders for the functor of points `G`. -/
theorem exactSource {𝒪 : Type} [CommRing 𝒪] {O : Type} [CommRing O] [Algebra 𝒪 O]
    (M : ModuliPackage.{0, 0} p O) (B : Type) [CommRing B] [Algebra 𝒪 B] :
    (ModuliPackage.G 𝒪 M).obj B = ModuliPackage.GPoint 𝒪 M B :=
  ModuliPackage.G_obj 𝒪 M B

/-- The identity map on points is the identity, with the original binders. -/
theorem exactSourceMapId {𝒪 : Type} [CommRing 𝒪] {O : Type} [CommRing O]
    [Algebra 𝒪 O] (M : ModuliPackage.{0, 0} p O) {B : Type} [CommRing B]
    [Algebra 𝒪 B] (x : ModuliPackage.GPoint 𝒪 M B) :
    x.map (AlgHom.id 𝒪 B) = x :=
  x.map_id

/-- Non-vacuity: over any ring of characteristic `p`, the standard special formal
`O_D`-module exists; its Lie algebra is the direct sum of the two eigenlines of `Zp2 p`, and
it has height `4`. -/
example {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B) :
    IsCompl ((SpecialFormalODModule.standard j).lieZero j)
        ((SpecialFormalODModule.standard j).lieOne j) ∧
      (SpecialFormalODModule.standard j).HasHeight 4 :=
  ⟨(SpecialFormalODModule.standard j).isSpecial.1, (SpecialFormalODModule.standard j).hasHeight⟩

/-- The two eigenlines of the standard module are the coordinate axes of its Lie algebra
`Fin 2 → B`: `Zp2 p` acts on the first coordinate through `j` and on the second through `j`
composed with Frobenius, so each basis vector lies in exactly one of them. -/
example {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B) :
    (Pi.single 0 1 : Fin 2 → B) ∈ (SpecialFormalODModule.standard j).lieZero j ∧
      (Pi.single 0 1 : Fin 2 → B) ∉ (SpecialFormalODModule.standard j).lieOne j ∧
      (Pi.single 1 1 : Fin 2 → B) ∈ (SpecialFormalODModule.standard j).lieOne j ∧
      (Pi.single 1 1 : Fin 2 → B) ∉ (SpecialFormalODModule.standard j).lieZero j := by
  have : Nontrivial B := CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).ne_one
  rw [SpecialFormalODModule.standard_toFormalODModule, Standard.mem_lieZero_iff,
    Standard.mem_lieOne_iff, Standard.mem_lieOne_iff, Standard.mem_lieZero_iff]
  simp

/-- In characteristic `p`, multiplication by `p` on the standard module is
`X i ↦ X i ^ (p ^ 2)`, whose kernel has degree `p ^ 4` (height `4`). -/
example {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B) :
    (SpecialFormalODModule.standard j).act (p : Zp2 p) =
      fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ (p ^ 2) := by
  have h := Standard.modB_act_p j
  rw [LubinTate.card_GF] at h
  exact h

/-- Over `𝔽_{p²}`, with `j` the reduction map `W(𝔽_{p²}) → 𝔽_{p²}`, the Lie algebra of the
standard module is two-dimensional and both eigenlines are one-dimensional. -/
example :
    Module.finrank (GaloisField p 2) (SpecialFormalODModule.standard
        (WittVector.constantCoeff : Zp2 p →+* GaloisField p 2)).Lie = 2 ∧
      Module.finrank (GaloisField p 2) ((SpecialFormalODModule.standard
        (WittVector.constantCoeff : Zp2 p →+* GaloisField p 2)).lieZero
          WittVector.constantCoeff) = 1 ∧
      Module.finrank (GaloisField p 2) ((SpecialFormalODModule.standard
        (WittVector.constantCoeff : Zp2 p →+* GaloisField p 2)).lieOne
          WittVector.constantCoeff) = 1 :=
  ⟨Module.finrank_fin_fun _, (Standard.lieZeroEquiv _).finrank_eq.trans (Module.finrank_self _),
    (Standard.lieOneEquiv _).finrank_eq.trans (Module.finrank_self _)⟩

end SpecialFormalFunctorTest

/-! ### Homomorphisms and endomorphisms of additive formal group laws

A matrix `A` gives a homomorphism `linHom A` of additive formal group laws. `Hom.id`, `Hom.comp`,
the zero homomorphism and the sum of homomorphisms act on these as the identity matrix, the matrix
product (in this order), the zero matrix and the matrix sum, and `linearPart` recovers `A`. On
the endomorphisms `linEnd A` the semiring `End (addMv g R)` and `linearPartHom` agree with matrix
arithmetic. -/

namespace SpecialFormalFunctorTest.HomEnd

open MvPowerSeries MvFormalGroup

section AddMv

variable {g : ℕ} {R : Type*} [CommRing R]

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

section Hom

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

end Hom

section End

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

end SpecialFormalFunctorTest.HomEnd

end
