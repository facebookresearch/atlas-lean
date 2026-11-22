/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CerednikDrinfeld_CartierStructureConstants.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source file at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.RingTheory.WittVector.GradedCartierModuleData
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.RingTheory.WittVector.Domain
import Mathlib.RingTheory.WittVector.Identities

/-!
# Lifts of structure constants

The lift ring of two elements `u v` of a ring `B` over a coefficient ring
`R` is the polynomial ring in variables indexed by `B`, modulo the relation
`X u * X v = p`. Structure constants valued in `B` lift to this ring, and a
homomorphism out of it is determined by a factorization of `p` in `B`.
-/

@[expose] public section

universe u v

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommRing R]

private theorem eq_zero_of_C_mul_eq_zero {π : R}
    (hπ : ∀ r : R, π * r = 0 → r = 0) {g : MvPolynomial σ R}
    (h : C π * g = 0) : g = 0 := by
  ext e
  have he := congrArg (fun g : MvPolynomial σ R => g.coeff e) h
  rw [coeff_C_mul, MvPolynomial.coeff_zero] at he
  rw [MvPolynomial.coeff_zero]
  exact hπ _ he

private theorem exists_eq_C_mul_of_forall_dvd_coeff {π : R}
    {q : MvPolynomial σ R} (h : ∀ e, π ∣ q.coeff e) :
    ∃ q₁ : MvPolynomial σ R, q = C π * q₁ := by
  classical
  choose c hc using h
  refine ⟨∑ e ∈ q.support, monomial e (c e), ?_⟩
  rw [Finset.mul_sum]
  conv_lhs => rw [as_sum q]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [C_mul_monomial, ← hc e]

private theorem mem_span_of_C_mul_mem_span_X_mul_X_sub_C {π : R}
    (hπ : ∀ r : R, π * r = 0 → r = 0) (u v : σ) {g : MvPolynomial σ R}
    (h : C π * g ∈ Ideal.span {(X u * X v - C π : MvPolynomial σ R)}) :
    g ∈ Ideal.span {(X u * X v - C π : MvPolynomial σ R)} := by
  classical
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp h
  have hXq : q * X u * X v = C π * (g + q) := by
    have h1 : q * (X u * X v - C π) = C π * g := hq
    linear_combination h1
  have hdvd : ∀ e, π ∣ q.coeff e := by
    intro e
    have hc := congrArg
      (fun r : MvPolynomial σ R => r.coeff (e + Finsupp.single u 1 + Finsupp.single v 1)) hXq
    rw [coeff_mul_X, coeff_mul_X, coeff_C_mul] at hc
    exact ⟨_, hc⟩
  obtain ⟨q₁, rfl⟩ := exists_eq_C_mul_of_forall_dvd_coeff hdvd
  have hcancel : g + C π * q₁ = q₁ * X u * X v := by
    have h0 : C π * (g + C π * q₁ - q₁ * X u * X v) = 0 := by
      have h2 := hXq
      linear_combination (-1 : MvPolynomial σ R) * h2
    have h3 := eq_zero_of_C_mul_eq_zero hπ h0
    linear_combination h3
  refine Ideal.mem_span_singleton'.mpr ⟨q₁, ?_⟩
  linear_combination (-1 : MvPolynomial σ R) * hcancel

end MvPolynomial

namespace CerednikDrinfeld

namespace CartierLift

open MvPolynomial

variable (p : ℕ) (R : Type v) [CommRing R] {B : Type u}

/-- The defining relation of the lift ring: `X u * X v = p`. -/
noncomputable def liftRel (u v : B) : MvPolynomial B R :=
  X u * X v - C (p : R)

/-- The lift ring of `u` and `v`: polynomials modulo `X u * X v = p`. -/
abbrev LiftRing (u v : B) : Type (max u v) :=
  MvPolynomial B R ⧸ Ideal.span {liftRel p R u v}

variable {p R}

/-- The image of the variable `X b` in the lift ring. -/
noncomputable def liftVar (u v : B) (b : B) : LiftRing p R u v :=
  Ideal.Quotient.mk _ (X b)

theorem liftVar_mul_liftVar (u v : B) :
    liftVar (p := p) (R := R) u v u * liftVar (p := p) (R := R) u v v = p := by
  rw [liftVar, liftVar, ← map_mul,
    ← map_natCast (Ideal.Quotient.mk (Ideal.span {liftRel p R u v})),
    ← MvPolynomial.C_eq_coe_nat]
  refine (Ideal.Quotient.eq).mpr (Ideal.subset_span ?_)
  simp [liftRel]

/-- The homomorphism from the lift ring determined by a factorization
`u * v = p` in `B`. -/
noncomputable def liftHom [CommRing B] (j : R →+* B) (u v : B) (huv : u * v = p) :
    LiftRing p R u v →+* B :=
  Ideal.Quotient.lift _ (eval₂Hom j id) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, liftRel, map_sub, map_mul, eval₂Hom_X', eval₂Hom_X',
      eval₂Hom_C, map_natCast, id, id, huv, sub_self, mul_zero])

@[simp] theorem liftHom_liftVar [CommRing B] (j : R →+* B) (u v : B)
    (huv : u * v = p) (b : B) :
    liftHom j u v huv (liftVar u v b) = b := by
  rw [liftHom, liftVar, Ideal.Quotient.lift_mk, eval₂Hom_X']
  rfl

theorem liftHom_mk_C [CommRing B] (j : R →+* B) (u v : B) (huv : u * v = p)
    (r : R) :
    liftHom j u v huv (Ideal.Quotient.mk _ (C r)) = j r := by
  rw [liftHom, Ideal.Quotient.lift_mk, eval₂Hom_C]

theorem liftHom_comp_algebraMap [CommRing B] (j : R →+* B) (u v : B)
    (huv : u * v = p) :
    (liftHom j u v huv).comp (algebraMap R (LiftRing p R u v)) = j :=
  RingHom.ext fun r => liftHom_mk_C j u v huv r

theorem liftHom_surjective [CommRing B] (j : R →+* B) (u v : B)
    (huv : u * v = p) :
    Function.Surjective (liftHom j u v huv) :=
  fun b => ⟨liftVar u v b, liftHom_liftVar j u v huv b⟩

/-- Multiplication by `p` is injective in the lift ring when it is
injective on coefficients. -/
theorem natCast_mul_eq_zero (hR : ∀ r : R, (p : R) * r = 0 → r = 0)
    (u v : B) (x : LiftRing p R u v) (hx : (p : LiftRing p R u v) * x = 0) :
    x = 0 := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.eq_zero_iff_mem]
  refine MvPolynomial.mem_span_of_C_mul_mem_span_X_mul_X_sub_C hR u v ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, MvPolynomial.C_eq_coe_nat,
    map_natCast]
  exact hx

/-- The lift of the structure constant `a m i` to the lift ring of the
first two constants. -/
noncomputable def liftConstants (a : ℕ → Fin 2 → B) (m : ℕ) (i : Fin 2) :
    LiftRing p R (a 0 0) (a 0 1) :=
  liftVar (a 0 0) (a 0 1) (a m i)

@[simp] theorem liftHom_liftConstants [CommRing B] (j : R →+* B)
    (a : ℕ → Fin 2 → B) (h : a 0 0 * a 0 1 = p) (m : ℕ) (i : Fin 2) :
    liftHom j (a 0 0) (a 0 1) h (liftConstants (p := p) a m i) = a m i :=
  liftHom_liftVar j _ _ h _

theorem liftConstants_zero_zero_mul (a : ℕ → Fin 2 → B) :
    liftConstants (p := p) (R := R) a 0 0 *
      liftConstants (p := p) (R := R) a 0 1 = p :=
  liftVar_mul_liftVar _ _

/-- Multiplication by `p` is injective on the Witt vectors over the field
with `p ^ 2` elements. -/
theorem zp2_natCast_mul_eq_zero [Fact p.Prime] (r : Zp2 p)
    (h : (p : Zp2 p) * r = 0) : r = 0 := by
  rcases mul_eq_zero.mp h with h0 | h0
  · exact absurd h0 (WittVector.p_nonzero p (GaloisField p 2))
  · exact h0

/-- Multiplication by `p` is injective in the lift ring over `Zp2`. -/
theorem natCast_mul_eq_zero_zp2 [Fact p.Prime] (u v : B)
    (x : LiftRing p (Zp2 p) u v) (hx : (p : LiftRing p (Zp2 p) u v) * x = 0) :
    x = 0 :=
  natCast_mul_eq_zero (zp2_natCast_mul_eq_zero (p := p)) u v x hx

end CartierLift

end CerednikDrinfeld
