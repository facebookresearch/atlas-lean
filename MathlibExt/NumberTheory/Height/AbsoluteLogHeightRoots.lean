/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import MathlibExt.NumberTheory.Height.Absolute

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.GaussNorm

@[expose] public section

namespace MathlibExt.NumberTheory.Height.AbsoluteWanted

open Polynomial

/-!
# Absolute logarithmic height via Mahler measure of a primitive integral minpoly

Private helpers proving `absLogHeight₁_eq_log_leadingCoeff_add_sum_log_roots`.
-/

-- Gauss norm of a primitive integral polynomial is 1.
private theorem alh_gaussNorm_map_intCast_eq_one_of_isPrimitive
    {R : Type*} [Field R] (v : AbsoluteValue R ℝ)
    (hna : IsNonarchimedean v) (q : ℤ[X]) (hq : q.IsPrimitive) :
    (q.map (Int.castRingHom R)).gaussNorm v 1 = 1 := by
  have hcast : ∀ n : ℤ, v (n : R) ≤ 1 :=
    fun n => hna.apply_intCast_le_one (map_zero_le v 1) (map_one v)
      (map_neg_eq_map v)
  have hle : (q.map (Int.castRingHom R)).gaussNorm v 1 ≤ 1 := by
    obtain ⟨i, hi⟩ := Polynomial.exists_eq_gaussNorm v 1 (q.map (Int.castRingHom R))
    rw [hi, one_pow, mul_one, Polynomial.coeff_map]
    exact hcast _
  have hne : q.support.Nonempty := by
    rw [Polynomial.support_nonempty]
    exact hq.ne_zero
  have hge : 1 ≤ (q.map (Int.castRingHom R)).gaussNorm v 1 := by
    have hcont : q.support.gcd q.coeff = 1 :=
      Polynomial.isPrimitive_iff_content_eq_one.mp hq
    obtain ⟨f, hf⟩ := Finset.gcd_eq_sum_mul q.support q.coeff
    have hsum : (∑ a ∈ q.support, q.coeff a * f a) = 1 := by
      rw [← hf, hcont]
    have h1eq : ((1 : ℤ) : R)
        = ∑ a ∈ q.support, ((q.coeff a * f a : ℤ) : R) := by
      rw [← hsum, Int.cast_sum]
    have hval : (1 : ℝ)
        = v (∑ a ∈ q.support, ((q.coeff a * f a : ℤ) : R)) := by
      rw [← h1eq, Int.cast_one, map_one]
    have hsup := hna.apply_sum_le_sup (s := q.support)
      (g := fun a => ((q.coeff a * f a : ℤ) : R)) hne
    have hsup_le : q.support.sup' hne
        (fun a => v ((q.coeff a * f a : ℤ) : R))
        ≤ (q.map (Int.castRingHom R)).gaussNorm v 1 := by
      rw [Finset.sup'_le_iff]
      intro a _
      rw [Int.cast_mul, map_mul]
      have hcoeff : v ((q.map (Int.castRingHom R)).coeff a)
          = v ((q.coeff a : ℤ) : R) := by
        rw [Polynomial.coeff_map]
        rfl
      have hgauss := (q.map (Int.castRingHom R)).le_gaussNorm v zero_le_one a
      rw [one_pow, mul_one, hcoeff] at hgauss
      calc v ((q.coeff a : ℤ) : R) * v ((f a : ℤ) : R)
          ≤ v ((q.coeff a : ℤ) : R) * 1 :=
            mul_le_mul_of_nonneg_left (hcast _) (AbsoluteValue.nonneg v _)
        _ = v ((q.coeff a : ℤ) : R) := mul_one _
        _ ≤ (q.map (Int.castRingHom R)).gaussNorm v 1 := hgauss
    exact hval.trans_le (hsup.trans hsup_le)
  exact le_antisymm hle hge

-- Auxiliary. Gauss norm of a single linear factor.
private theorem alh_gaussNorm_X_sub_C
    {R : Type*} [Field R] (v : AbsoluteValue R ℝ) (β : R) :
    (X - C β : R[X]).gaussNorm v 1 = max (v β) 1 := by
  have h0 : (X - C β : R[X]).coeff 0 = -β := by simp
  have h1 : (X - C β : R[X]).coeff 1 = 1 := by simp
  have hge : max (v β) 1 ≤ (X - C β : R[X]).gaussNorm v 1 := by
    apply max_le
    · have h := (X - C β : R[X]).le_gaussNorm v zero_le_one 0
      rw [one_pow, mul_one, h0, map_neg_eq_map] at h
      exact h
    · have h := (X - C β : R[X]).le_gaussNorm v zero_le_one 1
      rw [one_pow, mul_one, h1, map_one] at h
      exact h
  have hle : (X - C β : R[X]).gaussNorm v 1 ≤ max (v β) 1 := by
    obtain ⟨i, hi⟩ := Polynomial.exists_eq_gaussNorm v 1 (X - C β : R[X])
    rw [hi, one_pow, mul_one]
    by_cases hi0 : i = 0
    · subst hi0
      rw [h0, map_neg_eq_map]
      exact le_max_left _ _
    · by_cases hi1 : i = 1
      · subst hi1
        rw [h1, map_one]
        exact le_max_right _ _
      · have h1i : (1 : ℕ) ≠ i := fun h => hi1 h.symm
        have hcoeff : (X - C β : R[X]).coeff i = 0 := by
          simp [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C,
            hi0, h1i]
        rw [hcoeff, map_zero]
        exact (zero_le_one).trans (le_max_right _ _)
  exact le_antisymm hle hge

-- Gauss norm of a split linear-factor product.
private theorem alh_gaussNorm_C_mul_prod_X_sub_C
    {R : Type*} [Field R] (v : AbsoluteValue R ℝ)
    (hna : IsNonarchimedean v) (c : R) (s : Multiset R) :
    (C c * (s.map fun β => X - C β).prod).gaussNorm v 1
      = v c * (s.map fun β => max (v β) 1).prod := by
  induction s using Multiset.induction with
  | empty =>
    simp [Multiset.map_zero, Multiset.prod_zero]
  | cons b s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons,
      Multiset.prod_cons, mul_left_comm,
      Polynomial.gaussNorm_mul hna one_pos, ih,
      alh_gaussNorm_X_sub_C v b]
    ring

-- Local Gauss-norm identity for a primitive polynomial that splits.
private theorem alh_abs_leadingCoeff_mul_prod_max_roots_eq_one
    {R : Type*} [Field R] [CharZero R] (v : AbsoluteValue R ℝ)
    (hna : IsNonarchimedean v) (q : ℤ[X]) (hq : q.IsPrimitive)
    (hsplit : (q.map (Int.castRingHom R)).roots.card
      = (q.map (Int.castRingHom R)).natDegree) :
    v (q.leadingCoeff : R) *
      (((q.map (Int.castRingHom R)).roots.map fun β => max (v β) 1).prod) = 1 := by
  have hfactor :=
    Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hsplit
  have hlc : (q.map (Int.castRingHom R)).leadingCoeff = ((q.leadingCoeff : ℤ) : R) :=
    Polynomial.leadingCoeff_map_of_injective
      (RingHom.injective_int (Int.castRingHom R)) _
  have hgauss := congrArg (Polynomial.gaussNorm v 1) hfactor
  rw [alh_gaussNorm_C_mul_prod_X_sub_C v hna _ _, hlc,
    alh_gaussNorm_map_intCast_eq_one_of_isPrimitive v hna q hq] at hgauss
  exact hgauss

-- Finite multiplicative support of the max-with-one functions.
private theorem alh_hasFiniteMulSupport_max_finitePlace
    {E : Type*} [Field E] [NumberField E] (β : E) :
    (fun v : NumberField.FinitePlace E => max (v β) 1).HasFiniteMulSupport := by
  by_cases hβ : β = 0
  · subst hβ
    have heq : (fun v : NumberField.FinitePlace E => max (v (0 : E)) 1) = 1 := by
      funext v
      simp
    rw [heq]
    exact Function.hasFiniteMulSupport_fun_one
  · exact Function.HasFiniteMulSupport.max
      (NumberField.FinitePlace.hasFiniteMulSupport hβ)
      Function.hasFiniteMulSupport_fun_one

private theorem alh_hasFiniteMulSupport_prod_max_finitePlace
    {E : Type*} [Field E] [NumberField E] (s : Multiset E) :
    (fun v : NumberField.FinitePlace E =>
      (s.map fun β => max (v β) 1).prod).HasFiniteMulSupport := by
  induction s using Multiset.induction with
  | empty =>
    simpa only [Multiset.map_zero, Multiset.prod_zero, Pi.one_def] using
      Function.hasFiniteMulSupport_fun_one
        (α := NumberField.FinitePlace E) (M := ℝ)
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact Function.HasFiniteMulSupport.mul
      (alh_hasFiniteMulSupport_max_finitePlace a) ih

-- Auxiliary. The supremum over `Fin 2` is a max.
private theorem alh_iSup_fin_two (f : Fin 2 → ℝ) :
    (⨆ i, f i) = max (f 0) (f 1) := by
  apply le_antisymm
  · apply ciSup_le
    intro i
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  · apply max_le
    · exact le_ciSup (Set.finite_range f).bddAbove 0
    · exact le_ciSup (Set.finite_range f).bddAbove 1

-- Ideal norm times the finite part equals the denominator power.
private theorem alh_absNorm_span_mul_finprod_max_eq_pow
    {E : Type*} [Field E] [NumberField E] (β : E) (n : ℕ) (hn : n ≠ 0)
    (b : NumberField.RingOfIntegers E) (h : (n : E) * β = (b : E)) :
    ((Ideal.span ({(n : NumberField.RingOfIntegers E), b} : Set _)).absNorm : ℝ) *
      ∏ᶠ v : NumberField.FinitePlace E, max (v β) 1
      = (n : ℝ) ^ Module.finrank ℚ E := by
  have hnE : (n : E) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hnO : ((n : ℕ) : NumberField.RingOfIntegers E) ≠ 0 :=
    Nat.cast_ne_zero.mpr hn
  have htuple_ne : (![b, ((n : ℕ) : NumberField.RingOfIntegers E)] :
      Fin 2 → NumberField.RingOfIntegers E) ≠ 0 := by
    intro hcon
    apply hnO
    have h1 := congrFun hcon 1
    simpa using h1
  have hspan : Ideal.span
      (Set.range ![b, ((n : ℕ) : NumberField.RingOfIntegers E)])
      = Ideal.span ({((n : ℕ) : NumberField.RingOfIntegers E), b} : Set _) := by
    congr 1
    ext y
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    · rintro (rfl | rfl)
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
  have key := NumberField.absNorm_mul_finprod_finitePlace_eq_one htuple_ne
  rw [hspan] at key
  have hiSup : ∀ w : NumberField.FinitePlace E,
      (⨆ i : Fin 2, w (((![b, ((n : ℕ) : NumberField.RingOfIntegers E)] i :
        NumberField.RingOfIntegers E)) : E))
        = w (n : E) * max (w β) 1 := by
    intro w
    have e0 : (((![b, ((n : ℕ) : NumberField.RingOfIntegers E)] 0 :
        NumberField.RingOfIntegers E)) : E) = (b : E) := by
      simp [Matrix.cons_val_zero]
    have e1 : (((![b, ((n : ℕ) : NumberField.RingOfIntegers E)] 1 :
        NumberField.RingOfIntegers E)) : E) = (n : E) := by
      simp
    have hpos : 0 < w (n : E) :=
      NumberField.FinitePlace.pos_iff.mpr hnE
    have h2 := alh_iSup_fin_two (fun i => w (((![b, ((n : ℕ) :
      NumberField.RingOfIntegers E)] i : NumberField.RingOfIntegers E)) : E))
    rw [h2, e0, e1, ← h, map_mul, mul_max_of_nonneg _ _ hpos.le, mul_one]
  have hsplit : (∏ᶠ w : NumberField.FinitePlace E, (⨆ i : Fin 2,
      w (((![b, ((n : ℕ) : NumberField.RingOfIntegers E)] i :
        NumberField.RingOfIntegers E)) : E)))
      = (∏ᶠ w : NumberField.FinitePlace E, w (n : E)) *
        (∏ᶠ w : NumberField.FinitePlace E, max (w β) 1) := by
    have e := finprod_congr hiSup
    rw [e]
    exact finprod_mul_distrib
      (NumberField.FinitePlace.hasFiniteMulSupport hnE)
      (alh_hasFiniteMulSupport_max_finitePlace β)
  rw [hsplit] at key
  have hP : (∏ᶠ w : NumberField.FinitePlace E, w (n : E)) *
      ((n : ℝ) ^ Module.finrank ℚ E) = 1 := by
    have h2 : (n : E) = algebraMap ℚ E ((n : ℕ) : ℚ) := (map_natCast _ _).symm
    have hP0 := NumberField.FinitePlace.prod_eq_inv_abs_norm hnE
    rw [h2, Algebra.norm_algebraMap, Rat.cast_inv, Rat.cast_abs, Rat.cast_pow,
      Rat.cast_natCast,
      abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)] at hP0
    rw [← h2] at hP0
    rw [hP0, inv_mul_cancel₀ (pow_ne_zero _ (by exact_mod_cast hn))]
  have hND : ((Ideal.span ({(n : NumberField.RingOfIntegers E), b} :
      Set _)).absNorm : ℝ) *
      ∏ᶠ v : NumberField.FinitePlace E, max (v β) 1
      = (((Ideal.span ({(n : NumberField.RingOfIntegers E), b} : Set _)).absNorm :
        ℝ) * ((∏ᶠ w : NumberField.FinitePlace E, w (n : E)) *
        (∏ᶠ w : NumberField.FinitePlace E, max (w β) 1))) *
        ((n : ℝ) ^ Module.finrank ℚ E) := by
    have h2 : (((Ideal.span ({(n : NumberField.RingOfIntegers E), b} : Set _)).absNorm :
        ℝ) * ((∏ᶠ w : NumberField.FinitePlace E, w (n : E)) *
        (∏ᶠ w : NumberField.FinitePlace E, max (w β) 1))) *
        ((n : ℝ) ^ Module.finrank ℚ E)
        = (((Ideal.span ({(n : NumberField.RingOfIntegers E), b} : Set _)).absNorm :
          ℝ) * (∏ᶠ w : NumberField.FinitePlace E, max (w β) 1)) *
          ((∏ᶠ w : NumberField.FinitePlace E, w (n : E)) *
            ((n : ℝ) ^ Module.finrank ℚ E)) := by
      ring
    rw [h2, hP, mul_one]
  rw [hND, key, one_mul]

private theorem alh_finprod_max_algebraMap_eq_pow
    {E L : Type*} [Field E] [Field L] [NumberField E] [NumberField L]
    [Algebra E L] (β : E) :
    ∏ᶠ w : NumberField.FinitePlace L, max (w (algebraMap E L β)) 1
      = (∏ᶠ v : NumberField.FinitePlace E, max (v β) 1) ^ Module.finrank E L := by
  obtain ⟨n, hn, b, hnb, -⟩ :=
    NumberField.exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow β
  have hcoe : ∀ y : NumberField.RingOfIntegers E,
      algebraMap E L (y : E)
        = ((algebraMap (NumberField.RingOfIntegers E)
          (NumberField.RingOfIntegers L) y : NumberField.RingOfIntegers L) : L) := by
    intro y
    rw [show algebraMap (NumberField.RingOfIntegers E)
        (NumberField.RingOfIntegers L) y
        = NumberField.RingOfIntegers.mapRingHom (algebraMap E L) y from rfl]
    exact (NumberField.RingOfIntegers.mapRingHom_apply _ _).symm
  have hL : (n : L) * algebraMap E L β
      = ((algebraMap (NumberField.RingOfIntegers E)
        (NumberField.RingOfIntegers L) b : NumberField.RingOfIntegers L) : L) := by
    have h2 := congrArg (algebraMap E L) hnb
    rwa [map_mul, map_natCast, hcoe] at h2
  have hE := alh_absNorm_span_mul_finprod_max_eq_pow β n hn b hnb
  have hL2 := alh_absNorm_span_mul_finprod_max_eq_pow (algebraMap E L β) n hn _ hL
  have hIdeal : Ideal.span ({((n : ℕ) : NumberField.RingOfIntegers L),
      algebraMap (NumberField.RingOfIntegers E)
        (NumberField.RingOfIntegers L) b} : Set (NumberField.RingOfIntegers L))
      = Ideal.map (algebraMap (NumberField.RingOfIntegers E)
        (NumberField.RingOfIntegers L))
        (Ideal.span ({((n : ℕ) : NumberField.RingOfIntegers E), b} :
          Set (NumberField.RingOfIntegers E))) := by
    rw [Ideal.map_span]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨_, Or.inl rfl, by rw [map_natCast]⟩
      · exact ⟨_, Or.inr rfl, rfl⟩
    · rintro ⟨z, (rfl | rfl), rfl⟩
      · exact Or.inl (by rw [map_natCast])
      · exact Or.inr rfl
  have hnorm := Ideal.absNorm_algebraMap (NumberField.RingOfIntegers E)
    (NumberField.RingOfIntegers L)
    (Ideal.span ({((n : ℕ) : NumberField.RingOfIntegers E), b} :
      Set (NumberField.RingOfIntegers E)))
  have hfr : Module.finrank E L
      = Module.finrank (NumberField.RingOfIntegers E)
        (NumberField.RingOfIntegers L) :=
    IsFractionRing.finrank_eq _ _ _ _
  have hmul : Module.finrank ℚ E * Module.finrank E L = Module.finrank ℚ L :=
    Module.finrank_mul_finrank _ _ _
  have hNE : (Ideal.span ({((n : ℕ) : NumberField.RingOfIntegers E), b} :
      Set (NumberField.RingOfIntegers E))).absNorm ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff]
    intro hbot
    have hmem := Ideal.subset_span (s := ({((n : ℕ) : NumberField.RingOfIntegers E), b} :
      Set (NumberField.RingOfIntegers E)))
      (by simp : ((n : ℕ) : NumberField.RingOfIntegers E) ∈ _)
    rw [hbot] at hmem
    exact hn (by simpa using hmem)
  rw [hIdeal, hnorm] at hL2
  rw [Nat.cast_pow] at hL2
  rw [← hfr] at hL2
  have hEpow := congrArg (· ^ Module.finrank E L) hE
  rw [mul_pow, ← pow_mul, hmul] at hEpow
  have hcancel : (((Ideal.span ({((n : ℕ) : NumberField.RingOfIntegers E), b} :
      Set (NumberField.RingOfIntegers E))).absNorm : ℕ) : ℝ) ^ Module.finrank E L *
      (∏ᶠ w : NumberField.FinitePlace L, max (w (algebraMap E L β)) 1)
      = (((Ideal.span ({((n : ℕ) : NumberField.RingOfIntegers E), b} :
      Set (NumberField.RingOfIntegers E))).absNorm : ℕ) : ℝ) ^ Module.finrank E L *
      ((∏ᶠ v : NumberField.FinitePlace E, max (v β) 1) ^ Module.finrank E L) :=
    hL2.trans hEpow.symm
  have hpos : (((Ideal.span ({((n : ℕ) : NumberField.RingOfIntegers E), b} :
      Set (NumberField.RingOfIntegers E))).absNorm : ℕ) : ℝ) ^ Module.finrank E L
      ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr hNE)
  exact mul_left_cancel₀ hpos hcancel

private theorem alh_finprod_max_ringHom_pow_eq
    {E L : Type*} [Field E] [Field L] [NumberField E] [NumberField L]
    (τ : E →+* L) (β : E) :
    (∏ᶠ w : NumberField.FinitePlace L, max (w (τ β)) 1) ^ Module.finrank ℚ E
      = (∏ᶠ v : NumberField.FinitePlace E, max (v β) 1) ^ Module.finrank ℚ L := by
  let _ := τ.toAlgebra
  have h6 : (∏ᶠ w : NumberField.FinitePlace L, max (w (τ β)) 1)
      = (∏ᶠ v : NumberField.FinitePlace E, max (v β) 1) ^ Module.finrank E L :=
    alh_finprod_max_algebraMap_eq_pow β
  have hmul : Module.finrank ℚ E * Module.finrank E L = Module.finrank ℚ L :=
    Module.finrank_mul_finrank _ _ _
  have hpow := congrArg (· ^ Module.finrank ℚ E) h6
  rwa [← pow_mul, mul_comm (Module.finrank E L) _, hmul] at hpow

-- Auxiliary. Swap a finprod over finite places with a multiset product.
private theorem alh_finprod_prod_max_swap
    {L : Type*} [Field L] [NumberField L] (s : Multiset L) :
    (∏ᶠ w : NumberField.FinitePlace L, ((s.map fun β => max (w β) 1).prod))
    = ((s.map fun β => ∏ᶠ w : NumberField.FinitePlace L, max (w β) 1).prod) := by
  induction s using Multiset.induction with
  | empty =>
    simp [Multiset.map_zero, Multiset.prod_zero]
  | cons b s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [finprod_mul_distrib (alh_hasFiniteMulSupport_max_finitePlace b)
      (alh_hasFiniteMulSupport_prod_max_finitePlace s), ih]

-- Product over roots of the finite parts equals the leading-coefficient power.
private theorem alh_prod_roots_finprod_max_eq_pow
    {L : Type*} [Field L] [NumberField L] (q : ℤ[X]) (hq : q.IsPrimitive)
    (hsplit : (q.map (Int.castRingHom L)).roots.card
      = (q.map (Int.castRingHom L)).natDegree) :
    (((q.map (Int.castRingHom L)).roots.map fun β =>
      ∏ᶠ w : NumberField.FinitePlace L, max (w β) 1).prod)
      = (((|q.leadingCoeff| : ℤ) : ℝ) ^ Module.finrank ℚ L) := by
  have hna : ∀ w : NumberField.FinitePlace L,
      IsNonarchimedean (w.val : AbsoluteValue L ℝ) := by
    intro w
    exact NumberField.FinitePlace.add_le w
  have hlc : q.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hq.ne_zero
  have ha : (((q.leadingCoeff : ℤ)) : L) ≠ 0 := Int.cast_ne_zero.mpr hlc
  have hloc : ∀ w : NumberField.FinitePlace L,
      (w (((q.leadingCoeff : ℤ)) : L)) *
        ((((q.map (Int.castRingHom L)).roots).map fun β => max (w β) 1).prod)
        = 1 := by
    intro w
    have h3 := alh_abs_leadingCoeff_mul_prod_max_roots_eq_one (w.val) (hna w) q hq
      hsplit
    simpa only [← NumberField.FinitePlace.coe_apply] using h3
  have hfin : (∏ᶠ w : NumberField.FinitePlace L, w (((q.leadingCoeff : ℤ)) : L)) *
      (((q.map (Int.castRingHom L)).roots.map fun β =>
        ∏ᶠ w : NumberField.FinitePlace L, max (w β) 1).prod) = 1 := by
    have h1 : (∏ᶠ w : NumberField.FinitePlace L,
        ((w (((q.leadingCoeff : ℤ)) : L)) *
          ((((q.map (Int.castRingHom L)).roots).map fun β => max (w β) 1).prod)))
        = 1 :=
      finprod_eq_one_of_forall_eq_one hloc
    rw [finprod_mul_distrib (NumberField.FinitePlace.hasFiniteMulSupport ha)
      (alh_hasFiniteMulSupport_prod_max_finitePlace _),
      alh_finprod_prod_max_swap] at h1
    exact h1
  have hPa : (∏ᶠ w : NumberField.FinitePlace L, w (((q.leadingCoeff : ℤ)) : L))
      = (((|Algebra.norm ℚ (((q.leadingCoeff : ℤ)) : L)|⁻¹ : ℚ)) : ℝ) :=
    NumberField.FinitePlace.prod_eq_inv_abs_norm ha
  have hnormQ : Algebra.norm ℚ (((q.leadingCoeff : ℤ)) : L)
      = (((q.leadingCoeff : ℤ)) : ℚ) ^ Module.finrank ℚ L := by
    have hcast : (((q.leadingCoeff : ℤ)) : L)
        = algebraMap ℚ L (((q.leadingCoeff : ℤ)) : ℚ) := (map_intCast _ _).symm
    rw [hcast, Algebra.norm_algebraMap]
  have habs : |Algebra.norm ℚ (((q.leadingCoeff : ℤ)) : L)|
      = (((|q.leadingCoeff| : ℤ)) : ℚ) ^ Module.finrank ℚ L := by
    rw [hnormQ, abs_pow, Int.cast_abs]
  have hG := eq_inv_of_mul_eq_one_right hfin
  rw [hPa, Rat.cast_inv, inv_inv, habs, Rat.cast_pow, Rat.cast_intCast] at hG
  exact hG

-- Properties of the primitive integral minpoly.
private theorem alh_primitiveIntMinpoly_map_eq_C_mul_minpoly
    {K : Type*} [Field K] [CharZero K] {x : K} (hx : IsIntegral ℚ x) :
    (NumberField.primitiveIntMinpoly x).map (Int.castRingHom ℚ)
      = C ((NumberField.primitiveIntMinpoly x).leadingCoeff : ℚ) * minpoly ℚ x := by
  have hmin_ne : minpoly ℚ x ≠ 0 := minpoly.ne_zero hx
  have hN_ne :
      IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ x) ≠ 0 := by
    intro hcon
    rw [IsFractionRing.integerNormalization_eq_zero_iff] at hcon
    exact hmin_ne hcon
  have haevalN :
      aeval x (IsLocalization.integerNormalization (nonZeroDivisors ℤ)
        (minpoly ℚ x)) = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero _ _ (minpoly.aeval ℚ x)
  have hcontent_ne :
      (IsLocalization.integerNormalization (nonZeroDivisors ℤ)
        (minpoly ℚ x)).content ≠ 0 :=
    fun hc => hN_ne (Polynomial.content_eq_zero_iff.mp hc)
  have haeval_prim :
      aeval x (IsLocalization.integerNormalization (nonZeroDivisors ℤ)
        (minpoly ℚ x)).primPart = 0 := by
    have hmul := congrArg (aeval x)
      (Polynomial.eq_C_content_mul_primPart
        (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ x)))
    rw [map_mul, Polynomial.aeval_C] at hmul
    rw [haevalN] at hmul
    have hcK : (((IsLocalization.integerNormalization (nonZeroDivisors ℤ)
        (minpoly ℚ x)).content : ℤ)) ≠ 0 :=
      hcontent_ne
    have hcast_ne : ((((IsLocalization.integerNormalization (nonZeroDivisors ℤ)
        (minpoly ℚ x)).content : ℤ)) : K) ≠ 0 :=
      Int.cast_ne_zero.mpr hcK
    have hC : algebraMap ℤ K (IsLocalization.integerNormalization
        (nonZeroDivisors ℤ) (minpoly ℚ x)).content
        = ((((IsLocalization.integerNormalization (nonZeroDivisors ℤ)
        (minpoly ℚ x)).content : ℤ)) : K) := by
      simp
    rw [hC] at hmul
    rcases mul_eq_zero.mp hmul.symm with h | h
    · exact absurd h hcast_ne
    · exact h
  have haeval_map :
      aeval x ((IsLocalization.integerNormalization (nonZeroDivisors ℤ)
        (minpoly ℚ x)).primPart.map (Int.castRingHom ℚ)) = 0 := by
    rw [← algebraMap_int_eq, Polynomial.aeval_map_algebraMap]
    exact haeval_prim
  have hdvd : minpoly ℚ x ∣ (IsLocalization.integerNormalization
      (nonZeroDivisors ℤ) (minpoly ℚ x)).primPart.map (Int.castRingHom ℚ) :=
    minpoly.dvd ℚ x haeval_map
  have hprim : NumberField.primitiveIntMinpoly x
      = (IsLocalization.integerNormalization (nonZeroDivisors ℤ)
        (minpoly ℚ x)).primPart := rfl
  have hdeg : ((IsLocalization.integerNormalization (nonZeroDivisors ℤ)
      (minpoly ℚ x)).primPart.map
      (Int.castRingHom ℚ)).natDegree ≤ (minpoly ℚ x).natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective
      (RingHom.injective_int (Int.castRingHom ℚ)), ← hprim]
    exact le_of_eq (NumberField.primitiveIntMinpoly_natDegree x)
  have hfin := Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic hx) hdvd hdeg
  rw [Polynomial.leadingCoeff_map_of_injective
    (RingHom.injective_int (Int.castRingHom ℚ)), ← hprim] at hfin
  exact hfin

private theorem alh_primitiveIntMinpoly_map_roots_eq_aroots
    {K : Type*} [Field K] [CharZero K] {x : K} (hx : IsIntegral ℚ x)
    (E : Type*) [Field E] [CharZero E] :
    ((NumberField.primitiveIntMinpoly x).map (Int.castRingHom E)).roots
      = (minpoly ℚ x).aroots E := by
  have hmap := alh_primitiveIntMinpoly_map_eq_C_mul_minpoly hx
  have hmapE := congrArg (Polynomial.map (algebraMap ℚ E)) hmap
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map] at hmapE
  have hcomp : (algebraMap ℚ E).comp (Int.castRingHom ℚ) = Int.castRingHom E :=
    Subsingleton.elim _ _
  rw [hcomp] at hmapE
  have hcE : algebraMap ℚ E
      ((NumberField.primitiveIntMinpoly x).leadingCoeff : ℚ) ≠ 0 := by
    rw [map_intCast]
    exact Int.cast_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr
      (NumberField.primitiveIntMinpoly_ne_zero x))
  rw [hmapE, Polynomial.roots_C_mul _ hcE, Polynomial.aroots_def]

private theorem alh_primitiveIntMinpoly_map_roots_nodup
    {K : Type*} [Field K] [CharZero K] {x : K} (hx : IsIntegral ℚ x)
    (E : Type*) [Field E] [CharZero E] :
    ((NumberField.primitiveIntMinpoly x).map (Int.castRingHom E)).roots.Nodup := by
  rw [alh_primitiveIntMinpoly_map_roots_eq_aroots hx E, Polynomial.aroots_def]
  apply Polynomial.nodup_roots
  exact ((minpoly.irreducible hx).separable).map

-- Finite part at the generator equals the absolute leading coefficient.
private theorem alh_finprod_max_gen_eq_abs_leadingCoeff
    {K : Type*} [Field K] [CharZero K] {x : K} (hx : IsIntegral ℚ x)
    [FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ {x})]
    [NumberField ↥(IntermediateField.adjoin ℚ {x})] :
    ∏ᶠ v : NumberField.FinitePlace ↥(IntermediateField.adjoin ℚ {x}),
      max (v (IntermediateField.AdjoinSimple.gen ℚ x)) 1
      = (((|(NumberField.primitiveIntMinpoly x).leadingCoeff| : ℤ)) : ℝ) := by
  have hNFL : NumberField (Polynomial.SplittingField (minpoly ℚ x)) := ⟨⟩
  have hroots : ((NumberField.primitiveIntMinpoly x).map
      (Int.castRingHom (Polynomial.SplittingField (minpoly ℚ x)))).roots
      = (minpoly ℚ x).aroots (Polynomial.SplittingField (minpoly ℚ x)) :=
    alh_primitiveIntMinpoly_map_roots_eq_aroots hx _
  have hspl := Polynomial.SplittingField.splits (minpoly ℚ x)
  have hsplit : ((NumberField.primitiveIntMinpoly x).map
      (Int.castRingHom (Polynomial.SplittingField (minpoly ℚ x)))).roots.card
      = ((NumberField.primitiveIntMinpoly x).map
        (Int.castRingHom (Polynomial.SplittingField (minpoly ℚ x)))).natDegree := by
    rw [hroots, Polynomial.aroots_def, ← hspl.natDegree_eq_card_roots,
      Polynomial.natDegree_map_eq_of_injective
        (FaithfulSMul.algebraMap_injective ℚ _) _,
      Polynomial.natDegree_map_eq_of_injective
        (RingHom.injective_int (Int.castRingHom _)) _,
      NumberField.primitiveIntMinpoly_natDegree]
  have hN8 := alh_prod_roots_finprod_max_eq_pow
    (NumberField.primitiveIntMinpoly x)
    (NumberField.primitiveIntMinpoly_isPrimitive x) hsplit
  have hmem : ∀ β ∈ ((NumberField.primitiveIntMinpoly x).map
      (Int.castRingHom (Polynomial.SplittingField (minpoly ℚ x)))).roots,
      β ∈ (minpoly ℚ x).aroots (Polynomial.SplittingField (minpoly ℚ x)) := by
    intro β hβ
    rw [hroots] at hβ
    exact hβ
  have hN7 : ∀ β ∈ ((NumberField.primitiveIntMinpoly x).map
      (Int.castRingHom (Polynomial.SplittingField (minpoly ℚ x)))).roots,
      ((∏ᶠ w : NumberField.FinitePlace
        (Polynomial.SplittingField (minpoly ℚ x)), max (w β) 1)
        ^ Module.finrank ℚ ↥(IntermediateField.adjoin ℚ {x}))
      = ((∏ᶠ v : NumberField.FinitePlace ↥(IntermediateField.adjoin ℚ {x}),
        max (v (IntermediateField.AdjoinSimple.gen ℚ x)) 1)
        ^ Module.finrank ℚ (Polynomial.SplittingField (minpoly ℚ x))) := by
    intro β hβ
    let σ := (IntermediateField.algHomAdjoinIntegralEquiv ℚ (K := Polynomial.SplittingField
      (minpoly ℚ x)) hx).symm ⟨β, hmem β hβ⟩
    have happly : (σ.toRingHom) (IntermediateField.AdjoinSimple.gen ℚ x) = β :=
      IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hx _
    have hτ := alh_finprod_max_ringHom_pow_eq (E := ↥(IntermediateField.adjoin ℚ {x}))
      (L := Polynomial.SplittingField (minpoly ℚ x))
      σ.toRingHom (IntermediateField.AdjoinSimple.gen ℚ x)
    rwa [happly] at hτ
  have hfinF : Module.finrank ℚ ↥(IntermediateField.adjoin ℚ {x})
      = (minpoly ℚ x).natDegree :=
    IntermediateField.adjoin.finrank hx
  have hcardR : ((NumberField.primitiveIntMinpoly x).map
      (Int.castRingHom (Polynomial.SplittingField (minpoly ℚ x)))).roots.card
      = (minpoly ℚ x).natDegree := by
    rw [hsplit, Polynomial.natDegree_map_eq_of_injective
      (RingHom.injective_int (Int.castRingHom _)) _,
      NumberField.primitiveIntMinpoly_natDegree]
  have hmap : ((NumberField.primitiveIntMinpoly x).map
      (Int.castRingHom (Polynomial.SplittingField (minpoly ℚ x)))).roots.map
      (fun β => (∏ᶠ w : NumberField.FinitePlace
        (Polynomial.SplittingField (minpoly ℚ x)), max (w β) 1)
        ^ Module.finrank ℚ ↥(IntermediateField.adjoin ℚ {x}))
      = Multiset.replicate
        ((NumberField.primitiveIntMinpoly x).map
          (Int.castRingHom (Polynomial.SplittingField (minpoly ℚ x)))).roots.card
        ((∏ᶠ v : NumberField.FinitePlace ↥(IntermediateField.adjoin ℚ {x}),
          max (v (IntermediateField.AdjoinSimple.gen ℚ x)) 1)
          ^ Module.finrank ℚ (Polynomial.SplittingField (minpoly ℚ x))) := by
    rw [← Multiset.map_const']
    apply Multiset.map_congr rfl
    intro β hβ
    exact hN7 β hβ
  have hpow8 := congrArg (· ^ Module.finrank ℚ ↥(IntermediateField.adjoin ℚ {x})) hN8
  rw [← pow_mul, ← Multiset.prod_map_pow, hmap, Multiset.prod_replicate, hcardR,
    hfinF, ← pow_mul] at hpow8
  have hFL : Module.finrank ℚ (Polynomial.SplittingField (minpoly ℚ x)) ≠ 0 :=
    Module.finrank_pos.ne'
  have hd : (minpoly ℚ x).natDegree ≠ 0 := (minpoly.natDegree_pos hx).ne'
  have hA : (0 : ℝ) ≤ (((|(NumberField.primitiveIntMinpoly x).leadingCoeff| : ℤ)) : ℝ) := by
    positivity
  have hG : (0 : ℝ) ≤ (∏ᶠ v : NumberField.FinitePlace ↥(IntermediateField.adjoin ℚ {x}),
      max (v (IntermediateField.AdjoinSimple.gen ℚ x)) 1) := by
    apply finprod_nonneg
    intro v
    exact zero_le_one.trans (le_max_right _ _)
  have hne : Module.finrank ℚ (Polynomial.SplittingField (minpoly ℚ x))
      * (minpoly ℚ x).natDegree ≠ 0 :=
    Nat.mul_ne_zero hFL hd
  exact (pow_left_inj₀ hG hA hne).mp hpow8

-- Infinite places with multiplicity are complex embeddings.
private theorem alh_prod_infinitePlace_pow_mult_eq_prod_embeddings
    {E : Type*} [Field E] [NumberField E] {M : Type*} [CommMonoid M]
    (h : NumberField.InfinitePlace E → M) :
    ∏ w : NumberField.InfinitePlace E, h w ^ w.mult
      = ∏ φ : E →+* ℂ, h (NumberField.InfinitePlace.mk φ) := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ
    (fun φ : E →+* ℂ => NumberField.InfinitePlace.mk φ)
    (fun φ => h (NumberField.InfinitePlace.mk φ))]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hconst : ∀ φ ∈ Finset.univ.filter
      (fun φ : E →+* ℂ => NumberField.InfinitePlace.mk φ = w),
      h (NumberField.InfinitePlace.mk φ) = h w := by
    intro φ hφ
    rw [Finset.mem_filter] at hφ
    rw [hφ.2]
  rw [Finset.prod_congr rfl hconst, Finset.prod_const,
    NumberField.InfinitePlace.card_filter_mk_eq]

-- Multiplicative height at the generator is the Mahler measure.
private theorem alh_mulHeight₁_gen_eq_mahlerMeasure
    {K : Type*} [Field K] [CharZero K] {x : K} (hx : IsIntegral ℚ x)
    [FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ {x})]
    [NumberField ↥(IntermediateField.adjoin ℚ {x})] :
    Height.mulHeight₁ (IntermediateField.AdjoinSimple.gen ℚ x)
      = Polynomial.mahlerMeasure
        ((NumberField.primitiveIntMinpoly x).map (Int.castRingHom ℂ)) := by
  have h11 : (∏ w : NumberField.InfinitePlace ↥(IntermediateField.adjoin ℚ {x}),
      max (w (IntermediateField.AdjoinSimple.gen ℚ x)) 1 ^ w.mult)
      = ∏ φ : ↥(IntermediateField.adjoin ℚ {x}) →+* ℂ,
        max ((NumberField.InfinitePlace.mk φ)
          (IntermediateField.AdjoinSimple.gen ℚ x)) 1 :=
    alh_prod_infinitePlace_pow_mult_eq_prod_embeddings _
  have hrootsC : ((NumberField.primitiveIntMinpoly x).map (Int.castRingHom ℂ)).roots
      = (minpoly ℚ x).aroots ℂ :=
    alh_primitiveIntMinpoly_map_roots_eq_aroots hx ℂ
  have hnodup := alh_primitiveIntMinpoly_map_roots_nodup hx ℂ
  have hval : ∀ ψ : ↥(IntermediateField.adjoin ℚ {x}) →ₐ[ℚ] ℂ,
      (((IntermediateField.algHomAdjoinIntegralEquiv ℚ (K := ℂ) hx) ψ :
        {y : ℂ // y ∈ (minpoly ℚ x).aroots ℂ}) : ℂ)
      = ψ (IntermediateField.AdjoinSimple.gen ℚ x) := by
    intro ψ
    have h := IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ (K := ℂ)
      hx ((IntermediateField.algHomAdjoinIntegralEquiv ℚ (K := ℂ) hx) ψ)
    rw [Equiv.symm_apply_apply] at h
    exact h.symm
  have htrans : (∏ φ : ↥(IntermediateField.adjoin ℚ {x}) →+* ℂ,
      max ‖φ (IntermediateField.AdjoinSimple.gen ℚ x)‖ 1)
      = ∏ y : {y : ℂ // y ∈ (minpoly ℚ x).aroots ℂ}, max ‖(y : ℂ)‖ 1 := by
    apply Fintype.prod_equiv ((RingHom.equivRatAlgHom _ _).trans
      (IntermediateField.algHomAdjoinIntegralEquiv ℚ (K := ℂ) hx))
    intro φ
    simp only [Equiv.trans_apply]
    rw [hval, RingHom.equivRatAlgHom_apply, RingHom.toRatAlgHom_apply]
  have hsub : (∏ y : {y : ℂ // y ∈ (minpoly ℚ x).aroots ℂ}, max ‖(y : ℂ)‖ 1)
      = (Multiset.map (fun a => max ‖a‖ 1)
        ((NumberField.primitiveIntMinpoly x).map (Int.castRingHom ℂ)).roots).prod := by
    let hFI : Fintype {y : ℂ // y ∈ (minpoly ℚ x).aroots ℂ} :=
      Multiset.Subtype.fintype _
    have hps := Finset.prod_subtype (F := hFI) ((minpoly ℚ x).aroots ℂ).toFinset
      (fun z => Multiset.mem_toFinset) (fun z => max ‖z‖ 1)
    have hnodA : ((minpoly ℚ x).aroots ℂ).Nodup := by
      rwa [← hrootsC]
    have hdedup : ((minpoly ℚ x).aroots ℂ).dedup
        = ((NumberField.primitiveIntMinpoly x).map (Int.castRingHom ℂ)).roots := by
      rw [hnodA.dedup, ← hrootsC]
    have e1 : (∏ a ∈ ((minpoly ℚ x).aroots ℂ).toFinset, max ‖a‖ 1)
        = (Multiset.map (fun z => max ‖z‖ 1)
          ((NumberField.primitiveIntMinpoly x).map (Int.castRingHom ℂ)).roots).prod := by
      rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hdedup]
    exact hps.symm.trans e1
  have hflip : (Multiset.map (fun a => max ‖a‖ 1)
      ((NumberField.primitiveIntMinpoly x).map (Int.castRingHom ℂ)).roots).prod
      = (Multiset.map (fun a => max 1 ‖a‖)
        ((NumberField.primitiveIntMinpoly x).map (Int.castRingHom ℂ)).roots).prod := by
    congr 1
    exact Multiset.map_congr rfl (fun a _ => max_comm _ _)
  have hlcC : ‖((NumberField.primitiveIntMinpoly x).map
      (Int.castRingHom ℂ)).leadingCoeff‖
      = (((|(NumberField.primitiveIntMinpoly x).leadingCoeff| : ℤ)) : ℝ) := by
    have e : (Int.castRingHom ℂ) ((NumberField.primitiveIntMinpoly x).leadingCoeff)
        = (((NumberField.primitiveIntMinpoly x).leadingCoeff : ℤ) : ℂ) := rfl
    rw [Polynomial.leadingCoeff_map_of_injective
      (RingHom.injective_int (Int.castRingHom ℂ)) _, e, Complex.norm_intCast]
    exact Int.cast_abs.symm
  rw [NumberField.mulHeight₁_eq, h11]
  simp only [NumberField.InfinitePlace.apply]
  rw [htrans, hsub, hflip,
    Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots, hlcC,
    alh_finprod_max_gen_eq_abs_leadingCoeff hx]
  exact mul_comm _ _

/-- **Logarithmic height from the roots of the minimal polynomial, for an integral element.** Let
$K$ be a field of characteristic zero and let $x \in K$ be integral over $\mathbb{Q}$. Let $d$ be
the degree of the minimal polynomial of $x$ over $\mathbb{Q}$, and let $P_x \in \mathbb{Z}[X]$ be
the primitive integral minimal polynomial of $x$, with leading coefficient $a$. Then the absolute
logarithmic height of $x$ is
$$h(x) = \frac{1}{d}\Big(\log |a| + \sum_{z} \log^+ |z|\Big),$$
where the sum runs over the complex roots $z$ of $P_x$, counted with multiplicity, and
$\log^+ t = \max(0, \log t)$. -/
public theorem absLogHeight₁_eq_log_leadingCoeff_add_sum_log_roots_of_isIntegral
    {K : Type*} [Field K] [CharZero K] [Algebra ℚ K] (x : K) (hx : IsIntegral ℚ x) :
    NumberField.absLogHeight₁ x =
      (Real.log
          ‖((NumberField.primitiveIntMinpoly x).map (Int.castRingHom ℂ)).leadingCoeff‖ +
        (((NumberField.primitiveIntMinpoly x).map (Int.castRingHom ℂ)).roots.map
          (fun z => Real.posLog ‖z‖)).sum) /
        ((minpoly ℚ x).natDegree : ℝ) := by
  have hAlg : (inferInstance : Algebra ℚ K) = DivisionRing.toRatAlgebra :=
    Subsingleton.elim _ _
  subst hAlg
  rw [NumberField.absLogHeight₁, NumberField.absMulHeight₁, dite_eq_left hx]
  let _ : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {x}) :=
    IntermediateField.adjoin.finiteDimensional hx
  let _ : NumberField (IntermediateField.adjoin ℚ {x}) := {}
  rw [Real.log_rpow (Height.mulHeight₁_pos _) _,
    IntermediateField.adjoin.finrank hx,
    alh_mulHeight₁_gen_eq_mahlerMeasure hx,
    ← Polynomial.logMahlerMeasure_eq_log_MahlerMeasure,
    Polynomial.logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots,
    div_eq_inv_mul]

/-- **Logarithmic height from the roots of the minimal polynomial, for an algebraic element.** Let
$K$ be a field of characteristic zero and let $x \in K$ be algebraic over $\mathbb{Q}$. Let $d$ be
the degree of the minimal polynomial of $x$ over $\mathbb{Q}$, and let $P_x \in \mathbb{Z}[X]$ be
the primitive integral minimal polynomial of $x$, with leading coefficient $a$. Then the absolute
logarithmic height of $x$ is
$$h(x) = \frac{1}{d}\Big(\log |a| + \sum_{z} \log^+ |z|\Big),$$
where the sum runs over the complex roots $z$ of $P_x$, counted with multiplicity, and
$\log^+ t = \max(0, \log t)$. -/
public theorem absLogHeight₁_eq_log_leadingCoeff_add_sum_log_roots_of_isAlgebraic
    {K : Type*} [Field K] [CharZero K] [Algebra ℚ K] (x : K) (hx : IsAlgebraic ℚ x) :
    NumberField.absLogHeight₁ x =
      (Real.log
          ‖((NumberField.primitiveIntMinpoly x).map (Int.castRingHom ℂ)).leadingCoeff‖ +
        (((NumberField.primitiveIntMinpoly x).map (Int.castRingHom ℂ)).roots.map
          (fun z => Real.posLog ‖z‖)).sum) /
        ((minpoly ℚ x).natDegree : ℝ) :=
  absLogHeight₁_eq_log_leadingCoeff_add_sum_log_roots_of_isIntegral x
    (IsAlgebraic.isIntegral hx)

/-- **Logarithmic height from the roots of the minimal polynomial.** Let $K$ be a field of
characteristic zero that is algebraic over $\mathbb{Q}$, and let $x \in K$. Let $d$ be the degree
of the minimal polynomial of $x$ over $\mathbb{Q}$, and let $P_x \in \mathbb{Z}[X]$ be the
primitive integral minimal polynomial of $x$, with leading coefficient $a$. Then the absolute
logarithmic height of $x$ is
$$h(x) = \frac{1}{d}\Big(\log |a| + \sum_{z} \log^+ |z|\Big),$$
where the sum runs over the complex roots $z$ of $P_x$, counted with multiplicity, and
$\log^+ t = \max(0, \log t)$.

Proves `Wanted` entry `absLogHeight₁_eq_log_leadingCoeff_add_sum_log_roots`.

Source: arXiv:2608.15903; equivalent formulas occur
in arXiv:2304.11607, 2309.11173, 2311.13047, 2311.14001, 2607.25168, 2608.04445, and 2608.20995.
-/
public theorem absLogHeight₁_eq_log_leadingCoeff_add_sum_log_roots
    {K : Type*} [Field K] [CharZero K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K] (x : K) :
    NumberField.absLogHeight₁ x =
      (Real.log
          ‖((NumberField.primitiveIntMinpoly x).map (Int.castRingHom ℂ)).leadingCoeff‖ +
        (((NumberField.primitiveIntMinpoly x).map (Int.castRingHom ℂ)).roots.map
          (fun z => Real.posLog ‖z‖)).sum) /
        ((minpoly ℚ x).natDegree : ℝ) :=
  absLogHeight₁_eq_log_leadingCoeff_add_sum_log_roots_of_isIntegral x
    (IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic x))

/-- **Multiplicative height as a Mahler measure, for an integral element.** Let $K$ be a field of
characteristic zero and let $x \in K$ be integral over $\mathbb{Q}$. Let $d$ be the degree of the
minimal polynomial of $x$ over $\mathbb{Q}$, and let $P_x \in \mathbb{Z}[X]$ be the primitive
integral minimal polynomial of $x$. Then the absolute multiplicative height of $x$ is
$H(x) = M(P_x)^{1/d}$, where $M(P_x)$ is the Mahler measure of $P_x$ regarded as a polynomial
with complex coefficients. -/
public theorem absMulHeight₁_eq_mapMahlerMeasure_of_isIntegral
    {K : Type*} [Field K] [CharZero K] [Algebra ℚ K] (x : K) (hx : IsIntegral ℚ x) :
    NumberField.absMulHeight₁ x =
      (NumberField.primitiveIntMinpoly x).mapMahlerMeasure (Int.castRingHom ℂ) ^
        ((minpoly ℚ x).natDegree : ℝ)⁻¹ := by
  have hAlg : (inferInstance : Algebra ℚ K) = DivisionRing.toRatAlgebra :=
    Subsingleton.elim _ _
  subst hAlg
  rw [NumberField.absMulHeight₁, dite_eq_left hx]
  let _ : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {x}) :=
    IntermediateField.adjoin.finiteDimensional hx
  let _ : NumberField (IntermediateField.adjoin ℚ {x}) := {}
  rw [IntermediateField.adjoin.finrank hx,
    alh_mulHeight₁_gen_eq_mahlerMeasure hx,
    Polynomial.mapMahlerMeasure_eq]

/--
**Absolute multiplicative height as a Mahler measure.** Let $K$ be a field of characteristic
zero that is algebraic over $\mathbb{Q}$, and let $x \in K$. Let $d$ be the degree of the minimal
polynomial of $x$ over $\mathbb{Q}$, and let $P_x \in \mathbb{Z}[X]$ be the primitive integral
minimal polynomial of $x$. Then the absolute multiplicative height of $x$ is $H(x) = M(P_x)^{1/d}$,
where $M(P_x)$ is the Mahler measure of $P_x$ regarded as a polynomial with complex coefficients.

Proves `Wanted` entry `absMulHeight₁_eq_mapMahlerMeasure`.

Source: arXiv:2608.15891, lines
205–217; equivalent formulations also occur in arXiv:2306.11331, 2307.11849, 2307.14915,
2312.04354, 2607.28857, 2607.29208, and 2608.11904.
-/
public theorem absMulHeight₁_eq_mapMahlerMeasure {K : Type*} [Field K] [CharZero K]
    [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K] (x : K) :
    NumberField.absMulHeight₁ x =
      (NumberField.primitiveIntMinpoly x).mapMahlerMeasure (Int.castRingHom ℂ) ^
        ((minpoly ℚ x).natDegree : ℝ)⁻¹ :=
  absMulHeight₁_eq_mapMahlerMeasure_of_isIntegral x
    (IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic x))

end MathlibExt.NumberTheory.Height.AbsoluteWanted
