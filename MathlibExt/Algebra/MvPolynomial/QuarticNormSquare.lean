/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`Theorems/Thm_MvPolynomial_isSquare_or_isSquare_of_isHomogeneous_
of_forall_eval_mul_eq.lean`
and
`P2M/Sol/S_MvPolynomial_isSquare_or_isSquare_of_isHomogeneous_
of_forall_eval_mul_eq.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
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

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Real.Sqrt
public import Mathlib.Data.Real.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section

set_option autoImplicit false

namespace P2mKcQuarticNorm

section Mono

variable {K : Type*} [Field K] [Infinite K]

open Polynomial

private theorem poly_eq_of_forall_ne_zero (p q : K[X]) (h : ∀ s : K, s ≠ 0 → p.eval s = q.eval s) :
    p = q := by
  have hinf : Set.Infinite {s : K | s ≠ 0} := by
    have : ({s : K | s ≠ 0}) = ({(0 : K)} : Set K)ᶜ := by ext; simp
    rw [this]; exact (Set.finite_singleton _).infinite_compl
  have h0 : p - q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply hinf.mono
    intro s hs
    simp only [Set.mem_setOf_eq, IsRoot.def, eval_sub, h s hs, sub_self]
  exact sub_eq_zero.mp h0

private theorem eq_X_pow_of_mul : ∀ (N : ℕ) (p : K[X]), p.natDegree ≤ N →
    (∀ s s' : K, s' ≠ 0 → p.eval (s * s') = p.eval s * p.eval s') → p.eval 1 = 1 → ∃ α : ℕ, p = X ^
        α := by
  intro N
  induction N with
  | zero =>
      intro p hN _ h1
      refine ⟨0, ?_⟩
      rw [Nat.le_zero, Polynomial.natDegree_eq_zero] at hN
      obtain ⟨x, rfl⟩ := hN
      rw [eval_C] at h1
      rw [h1, pow_zero, map_one]
  | succ N ih =>
      intro p hN hmul h1
      by_cases h0 : p.eval 0 = 0
      · obtain ⟨p₁, rfl⟩ : X ∣ p := Polynomial.X_dvd_iff.mpr (by rwa
            [Polynomial.coeff_zero_eq_eval_zero])
        have hp₁ : p₁ ≠ 0 := by
          rintro rfl
          simp at h1
        have hdeg : p₁.natDegree ≤ N := by
          have := Polynomial.natDegree_X_mul hp₁
          omega
        have h1' : p₁.eval 1 = 1 := by simpa using h1

        have hmul₀ : ∀ s s' : K, s ≠ 0 → s' ≠ 0 → p₁.eval (s * s') = p₁.eval s * p₁.eval s' := by
          intro s s' hs hs'
          have := hmul s s' hs'
          simp only [eval_mul, eval_X] at this
          have hss : s * s' ≠ 0 := mul_ne_zero hs hs'
          apply mul_left_cancel₀ hss
          linear_combination this

        have hmul' : ∀ s s' : K, s' ≠ 0 → p₁.eval (s * s') = p₁.eval s * p₁.eval s' := by
          intro s s' hs'
          have hid : p₁.comp (X * C s') = p₁ * C (p₁.eval s') := by
            apply poly_eq_of_forall_ne_zero
            intro u hu
            simp only [eval_comp, eval_mul, eval_X, eval_C]
            exact hmul₀ u s' hu hs'
          have := congrArg (Polynomial.eval s) hid
          simpa only [eval_comp, eval_mul, eval_X, eval_C] using this
        obtain ⟨α, hα⟩ := ih p₁ hdeg hmul' h1'
        exact ⟨α + 1, by rw [hα, pow_succ, mul_comm]⟩
      · refine ⟨0, ?_⟩
        rw [pow_zero]
        apply poly_eq_of_forall_ne_zero
        intro s hs
        have := hmul 0 s hs
        rw [zero_mul] at this
        rw [eval_one]

        have h2 : p.eval 0 * (p.eval s - 1) = 0 := by linear_combination -this
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact absurd h3 h0
        · linear_combination h3

private theorem exists_eq_prod_pow {ι : Type*} [Fintype ι] [DecidableEq ι] (g : (ι → K) → K)
    (hmul : ∀ y y' : ι → K, g (y * y') = g y * g y') (hone : g 1 = 1)
    (hpoly : ∀ i : ι, ∃ p : K[X], ∀ s : K, g (Function.update 1 i s) = p.eval s) :
    ∃ α : ι → ℕ, ∀ y : ι → K, g y = ∏ i, y i ^ α i := by
  have key : ∀ i : ι, ∃ αi : ℕ, ∀ s : K, g (Function.update 1 i s) = s ^ αi := by
    intro i
    obtain ⟨p, hp⟩ := hpoly i
    have hpm : ∀ s s' : K, s' ≠ 0 → p.eval (s * s') = p.eval s * p.eval s' := by
      intro s s' _
      rw [← hp, ← hp, ← hp, ← hmul]
      congr 1
      ext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    have hp1 : p.eval 1 = 1 := by
      rw [← hp]
      have : Function.update (1 : ι → K) i 1 = 1 := by
        ext j; by_cases hj : j = i
        · subst hj; simp
        · simp [Function.update_of_ne hj]
      rw [this, hone]
    obtain ⟨αi, hα⟩ := eq_X_pow_of_mul p.natDegree p le_rfl hpm hp1
    exact ⟨αi, fun s => by rw [hp, hα, eval_pow, eval_X]⟩
  choose α hα using key
  refine ⟨α, fun y => ?_⟩
  have hprod : ∀ (s : Finset ι) (z : ι → (ι → K)), g (∏ i ∈ s, z i) = ∏ i ∈ s, g (z i) := by
    intro s z
    induction s using Finset.induction_on with
    | empty => simp [hone]
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, hmul, ih]
  conv_lhs => rw [← Finset.univ_prod_mulSingle y]
  rw [hprod]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact hα i (y i)

end Mono

section Mul

private def mulV {R : Type*} [CommRing R] (D c : R) (v w : Fin 4 → R) : Fin 4 → R :=
  ![v 0 * w 0 + D * (v 1 * w 1) + c * (v 2 * w 2) + D * c * (v 3 * w 3),
    v 0 * w 1 + v 1 * w 0 + c * (v 2 * w 3 + v 3 * w 2),
    v 0 * w 2 + v 2 * w 0 + D * (v 1 * w 3 + v 3 * w 1),
    v 0 * w 3 + v 3 * w 0 + v 1 * w 2 + v 2 * w 1]

private theorem map_mulV {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (D c : R) (v w : Fin
    4 → R) :
    (fun i => φ (mulV D c v w i)) = mulV (φ D) (φ c) (fun i => φ (v i)) (fun i => φ (w i)) := by
  ext i
  fin_cases i <;> simp [mulV]

private noncomputable def mulPoly (D c : ℚ) : Fin 4 → MvPolynomial (Fin 4 ⊕ Fin 4) ℚ :=
  mulV (MvPolynomial.C D) (MvPolynomial.C c) (fun i => MvPolynomial.X (Sum.inl i)) (fun i =>
      MvPolynomial.X (Sum.inr i))

private theorem aeval_mulPoly {S : Type*} [CommRing S] [Algebra ℚ S] (D c : ℚ) (x : Fin 4 ⊕ Fin 4 →
    S) (i : Fin 4) :
    MvPolynomial.aeval x (mulPoly D c i) =
      mulV (algebraMap ℚ S D) (algebraMap ℚ S c) (fun i => x (Sum.inl i)) (fun i => x (Sum.inr i)) i
          := by
  fin_cases i <;> simp [mulPoly, mulV]

private theorem aeval_mulV_eq {S : Type*} [CommRing S] [Algebra ℚ S] (D c : ℤ) (F : (Fin 4 → ℤ) → ℕ)
    (P : MvPolynomial (Fin 4) ℚ)
    (hF : ∀ v : Fin 4 → ℤ, (F v : ℚ) = MvPolynomial.eval (fun i => (v i : ℚ)) P)
    (hmul : ∀ v w : Fin 4 → ℤ, F (mulV D c v w) = F v * F w)
    (v w : Fin 4 → S) :
    MvPolynomial.aeval (mulV (algebraMap ℚ S D) (algebraMap ℚ S c) v w) P =
      MvPolynomial.aeval v P * MvPolynomial.aeval w P := by
  classical

  set Q : MvPolynomial (Fin 4 ⊕ Fin 4) ℚ :=
    MvPolynomial.bind₁ (mulPoly D c) P -
      MvPolynomial.rename Sum.inl P * MvPolynomial.rename Sum.inr P with hQ
  have hQ0 : Q = 0 := by
    apply MvPolynomial.funext_set (fun _ => Set.range (Int.cast : ℤ → ℚ))
      (fun _ => Set.infinite_range_of_injective Int.cast_injective)
    intro x hx
    rw [Set.mem_univ_pi] at hx
    choose z hz using hx
    have hxz : x = fun i => (z i : ℚ) := funext fun i => (hz i).symm
    rw [map_zero]
    change MvPolynomial.aeval x Q = 0
    rw [hQ, map_sub, map_mul, MvPolynomial.aeval_bind₁, MvPolynomial.aeval_rename,
        MvPolynomial.aeval_rename]
    simp only [aeval_mulPoly, MvPolynomial.aeval_eq_eval, hxz]
    have h1 : mulV (algebraMap ℚ ℚ (D : ℚ)) (algebraMap ℚ ℚ (c : ℚ)) (fun i => ((z (Sum.inl i)) :
        ℚ))
        (fun i => ((z (Sum.inr i)) : ℚ)) =
        fun i => ((mulV D c (fun i => z (Sum.inl i)) (fun i => z (Sum.inr i)) i : ℤ) : ℚ) := by
      have := map_mulV (Int.castRingHom ℚ) D c (fun i => z (Sum.inl i)) (fun i => z (Sum.inr i))
      simp only [eq_intCast] at this
      rw [this]
      simp
    rw [h1, ← hF, show ((fun i => (z i : ℚ)) ∘ Sum.inl) = fun i => ((z (Sum.inl i) : ℤ) : ℚ) from
        rfl,
      show ((fun i => (z i : ℚ)) ∘ Sum.inr) = fun i => ((z (Sum.inr i) : ℤ) : ℚ) from rfl, ← hF, ←
          hF, hmul]
    push_cast
    ring
  have := congrArg (MvPolynomial.aeval (Sum.elim v w)) hQ0
  rw [map_zero, hQ, map_sub, map_mul, MvPolynomial.aeval_bind₁, MvPolynomial.aeval_rename,
    MvPolynomial.aeval_rename, sub_eq_zero] at this
  simpa only [aeval_mulPoly, Sum.elim_inl, Sum.elim_inr, Sum.elim_comp_inl, Sum.elim_comp_inr] using
      this

private theorem eval_smul_of_isHomogeneous {σ R : Type*} [CommSemiring R] {φ : MvPolynomial σ R} {n
    : ℕ}
    (hφ : φ.IsHomogeneous n) (r : R) (x : σ → R) :
    MvPolynomial.eval (r • x) φ = r ^ n * MvPolynomial.eval x φ := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [hφ.degree_eq_sum_deg_support hd, ← Finset.prod_pow_eq_pow_sum, mul_left_comm, ←
      Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
  rw [Pi.smul_apply, smul_eq_mul, mul_pow]

private theorem aeval_smul_real (P : MvPolynomial (Fin 4) ℚ) (hP : P.IsHomogeneous 4) (r : ℝ) (v :
    Fin 4 → ℝ) :
    MvPolynomial.aeval (r • v) P = r ^ 4 * MvPolynomial.aeval v P := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, ← MvPolynomial.eval_map, ←
      MvPolynomial.eval_map]
  exact eval_smul_of_isHomogeneous (hP.map _) r v

private theorem aeval_intCast (F : (Fin 4 → ℤ) → ℕ) (P : MvPolynomial (Fin 4) ℚ)
    (hF : ∀ v : Fin 4 → ℤ, (F v : ℚ) = MvPolynomial.eval (fun i => (v i : ℚ)) P) (z : Fin 4 → ℤ) :
    MvPolynomial.aeval (fun i => ((z i : ℤ) : ℝ)) P = (F z : ℝ) := by
  have h1 : (fun i => ((z i : ℤ) : ℝ)) = (algebraMap ℚ ℝ) ∘ (fun i => ((z i : ℤ) : ℚ)) := by
    ext i; simp
  have h2 := MvPolynomial.eval₂_comp_left (algebraMap ℚ ℝ) (RingHom.id ℚ) (fun i => ((z i : ℤ) : ℚ))
      P
  rw [RingHom.comp_id] at h2
  rw [MvPolynomial.aeval_def, h1, ← h2]
  change algebraMap ℚ ℝ (MvPolynomial.eval (fun i => ((z i : ℤ) : ℚ)) P) = _
  rw [← hF]
  simp

end Mul

section Chi

private def sgn1 : Fin 4 → ℝ := ![1, 1, -1, -1]
private def sgn2 : Fin 4 → ℝ := ![1, -1, 1, -1]

private def chi (d e : ℝ) (v : Fin 4 → ℝ) : Fin 4 → ℝ := fun i =>
  v 0 + sgn1 i * d * v 1 + sgn2 i * e * v 2 + sgn1 i * sgn2 i * (d * e) * v 3

private noncomputable def xi (d e : ℝ) (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![(y 0 + y 1 + y 2 + y 3) / 4, (y 0 + y 1 - y 2 - y 3) / (4 * d), (y 0 - y 1 + y 2 - y 3) / (4 *
      e),
    (y 0 - y 1 - y 2 + y 3) / (4 * d * e)]

variable {d e : ℝ}

private theorem chi_apply (v : Fin 4 → ℝ) (i : Fin 4) :
    chi d e v i = v 0 + sgn1 i * d * v 1 + sgn2 i * e * v 2 + sgn1 i * sgn2 i * (d * e) * v 3 := rfl

private theorem chi_xi (hd : d ≠ 0) (he : e ≠ 0) (y : Fin 4 → ℝ) : chi d e (xi d e y) = y := by
  have h4d : (4 : ℝ) * d ≠ 0 := mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hd
  have h4e : (4 : ℝ) * e ≠ 0 := mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) he
  have h4de : (4 : ℝ) * d * e ≠ 0 := mul_ne_zero h4d he
  ext i
  fin_cases i <;> simp [chi, xi, sgn1, sgn2] <;> field_simp [hd, he, h4d, h4e, h4de] <;> ring

private theorem xi_chi (hd : d ≠ 0) (he : e ≠ 0) (v : Fin 4 → ℝ) : xi d e (chi d e v) = v := by
  have h4d : (4 : ℝ) * d ≠ 0 := mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hd
  have h4e : (4 : ℝ) * e ≠ 0 := mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) he
  have h4de : (4 : ℝ) * d * e ≠ 0 := mul_ne_zero h4d he
  ext i
  fin_cases i <;> simp [chi, xi, sgn1, sgn2] <;> field_simp [hd, he, h4d, h4e, h4de] <;> ring

private theorem chi_injective (hd : d ≠ 0) (he : e ≠ 0) : Function.Injective (chi d e) :=
  Function.LeftInverse.injective (xi_chi hd he)

private theorem chi_mulV (v w : Fin 4 → ℝ) : chi d e (mulV (d ^ 2) (e ^ 2) v w) = chi d e v * chi d
    e w := by
  ext i
  fin_cases i <;> simp [chi, mulV, sgn1, sgn2] <;> ring

private theorem xi_mul (hd : d ≠ 0) (he : e ≠ 0) (y y' : Fin 4 → ℝ) :
    xi d e (y * y') = mulV (d ^ 2) (e ^ 2) (xi d e y) (xi d e y') := by
  apply chi_injective hd he
  rw [chi_mulV, chi_xi hd he, chi_xi hd he, chi_xi hd he]

private theorem xi_one : xi d e 1 = ![1, 0, 0, 0] := by
  ext i
  fin_cases i <;> simp [xi]; ring

private theorem xi_update (i : Fin 4) (s : ℝ) :
    xi d e (Function.update 1 i s) = xi d e (Function.update 1 i 0) + s • xi d e (Pi.single i 1) :=
        by
  ext j
  fin_cases i <;> fin_cases j <;> simp [xi, Function.update, Pi.single, Fin.ext_iff] <;> ring

end Chi

section Values

variable {d e : ℝ} (α : Fin 4 → ℕ)

private theorem cast_vec (a₀ a₁ a₂ a₃ : ℤ) :
    (fun i => ((![a₀, a₁, a₂, a₃] i : ℤ) : ℝ)) = ![(a₀ : ℝ), (a₁ : ℝ), (a₂ : ℝ), (a₃ : ℝ)] := by
  ext i; fin_cases i <;> simp

private theorem prod_chi_1100 : ∏ i, chi d e ![1, 1, 0, 0] i ^ α i = (1 + d) ^ (α 0 + α 1) * (1 - d)
    ^ (α 2 + α 3) := by
  simp only [Fin.prod_univ_four, chi_apply, sgn1, sgn2, pow_add]
  simp
  ring

private theorem prod_chi_1010 : ∏ i, chi d e ![1, 0, 1, 0] i ^ α i = (1 + e) ^ (α 0 + α 2) * (1 - e)
    ^ (α 1 + α 3) := by
  simp only [Fin.prod_univ_four, chi_apply, sgn1, sgn2, pow_add]
  simp
  ring

private theorem prod_chi_r001 (r : ℝ) :
    ∏ i, chi d e ![r, 0, 0, 1] i ^ α i = (r + d * e) ^ (α 0 + α 3) * (r - d * e) ^ (α 1 + α 2) := by
  simp only [Fin.prod_univ_four, chi_apply, sgn1, sgn2, pow_add]
  simp
  ring

private theorem prod_chi_2000 : ∏ i, chi d e ((2 : ℝ) • ![1, 0, 0, 0]) i ^ α i = 2 ^ (α 0 + α 1 + α
    2 + α 3) := by
  simp only [Fin.prod_univ_four, chi_apply, sgn1, sgn2, pow_add]
  simp

private theorem chi_test (w : ℚ) (i j : Fin 4) :
    chi d e ![((w.num : ℤ) : ℝ), -sgn1 i * (w.den : ℝ), -sgn2 i * (w.den : ℝ), 0] j =
      (w.den : ℝ) * ((w : ℝ) - (sgn1 j * sgn1 i * d + sgn2 j * sgn2 i * e)) := by
  have hw : ((w.num : ℤ) : ℝ) = (w : ℝ) * (w.den : ℝ) := by exact_mod_cast (Rat.mul_den_eq_num
      w).symm
  simp only [chi_apply]
  simp [hw]
  ring

private theorem chi_test_self (w : ℚ) (i : Fin 4) :
    chi d e ![((w.num : ℤ) : ℝ), -sgn1 i * (w.den : ℝ), -sgn2 i * (w.den : ℝ), 0] i =
      (w.den : ℝ) * ((w : ℝ) - (d + e)) := by
  rw [chi_test]
  fin_cases i <;> simp [sgn1, sgn2]

private theorem chi_test_pos (hd : 0 < d) (w : ℚ) (hw : |d - e| < (w : ℝ)) (i j : Fin 4) (hij : j ≠
    i) :
    0 < chi d e ![((w.num : ℤ) : ℝ), -sgn1 i * (w.den : ℝ), -sgn2 i * (w.den : ℝ), 0] j := by
  rw [chi_test]
  have hden : (0 : ℝ) < (w.den : ℝ) := by exact_mod_cast w.den_pos
  apply mul_pos hden
  rw [abs_sub_lt_iff] at hw
  fin_cases i <;> fin_cases j <;> simp [sgn1, sgn2] at hij ⊢ <;> linarith

private theorem cast_test (w : ℚ) (i : Fin 4) : ∃ z : Fin 4 → ℤ,
    (fun j => ((z j : ℤ) : ℝ)) = ![((w.num : ℤ) : ℝ), -sgn1 i * (w.den : ℝ), -sgn2 i * (w.den : ℝ),
        0] := by
  fin_cases i
  · exact ⟨![w.num, -w.den, -w.den, 0], by ext j; fin_cases j <;> simp [sgn1, sgn2]⟩
  · exact ⟨![w.num, -w.den, w.den, 0], by ext j; fin_cases j <;> simp [sgn1, sgn2]⟩
  · exact ⟨![w.num, w.den, -w.den, 0], by ext j; fin_cases j <;> simp [sgn1, sgn2]⟩
  · exact ⟨![w.num, w.den, w.den, 0], by ext j; fin_cases j <;> simp [sgn1, sgn2]⟩

end Values

private theorem two_of_rat (x : ℝ) (hx : Irrational x) (X : ℚ) (hx2 : x ^ 2 = (X : ℝ))
    (A B : ℕ) (hA : Even A) (hB : Even B) (hAB : A + B = 4) (m : ℚ) (hm : (1 + x) ^ A * (1 - x) ^ B
        = (m : ℝ)) :
    A = 2 := by
  obtain ⟨a, rfl⟩ := hA
  have hX0 : (0 : ℝ) ≤ X := by rw [← hx2]; positivity
  have h4 : (4 + 4 * (X : ℝ)) ≠ 0 := by positivity
  have ha : a ≤ 2 := by omega
  interval_cases a
  · exfalso
    have hB4 : B = 4 := by omega
    subst hB4
    simp only [add_zero, pow_zero, one_mul] at hm
    have hlin : x * (4 + 4 * X) = 1 + 6 * X + X ^ 2 - m := by
      linear_combination (-1 : ℝ) * hm + (6 - 4 * x + x ^ 2 + X) * hx2
    apply hx
    refine ⟨(1 + 6 * X + X ^ 2 - m) / (4 + 4 * X), ?_⟩
    push_cast
    field_simp
    linarith
  · rfl
  · exfalso
    have hB0 : B = 0 := by omega
    subst hB0
    simp only [pow_zero, mul_one] at hm
    have hlin : x * (4 + 4 * X) = m - 1 - 6 * X - X ^ 2 := by
      linear_combination hm - (6 + 4 * x + x ^ 2 + X) * hx2
    apply hx
    refine ⟨(m - 1 - 6 * X - X ^ 2) / (4 + 4 * X), ?_⟩
    push_cast
    field_simp
    linarith

private theorem main (D c : ℤ) (hD : 0 < D) (hc : 0 < c)
    (F : (Fin 4 → ℤ) → ℕ) (P : MvPolynomial (Fin 4) ℚ) (hP : P.IsHomogeneous 4)
    (hF : ∀ v : Fin 4 → ℤ, (F v : ℚ) = MvPolynomial.eval (fun i => (v i : ℚ)) P)
    (hone : F ![1, 0, 0, 0] = 1)
    (hmul : ∀ v w : Fin 4 → ℤ, F (mulV D c v w) = F v * F w)
    (hzd : ∀ r : ℤ, r ^ 2 = D * c → F ![r, 0, 0, 1] = 0) :
    IsSquare D ∨ IsSquare c := by
  by_contra hnot
  obtain ⟨hDs, hcs⟩ := not_or.mp hnot

  set d : ℝ := Real.sqrt D with hd_def
  set e : ℝ := Real.sqrt c with he_def
  have hd : 0 < d := Real.sqrt_pos.mpr (by exact_mod_cast hD)
  have he : 0 < e := Real.sqrt_pos.mpr (by exact_mod_cast hc)
  have hd2 : d ^ 2 = ((D : ℚ) : ℝ) := by rw [Rat.cast_intCast]; exact Real.sq_sqrt (by
      exact_mod_cast hD.le)
  have he2 : e ^ 2 = ((c : ℚ) : ℝ) := by rw [Rat.cast_intCast]; exact Real.sq_sqrt (by
      exact_mod_cast hc.le)
  have hdirr : Irrational d := (irrational_sqrt_intCast_iff_of_nonneg hD.le).mpr hDs
  have heirr : Irrational e := (irrational_sqrt_intCast_iff_of_nonneg hc.le).mpr hcs

  set f : (Fin 4 → ℝ) → ℝ := fun v => MvPolynomial.aeval v P with hf_def
  have hfmul : ∀ v w, f (mulV (d ^ 2) (e ^ 2) v w) = f v * f w := by
    intro v w
    have := aeval_mulV_eq (S := ℝ) D c F P hF hmul v w
    rw [show algebraMap ℚ ℝ (D : ℚ) = d ^ 2 by rw [hd2]; rfl,
      show algebraMap ℚ ℝ (c : ℚ) = e ^ 2 by rw [he2]; rfl] at this
    exact this
  have hfone : f ![1, 0, 0, 0] = 1 := by
    have := aeval_intCast F P hF ![1, 0, 0, 0]
    rw [cast_vec, hone] at this
    simpa using this
  set g : (Fin 4 → ℝ) → ℝ := fun y => f (xi d e y) with hg_def
  have hgmul : ∀ y y', g (y * y') = g y * g y' := by
    intro y y'
    simp only [hg_def]
    rw [xi_mul hd.ne' he.ne', hfmul]
  have hgone : g 1 = 1 := by
    simp only [hg_def]
    rw [xi_one, hfone]
  have hgpoly : ∀ i : Fin 4, ∃ p : Polynomial ℝ, ∀ s : ℝ, g (Function.update 1 i s) = p.eval s := by
    intro i
    refine ⟨MvPolynomial.aeval (fun j => Polynomial.C (xi d e (Function.update 1 i 0) j) +
      Polynomial.C (xi d e (Pi.single i 1) j) * Polynomial.X) P, fun s => ?_⟩
    simp only [hg_def, hf_def]
    rw [xi_update, ← Polynomial.coe_aeval_eq_eval,
      show (Polynomial.aeval s) (MvPolynomial.aeval _ P) =
        ((Polynomial.aeval s).restrictScalars ℚ).comp (MvPolynomial.aeval _) P from rfl,
      MvPolynomial.comp_aeval]
    congr 1
    ext j
    simp only [MvPolynomial.aeval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
      AlgHom.restrictScalars_apply, Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_self,
      RingHom.id_apply]
    ring
  obtain ⟨α, hα⟩ := exists_eq_prod_pow g hgmul hgone hgpoly

  have hfchi : ∀ v, f v = ∏ i, (chi d e v i) ^ α i := by
    intro v
    have := hα (chi d e v)
    simp only [hg_def, xi_chi hd.ne' he.ne'] at this
    exact this
  have hFint : ∀ z : Fin 4 → ℤ, (F z : ℝ) = ∏ i, (chi d e (fun i => (z i : ℝ)) i) ^ α i := by
    intro z
    rw [← aeval_intCast F P hF z]
    exact hfchi _

  have hsum : α 0 + α 1 + α 2 + α 3 = 4 := by
    have h1 : f ((2 : ℝ) • ![1, 0, 0, 0]) = 2 ^ 4 * f ![1, 0, 0, 0] := aeval_smul_real P hP 2 _
    rw [hfone, mul_one, hfchi, prod_chi_2000] at h1
    exact Nat.pow_right_injective le_rfl (by exact_mod_cast h1)

  have heven : ∀ i, Even (α i) := by
    have hlt : |d - e| < d + e := by
      rw [abs_sub_lt_iff]; constructor <;> linarith
    obtain ⟨w, hw1, hw2⟩ := exists_rat_btwn hlt
    intro i
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨z, hz⟩ := cast_test w i
    have hval := hFint z
    rw [hz] at hval
    have hden : (0 : ℝ) < (w.den : ℝ) := by exact_mod_cast w.den_pos
    have hneg : chi d e ![((w.num : ℤ) : ℝ), -sgn1 i * (w.den : ℝ), -sgn2 i * (w.den : ℝ), 0] i ^ α
        i < 0 := by
      apply Odd.pow_neg hodd
      rw [chi_test_self]
      apply mul_neg_of_pos_of_neg hden
      linarith
    have hpos : 0 < ∏ j ∈ Finset.univ.erase i,
        chi d e ![((w.num : ℤ) : ℝ), -sgn1 i * (w.den : ℝ), -sgn2 i * (w.den : ℝ), 0] j ^ α j := by
      apply Finset.prod_pos
      intro j hj
      exact pow_pos (chi_test_pos hd w hw1 i j (Finset.ne_of_mem_erase hj)) _
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)] at hval
    have : ((F z : ℕ) : ℝ) < 0 := by rw [hval]; exact mul_neg_of_pos_of_neg hpos hneg
    linarith [(Nat.cast_nonneg (F z) : (0 : ℝ) ≤ F z)]

  have hA : α 0 + α 1 = 2 := by
    apply two_of_rat d hdirr D hd2 (α 0 + α 1) (α 2 + α 3) ((heven 0).add (heven 1)) ((heven 2).add
        (heven 3))
      (by omega) (F ![1, 1, 0, 0])
    have := hFint ![1, 1, 0, 0]
    rw [cast_vec] at this
    push_cast at this
    rw [prod_chi_1100] at this
    rw [← this]
    norm_cast
  have hB : α 0 + α 2 = 2 := by
    apply two_of_rat e heirr c he2 (α 0 + α 2) (α 1 + α 3) ((heven 0).add (heven 2)) ((heven 1).add
        (heven 3))
      (by omega) (F ![1, 0, 1, 0])
    have := hFint ![1, 0, 1, 0]
    rw [cast_vec] at this
    push_cast at this
    rw [prod_chi_1010] at this
    rw [← this]
    norm_cast
  obtain ⟨k0, hk0⟩ := heven 0
  obtain ⟨k1, hk1⟩ := heven 1
  obtain ⟨k2, hk2⟩ := heven 2
  obtain ⟨k3, hk3⟩ := heven 3

  by_cases hDc : IsSquare (D * c)
  · obtain ⟨r, hr⟩ := hDc
    set r₀ : ℤ := |r| with hr₀
    have hr₀sq : r₀ ^ 2 = D * c := by rw [hr, hr₀, sq_abs, sq]
    have hr₀pos : 0 < r₀ := by
      rw [hr₀, abs_pos]
      rintro rfl
      have : D * c = 0 := by rw [hr, mul_zero]
      exact absurd this (mul_pos hD hc).ne'
    have hde : d * e = (r₀ : ℝ) := by
      have h1 : (d * e) ^ 2 = ((r₀ : ℝ)) ^ 2 := by
        rw [mul_pow, hd2, he2]; push_cast; exact_mod_cast hr₀sq.symm
      have h2 : 0 ≤ d * e := by positivity
      have h3 : (0 : ℝ) ≤ r₀ := by exact_mod_cast hr₀pos.le
      nlinarith [h1, h2, h3, sq_nonneg (d * e - r₀), sq_nonneg (d * e + r₀)]
    have hz1 := hzd r₀ hr₀sq
    have hz2 := hzd (-r₀) (by rw [neg_sq]; exact hr₀sq)
    have hv1 := hFint ![r₀, 0, 0, 1]
    rw [hz1, cast_vec] at hv1
    push_cast at hv1
    rw [prod_chi_r001, hde, sub_self] at hv1
    have hv2 := hFint ![-r₀, 0, 0, 1]
    rw [hz2, cast_vec] at hv2
    push_cast at hv2
    rw [prod_chi_r001, hde, neg_add_cancel] at hv2
    have hr2 : (r₀ : ℝ) + r₀ ≠ 0 := by positivity
    have h12 : α 1 + α 2 ≠ 0 := by
      intro h0
      rw [h0, pow_zero, mul_one] at hv1
      exact pow_ne_zero _ hr2 hv1.symm
    have h03 : α 0 + α 3 ≠ 0 := by
      intro h0
      rw [h0, pow_zero, one_mul, show (-(r₀ : ℝ) - r₀) = -(r₀ + r₀) by ring] at hv2
      exact pow_ne_zero _ (neg_ne_zero.mpr hr2) hv2.symm
    omega
  · have hde2 : (d * e) ^ 2 = (((D * c : ℤ) : ℚ) : ℝ) := by
      rw [mul_pow, hd2, he2]; push_cast; ring
    have hdeirr : Irrational (d * e) := by
      have : d * e = Real.sqrt ((D * c : ℤ) : ℝ) := by
        rw [Int.cast_mul, Real.sqrt_mul (by exact_mod_cast hD.le)]
      rw [this]
      exact (irrational_sqrt_intCast_iff_of_nonneg (by positivity)).mpr hDc
    have hC : α 0 + α 3 = 2 := by
      apply two_of_rat (d * e) hdeirr _ hde2 (α 0 + α 3) (α 1 + α 2) ((heven 0).add (heven 3))
        ((heven 1).add (heven 2)) (by omega) (F ![1, 0, 0, 1])
      have := hFint ![1, 0, 0, 1]
      rw [cast_vec] at this
      push_cast at this
      rw [prod_chi_r001] at this
      rw [← this]
      norm_cast
    omega

end P2mKcQuarticNorm

/-- If the values of a homogeneous degree-four multivariate polynomial over
the rationals, encoded as a natural-number-valued function on integer
quadruples, are multiplicative for the indicated four-variable product and
normalized at the first basis vector, and vanish at the indicated test
vectors whenever a square root condition holds, then at least one of the
two positive integer parameters is a square. -/
public theorem MvPolynomial.isSquare_or_isSquare_of_isHomogeneous_of_forall_eval_mul_eq
    (D c : ℤ) (hD : 0 < D) (hc : 0 < c)
    (F : (Fin 4 → ℤ) → ℕ) (P : MvPolynomial (Fin 4) ℚ) (hP : P.IsHomogeneous 4)
    (hF : ∀ v : Fin 4 → ℤ, (F v : ℚ) = MvPolynomial.eval (fun i => (v i : ℚ)) P)
    (hone : F ![1, 0, 0, 0] = 1)
    (hmul : ∀ v w : Fin 4 → ℤ,
      F ![v 0 * w 0 + D * (v 1 * w 1) + c * (v 2 * w 2) + D * c * (v 3 * w 3),
          v 0 * w 1 + v 1 * w 0 + c * (v 2 * w 3 + v 3 * w 2),
          v 0 * w 2 + v 2 * w 0 + D * (v 1 * w 3 + v 3 * w 1),
          v 0 * w 3 + v 3 * w 0 + v 1 * w 2 + v 2 * w 1] = F v * F w)
    (hzd : ∀ r : ℤ, r ^ 2 = D * c → F ![r, 0, 0, 1] = 0) :
    IsSquare D ∨ IsSquare c :=
  P2mKcQuarticNorm.main D c hD hc F P hP hF hone (fun v w => hmul v w) hzd
