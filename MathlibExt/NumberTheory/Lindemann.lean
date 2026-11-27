/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.Group.UniqueProds.VectorSpace
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MathlibExt.NumberTheory.LindemannWanted

/-!
# Hermite–Lindemann theorem
This file proves the Hermite–Lindemann theorem: if `α : ℂ` is nonzero and algebraic
over `ℚ`, then `Complex.exp α` is transcendental over `ℚ`.
-/

/-- N1: strip powers of X from a monic integer polynomial killing a nonzero integral x. -/
private theorem hl_exists_monic_coeff_zero_ne_zero_of_isIntegral (x : ℂ) (hx : x ≠ 0)
    (hint : IsIntegral ℤ x) :
    ∃ q : Polynomial ℤ, q.Monic ∧ q.coeff 0 ≠ 0 ∧ Polynomial.aeval x q = 0 := by
  obtain ⟨p, hpmonic, hpeval⟩ := hint
  have hp0 : p ≠ 0 := hpmonic.ne_zero
  obtain ⟨q, hq_eq, hq_ndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 0
  have hX0 : (Polynomial.X - Polynomial.C (0 : ℤ)) = Polynomial.X := by simp
  rw [hX0] at hq_eq hq_ndvd
  have hXpow_monic : ((Polynomial.X : Polynomial ℤ) ^ Polynomial.rootMultiplicity 0 p).Monic :=
    Polynomial.monic_X_pow _
  have hq_monic : q.Monic := by
    have hprod_monic :
        ((Polynomial.X : Polynomial ℤ) ^ Polynomial.rootMultiplicity 0 p
          * q).Monic := by
      rw [← hq_eq]; exact hpmonic
    exact Polynomial.Monic.of_mul_monic_left hXpow_monic hprod_monic
  refine ⟨q, hq_monic, ?_, ?_⟩
  · intro hcoeff
    exact hq_ndvd (Polynomial.X_dvd_iff.mpr hcoeff)
  · have hpeval_a : Polynomial.aeval x p = 0 := hpeval
    have haeval : Polynomial.aeval x p = Polynomial.aeval x
        ((Polynomial.X : Polynomial ℤ) ^ Polynomial.rootMultiplicity 0 p * q) := by
      rw [← hq_eq]
    rw [map_mul, map_pow, Polynomial.aeval_X] at haeval
    rw [hpeval_a] at haeval
    have hxr : x ^ Polynomial.rootMultiplicity 0 p ≠ 0 := pow_ne_zero _ hx
    rcases mul_eq_zero.mp haeval.symm with h1 | h1
    · exact absurd h1 hxr
    · exact h1

open Classical in
/-- N2: common monic integer polynomial vanishing at all nonzero integral
points, with nonzero constant term. -/
private theorem hl_exists_int_poly_eval_zero_ne_zero_of_isIntegral {ι : Type*}
    [Finite ι] (x : ι → ℂ) (hint : ∀ i, IsIntegral ℤ (x i)) :
    ∃ F : Polynomial ℤ, F.Monic ∧ Polynomial.eval 0 F ≠ 0 ∧
      ∀ i, x i ≠ 0 → Polynomial.aeval (x i) F = 0 := by
  have := Fintype.ofFinite ι
  have hex : ∀ i, ∃ q : Polynomial ℤ,
      q.Monic ∧ (x i ≠ 0 → q.coeff 0 ≠ 0 ∧ Polynomial.aeval (x i) q = 0) := by
    intro i
    by_cases hi : x i ≠ 0
    · obtain ⟨q, hqm, hq0, hqeval⟩ :=
        hl_exists_monic_coeff_zero_ne_zero_of_isIntegral (x i) hi (hint i)
      exact ⟨q, hqm, fun _ => ⟨hq0, hqeval⟩⟩
    · exact ⟨1, Polynomial.monic_one, fun h => absurd h hi⟩
  choose Q hQm hQ using hex
  let s : Finset ι := Finset.univ.filter (fun i => x i ≠ 0)
  refine ⟨s.prod (fun i => Q i), ?_, ?_, ?_⟩
  · exact Polynomial.monic_prod_of_monic s _ (fun i _ => hQm i)
  · rw [Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hne : x i ≠ 0 := (Finset.mem_filter.mp hi).2
    have h := (hQ i hne).1
    rwa [Polynomial.coeff_zero_eq_eval_zero] at h
  · intro i hi
    have himem : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    have hQi : Polynomial.aeval (x i) (Q i) = 0 := (hQ i hi).2
    have hmap : Polynomial.aeval (x i) (s.prod (fun j => Q j))
        = s.prod (fun j => Polynomial.aeval (x i) (Q j)) := by
      rw [map_prod]
    rw [hmap]
    exact Finset.prod_eq_zero himem hQi

/-- Evaluating an integer `MvPolynomial` at integer casts is the cast of
the integer evaluation. -/
private theorem hl_aeval_intCast (n : ℕ) (Q : MvPolynomial (Fin n) ℤ)
    (e : Fin n → ℤ) :
    MvPolynomial.aeval (fun i => ((e i : ℤ) : ℂ)) Q
      = ((MvPolynomial.aeval e Q : ℤ) : ℂ) := by
  induction Q using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq, Int.cast_add]
  | mul_X p i hp => simp only [map_mul, MvPolynomial.aeval_X, hp, Int.cast_mul]

/-- Each elementary symmetric value at the roots is an integer cast
(Vieta's formula for the root multiset). -/
private theorem hl_esymm_aeval_roots_eq_intCast (n : ℕ) (a : Fin n → ℂ)
    (f : Polynomial ℤ)
    (hprod : Finset.prod Finset.univ
      (fun j => Polynomial.X - Polynomial.C (a j))
      = Polynomial.map (algebraMap ℤ ℂ) f)
    (k : ℕ) (hk : k ≤ n) :
    ∃ z : ℤ, MvPolynomial.aeval a (MvPolynomial.esymm (Fin n) ℤ k)
      = (z : ℂ) := by
  have hcard : (Multiset.map a Finset.univ.val).card = n := by
    rw [Multiset.card_map]
    change Finset.univ.card = n
    rw [Finset.card_univ, Fintype.card_fin]
  have hkk : n - (n - k) = k := Nat.sub_sub_self hk
  have hV := Multiset.prod_X_sub_C_coeff (Multiset.map a Finset.univ.val)
    (k := n - k) (by rw [hcard]; exact Nat.sub_le _ _)
  rw [hcard] at hV
  rw [hkk] at hV
  have hmap : (Multiset.map (fun t => Polynomial.X - Polynomial.C t)
        (Multiset.map a Finset.univ.val)).prod
      = Polynomial.map (algebraMap ℤ ℂ) f := by
    rw [Multiset.map_map]
    exact hprod
  rw [hmap] at hV
  have hneg : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
    rw [← mul_pow]
    norm_num
  have hsol : (Multiset.map a Finset.univ.val).esymm k
      = (-1 : ℂ) ^ k
        * (Polynomial.map (algebraMap ℤ ℂ) f).coeff (n - k) := by
    have h2 : (Multiset.map a Finset.univ.val).esymm k
        = (-1 : ℂ) ^ k * (((-1 : ℂ) ^ k)
          * (Multiset.map a Finset.univ.val).esymm k) := by
      rw [← mul_assoc, hneg, one_mul]
    rw [h2, ← hV]
  refine ⟨(-1) ^ k * f.coeff (n - k), ?_⟩
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) ℤ k a, hsol,
    Polynomial.coeff_map]
  have halg : (algebraMap ℤ ℂ) (f.coeff (n - k))
      = ((f.coeff (n - k) : ℤ) : ℂ) := by simp
  rw [halg]
  push_cast
  ring

/-- N4: a symmetric integer polynomial evaluated at the roots is an
integer cast (fundamental theorem of symmetric polynomials). -/
private theorem hl_symmetric_aeval_roots_eq_intCast (n : ℕ)
    (Φ : MvPolynomial (Fin n) ℤ) (hsym : Φ.IsSymmetric)
    (a : Fin n → ℂ) (f : Polynomial ℤ)
    (hprod : Finset.prod Finset.univ
      (fun j => Polynomial.X - Polynomial.C (a j))
      = Polynomial.map (algebraMap ℤ ℂ) f) :
    ∃ z : ℤ, MvPolynomial.aeval a Φ = (z : ℂ) := by
  obtain ⟨Q, hQ⟩ := MvPolynomial.esymmAlgHom_fin_surjective ℤ (n := n)
    (m := n) (le_refl n) ⟨Φ, hsym⟩
  have hΦ : Φ = MvPolynomial.aeval
      (fun i : Fin n ↦ MvPolynomial.esymm (Fin n) ℤ ((i : ℕ) + 1))
      Q := by
    have hval := congrArg Subtype.val hQ
    rw [MvPolynomial.esymmAlgHom_apply] at hval
    exact hval.symm
  have hex : ∀ i : Fin n, ∃ z : ℤ,
      MvPolynomial.aeval a (MvPolynomial.esymm (Fin n) ℤ ((i : ℕ) + 1))
        = (z : ℂ) := by
    intro i
    have hi : (i : ℕ) + 1 ≤ n := i.isLt
    exact hl_esymm_aeval_roots_eq_intCast n a f hprod ((i : ℕ) + 1) hi
  choose e he using hex
  have hcomp : MvPolynomial.aeval a Φ
      = MvPolynomial.aeval
        (fun i : Fin n ↦ MvPolynomial.aeval a
          (MvPolynomial.esymm (Fin n) ℤ ((i : ℕ) + 1))) Q := by
    rw [hΦ]
    have h := congrArg (fun F => F Q) (MvPolynomial.comp_aeval
      (fun i : Fin n ↦ MvPolynomial.esymm (Fin n) ℤ ((i : ℕ) + 1))
      (MvPolynomial.aeval a))
    simpa [AlgHom.comp_apply] using h
  rw [hcomp]
  simp only [he]
  exact ⟨MvPolynomial.aeval e Q, hl_aeval_intCast n Q e⟩

/-- Renaming the linear form of `u` by `σ` gives the linear form of
`u ∘ σ⁻¹`. -/
private theorem hl_rename_linearForm (n : ℕ) (κ : Type*)
    (lam : κ → ℤ) (u : Fin n → κ) (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.rename (⇑σ : Fin n → Fin n)
        (∑ j, MvPolynomial.C (lam (u j)) * MvPolynomial.X j)
      = ∑ j, MvPolynomial.C (lam ((u ∘ ⇑σ.symm) j))
        * MvPolynomial.X j := by
  have hre : (∑ j, MvPolynomial.C (lam (u j))
        * MvPolynomial.X (σ j))
      = ∑ j, MvPolynomial.C (lam (u (σ.symm j)))
        * MvPolynomial.X (σ (σ.symm j)) :=
    (Equiv.sum_comp σ.symm (fun j =>
      MvPolynomial.C (lam (u j)) * MvPolynomial.X (σ j))).symm
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      MvPolynomial.C (lam (u (σ.symm j)))
        * MvPolynomial.X (σ (σ.symm j))
      = MvPolynomial.C (lam ((u ∘ ⇑σ.symm) j))
        * MvPolynomial.X j := by
    intro j _
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  have hperm : (∑ j, MvPolynomial.C (lam (u j))
        * MvPolynomial.X (σ j))
      = ∑ j, MvPolynomial.C (lam ((u ∘ ⇑σ.symm) j))
        * MvPolynomial.X j :=
    hre.trans (Finset.sum_congr rfl hterm)
  have hdist : MvPolynomial.rename (⇑σ : Fin n → Fin n)
        (∑ j, MvPolynomial.C (lam (u j)) * MvPolynomial.X j)
      = ∑ j, MvPolynomial.C (lam (u j)) * MvPolynomial.X (σ j) := by
    have hterm2 : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        MvPolynomial.rename (⇑σ : Fin n → Fin n)
          (MvPolynomial.C (lam (u j)) * MvPolynomial.X j)
        = MvPolynomial.C (lam (u j)) * MvPolynomial.X (σ j) := by
      intro j _
      rw [map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X]
    rw [map_sum]
    exact Finset.sum_congr rfl hterm2
  exact hdist.trans hperm

/-- Evaluating the weighted power polynomial gives the weighted sum of
powers of the linear forms. -/
private theorem hl_aeval_weight_pow (n : ℕ) (κ : Type*) [Fintype κ]
    (W : (Fin n → κ) → ℤ) (lam : κ → ℤ) (a : Fin n → ℂ) (e : ℕ) :
    MvPolynomial.aeval a
        (∑ u : Fin n → κ, MvPolynomial.C (W u)
          * (∑ j, MvPolynomial.C (lam (u j)) * MvPolynomial.X j) ^ e)
      = ∑ u : Fin n → κ, ((W u : ℤ) : ℂ)
        * (∑ j, (((lam (u j) : ℤ)) : ℂ) * a j) ^ e := by
  have hterm : ∀ u ∈ (Finset.univ : Finset (Fin n → κ)),
      MvPolynomial.aeval a (MvPolynomial.C (W u)
        * (∑ j, MvPolynomial.C (lam (u j)) * MvPolynomial.X j) ^ e)
      = ((W u : ℤ) : ℂ)
        * (∑ j, (((lam (u j) : ℤ)) : ℂ) * a j) ^ e := by
    intro u _
    have hC : MvPolynomial.aeval a (MvPolynomial.C (W u))
        = ((W u : ℤ) : ℂ) := by
      rw [MvPolynomial.aeval_C]
      simp
    have hinner : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        MvPolynomial.aeval a
          (MvPolynomial.C (lam (u j)) * MvPolynomial.X j)
        = (((lam (u j) : ℤ)) : ℂ) * a j := by
      intro j _
      rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
      have halg : (algebraMap ℤ ℂ) (lam (u j))
          = (((lam (u j) : ℤ)) : ℂ) := by simp
      rw [halg]
    have hS : MvPolynomial.aeval a
          (∑ j, MvPolynomial.C (lam (u j)) * MvPolynomial.X j)
        = ∑ j, (((lam (u j) : ℤ)) : ℂ) * a j := by
      rw [MvPolynomial.aeval_sum]
      exact Finset.sum_congr rfl hinner
    rw [map_mul, map_pow, hC, hS]
  rw [MvPolynomial.aeval_sum]
  exact Finset.sum_congr rfl hterm

/-- N5, monomial case: weighted sums of powers of linear forms are
integer casts. -/
private theorem hl_sum_weight_pow_eq_intCast (n : ℕ) (κ : Type*)
    [Fintype κ] (W : (Fin n → κ) → ℤ)
    (hW : ∀ (σ : Equiv.Perm (Fin n)) (u : Fin n → κ), W (u ∘ σ) = W u)
    (lam : κ → ℤ) (a : Fin n → ℂ) (f : Polynomial ℤ)
    (hprod : Finset.prod Finset.univ
      (fun j => Polynomial.X - Polynomial.C (a j))
      = Polynomial.map (algebraMap ℤ ℂ) f)
    (e : ℕ) :
    ∃ z : ℤ, (∑ u : Fin n → κ, ((W u : ℤ) : ℂ)
      * (∑ j, (((lam (u j) : ℤ)) : ℂ) * a j) ^ e) = (z : ℂ) := by
  have hsym : (∑ u : Fin n → κ, MvPolynomial.C (W u)
      * (∑ j, MvPolynomial.C (lam (u j)) * MvPolynomial.X j)
        ^ e).IsSymmetric := by
    intro σ
    have hdist : MvPolynomial.rename (⇑σ : Fin n → Fin n)
          (∑ u : Fin n → κ, MvPolynomial.C (W u)
            * (∑ j, MvPolynomial.C (lam (u j)) * MvPolynomial.X j)
              ^ e)
        = ∑ u : Fin n → κ, MvPolynomial.C (W u)
          * (MvPolynomial.rename (⇑σ : Fin n → Fin n)
            (∑ j, MvPolynomial.C (lam (u j)) * MvPolynomial.X j))
            ^ e := by
      have hterm : ∀ u ∈ (Finset.univ : Finset (Fin n → κ)),
          MvPolynomial.rename (⇑σ : Fin n → Fin n)
            (MvPolynomial.C (W u)
              * (∑ j, MvPolynomial.C (lam (u j))
                * MvPolynomial.X j) ^ e)
          = MvPolynomial.C (W u)
            * (MvPolynomial.rename (⇑σ : Fin n → Fin n)
              (∑ j, MvPolynomial.C (lam (u j))
                * MvPolynomial.X j)) ^ e := by
        intro u _
        rw [map_mul, map_pow, MvPolynomial.rename_C]
      rw [map_sum]
      exact Finset.sum_congr rfl hterm
    rw [hdist]
    have hinner : ∀ u ∈ (Finset.univ : Finset (Fin n → κ)),
        MvPolynomial.C (W u)
          * (MvPolynomial.rename (⇑σ : Fin n → Fin n)
            (∑ j, MvPolynomial.C (lam (u j)) * MvPolynomial.X j))
            ^ e
        = MvPolynomial.C (W u)
          * (∑ j, MvPolynomial.C (lam ((u ∘ ⇑σ.symm) j))
            * MvPolynomial.X j) ^ e := by
      intro u _
      rw [hl_rename_linearForm]
    have hstep : (∑ u : Fin n → κ, MvPolynomial.C (W u)
          * (MvPolynomial.rename (⇑σ : Fin n → Fin n)
            (∑ j, MvPolynomial.C (lam (u j)) * MvPolynomial.X j))
            ^ e)
        = ∑ u : Fin n → κ, MvPolynomial.C (W u)
          * (∑ j, MvPolynomial.C (lam ((u ∘ ⇑σ.symm) j))
            * MvPolynomial.X j) ^ e :=
      Finset.sum_congr rfl hinner
    rw [hstep]
    let E : (Fin n → κ) ≃ (Fin n → κ) :=
      { toFun := fun v => v ∘ ⇑σ
        invFun := fun v => v ∘ ⇑σ.symm
        left_inv := fun v => funext fun j => by
          simp only [Function.comp_apply, Equiv.apply_symm_apply]
        right_inv := fun v => funext fun j => by
          simp only [Function.comp_apply, Equiv.symm_apply_apply] }
    have hEu : ∀ u : Fin n → κ, ⇑E.symm u = u ∘ ⇑σ.symm :=
      fun u => rfl
    have hmain : (∑ u : Fin n → κ, MvPolynomial.C (W (⇑E.symm u))
          * (∑ j, MvPolynomial.C (lam ((⇑E.symm u) j))
            * MvPolynomial.X j) ^ e)
        = ∑ u : Fin n → κ, MvPolynomial.C (W u)
          * (∑ j, MvPolynomial.C (lam (u j)) * MvPolynomial.X j)
            ^ e :=
      Equiv.sum_comp E.symm (fun v => MvPolynomial.C (W v)
        * (∑ j, MvPolynomial.C (lam (v j)) * MvPolynomial.X j) ^ e)
    have hcongr : (∑ u : Fin n → κ, MvPolynomial.C (W u)
          * (∑ j, MvPolynomial.C (lam ((u ∘ ⇑σ.symm) j))
            * MvPolynomial.X j) ^ e)
        = ∑ u : Fin n → κ, MvPolynomial.C (W (⇑E.symm u))
          * (∑ j, MvPolynomial.C (lam ((⇑E.symm u) j))
            * MvPolynomial.X j) ^ e := by
      have hterm : ∀ u ∈ (Finset.univ : Finset (Fin n → κ)),
          MvPolynomial.C (W u)
            * (∑ j, MvPolynomial.C (lam ((u ∘ ⇑σ.symm) j))
              * MvPolynomial.X j) ^ e
          = MvPolynomial.C (W (⇑E.symm u))
            * (∑ j, MvPolynomial.C (lam ((⇑E.symm u) j))
              * MvPolynomial.X j) ^ e := by
        intro u _
        rw [hEu u, hW σ.symm u]
      exact Finset.sum_congr rfl hterm
    exact hcongr.trans hmain
  obtain ⟨z, hz⟩ := hl_symmetric_aeval_roots_eq_intCast n _ hsym a f hprod
  rw [hl_aeval_weight_pow] at hz
  exact ⟨z, hz⟩

/-- N5: weighted sums of integer-polynomial values at linear forms are
integer casts. -/
private theorem hl_sum_weight_aeval_linearForm_eq_intCast (n : ℕ)
    (κ : Type*) [Fintype κ] (W : (Fin n → κ) → ℤ)
    (hW : ∀ (σ : Equiv.Perm (Fin n)) (u : Fin n → κ), W (u ∘ σ) = W u)
    (lam : κ → ℤ) (a : Fin n → ℂ) (f : Polynomial ℤ)
    (hprod : Finset.prod Finset.univ
      (fun j => Polynomial.X - Polynomial.C (a j))
      = Polynomial.map (algebraMap ℤ ℂ) f)
    (g : Polynomial ℤ) :
    ∃ z : ℤ, (∑ u : Fin n → κ, ((W u : ℤ) : ℂ)
      * Polynomial.aeval (∑ j, (((lam (u j) : ℤ)) : ℂ) * a j) g)
      = (z : ℂ) := by
  have hex : ∀ e : ℕ, ∃ z : ℤ, (∑ u : Fin n → κ, ((W u : ℤ) : ℂ)
      * (∑ j, (((lam (u j) : ℤ)) : ℂ) * a j) ^ e) = (z : ℂ) :=
    fun e => hl_sum_weight_pow_eq_intCast n κ W hW lam a f hprod e
  choose z hz using hex
  refine ⟨∑ e ∈ Finset.range (g.natDegree + 1), g.coeff e * z e, ?_⟩
  have h1 : (∑ u : Fin n → κ, ((W u : ℤ) : ℂ)
        * Polynomial.aeval (∑ j, (((lam (u j) : ℤ)) : ℂ) * a j) g)
      = ∑ u : Fin n → κ, ∑ e ∈ Finset.range (g.natDegree + 1),
        ((W u : ℤ) : ℂ) * ((((g.coeff e : ℤ)) : ℂ)
          * (∑ j, (((lam (u j) : ℤ)) : ℂ) * a j) ^ e) := by
    have hterm : ∀ u ∈ (Finset.univ : Finset (Fin n → κ)),
        ((W u : ℤ) : ℂ)
          * Polynomial.aeval (∑ j, (((lam (u j) : ℤ)) : ℂ) * a j) g
        = ∑ e ∈ Finset.range (g.natDegree + 1),
          ((W u : ℤ) : ℂ) * ((((g.coeff e : ℤ)) : ℂ)
            * (∑ j, (((lam (u j) : ℤ)) : ℂ) * a j) ^ e) := by
      intro u _
      have hae : Polynomial.aeval
            (∑ j, (((lam (u j) : ℤ)) : ℂ) * a j) g
          = ∑ e ∈ Finset.range (g.natDegree + 1),
            ((((g.coeff e : ℤ)) : ℂ)
              * (∑ j, (((lam (u j) : ℤ)) : ℂ) * a j) ^ e) := by
        rw [Polynomial.aeval_eq_sum_range]
        have hterm2 : ∀ e ∈ Finset.range (g.natDegree + 1),
            (g.coeff e : ℤ)
              • (∑ j, (((lam (u j) : ℤ)) : ℂ) * a j) ^ e
            = ((((g.coeff e : ℤ)) : ℂ)
              * (∑ j, (((lam (u j) : ℤ)) : ℂ) * a j) ^ e) := by
          intro e _
          rw [zsmul_eq_mul]
        exact Finset.sum_congr rfl hterm2
      rw [hae, Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  have h2 : (∑ u : Fin n → κ, ∑ e ∈ Finset.range (g.natDegree + 1),
        ((W u : ℤ) : ℂ) * ((((g.coeff e : ℤ)) : ℂ)
          * (∑ j, (((lam (u j) : ℤ)) : ℂ) * a j) ^ e))
      = ∑ e ∈ Finset.range (g.natDegree + 1),
        ((((g.coeff e : ℤ)) : ℂ)
          * (∑ u : Fin n → κ, ((W u : ℤ) : ℂ)
            * (∑ j, (((lam (u j) : ℤ)) : ℂ) * a j) ^ e)) := by
    rw [Finset.sum_comm]
    have hterm : ∀ e ∈ Finset.range (g.natDegree + 1),
        (∑ u : Fin n → κ, ((W u : ℤ) : ℂ) * ((((g.coeff e : ℤ)) : ℂ)
            * (∑ j, (((lam (u j) : ℤ)) : ℂ) * a j) ^ e))
        = ((((g.coeff e : ℤ)) : ℂ)
            * (∑ u : Fin n → κ, ((W u : ℤ) : ℂ)
              * (∑ j, (((lam (u j) : ℤ)) : ℂ) * a j) ^ e)) := by
      intro e _
      rw [Finset.mul_sum]
      have hterm2 : ∀ u ∈ (Finset.univ : Finset (Fin n → κ)),
          ((W u : ℤ) : ℂ) * ((((g.coeff e : ℤ)) : ℂ)
            * (∑ j, (((lam (u j) : ℤ)) : ℂ) * a j) ^ e)
          = ((((g.coeff e : ℤ)) : ℂ) * (((W u : ℤ) : ℂ)
            * (∑ j, (((lam (u j) : ℤ)) : ℂ) * a j) ^ e)) := by
        intro u _
        ring
      exact Finset.sum_congr rfl hterm2
    exact Finset.sum_congr rfl hterm
  have h3 : (∑ e ∈ Finset.range (g.natDegree + 1),
        ((((g.coeff e : ℤ)) : ℂ)
          * (∑ u : Fin n → κ, ((W u : ℤ) : ℂ)
            * (∑ j, (((lam (u j) : ℤ)) : ℂ) * a j) ^ e)))
      = (((∑ e ∈ Finset.range (g.natDegree + 1), g.coeff e * z e
        : ℤ)) : ℂ) := by
    have hterm : ∀ e ∈ Finset.range (g.natDegree + 1),
        ((((g.coeff e : ℤ)) : ℂ)
          * (∑ u : Fin n → κ, ((W u : ℤ) : ℂ)
            * (∑ j, (((lam (u j) : ℤ)) : ℂ) * a j) ^ e))
        = ((((g.coeff e * z e : ℤ))) : ℂ) := by
      intro e _
      rw [hz e, Int.cast_mul]
    have hstep : (∑ e ∈ Finset.range (g.natDegree + 1),
          ((((g.coeff e : ℤ)) : ℂ)
            * (∑ u : Fin n → κ, ((W u : ℤ) : ℂ)
              * (∑ j, (((lam (u j) : ℤ)) : ℂ) * a j) ^ e)))
        = ∑ e ∈ Finset.range (g.natDegree + 1),
          (((g.coeff e * z e : ℤ)) : ℂ) :=
      Finset.sum_congr rfl hterm
    rw [hstep, Int.cast_sum]
  exact h1.trans (h2.trans h3)

open Classical in
/-- N6: some fiber sum of the unsquared weights is nonzero (the group
ring `ℤ[ℂ]` has no zero divisors). -/
private theorem hl_exists_fiber_sum_ne_zero (n : ℕ) (a : Fin n → ℂ)
    (ha : ∀ j, a j ≠ 0) (B : Polynomial ℤ) (hB : B ≠ 0) :
    ∃ z : ℂ, (∑ k ∈ Finset.univ.filter
        (fun k : Fin n → Fin (B.natDegree + 1) =>
          (∑ j, (((k j).val : ℂ) * a j)) = z),
        Finset.prod Finset.univ
          (fun j => B.coeff (k j).val)) ≠ 0 := by
  have hlead : B.coeff B.natDegree ≠ 0 := by
    have h := Polynomial.leadingCoeff_ne_zero.mpr hB
    rwa [Polynomial.leadingCoeff] at h
  have hEj : ∀ j : Fin n,
      (∑ i : Fin (B.natDegree + 1), AddMonoidAlgebra.single
        ((((i.val : ℕ)) : ℂ) * a j) (B.coeff i.val)) ≠ 0 := by
    intro j
    have hiff : ∀ i : Fin (B.natDegree + 1),
        (((((i.val : ℕ)) : ℂ) * a j)
          = ((((B.natDegree : ℕ)) : ℂ) * a j))
        ↔ i = ⟨B.natDegree, Nat.lt_succ_self B.natDegree⟩ := by
      intro i
      constructor
      · intro hpt
        have h2 : (((i.val : ℕ)) : ℂ)
            = (((B.natDegree : ℕ)) : ℂ) :=
          mul_right_cancel₀ (ha j) hpt
        have h3 : i.val = B.natDegree := by exact_mod_cast h2
        exact Fin.ext h3
      · intro hpt
        simp only [hpt]
    have hsum : (∑ i : Fin (B.natDegree + 1),
          (AddMonoidAlgebra.single ((((i.val : ℕ)) : ℂ) * a j)
            (B.coeff i.val)).coeff
            ((((B.natDegree : ℕ)) : ℂ) * a j))
        = B.coeff B.natDegree := by
      have h0 : ∀ i ∈ (Finset.univ : Finset (Fin (B.natDegree + 1))),
          i ≠ ⟨B.natDegree, Nat.lt_succ_self B.natDegree⟩ →
          (AddMonoidAlgebra.single ((((i.val : ℕ)) : ℂ) * a j)
            (B.coeff i.val)).coeff
            ((((B.natDegree : ℕ)) : ℂ) * a j) = 0 := by
        intro i _ hi
        rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
          ite_eq_right]
        intro hcon
        exact hi ((hiff i).mp hcon)
      have h1 : (⟨B.natDegree, Nat.lt_succ_self B.natDegree⟩
            : Fin (B.natDegree + 1)) ∉ Finset.univ →
          (AddMonoidAlgebra.single
              (((((⟨B.natDegree, Nat.lt_succ_self B.natDegree⟩
                : Fin (B.natDegree + 1)).val : ℕ)) : ℂ) * a j)
            (B.coeff (⟨B.natDegree, Nat.lt_succ_self B.natDegree⟩
              : Fin (B.natDegree + 1)).val)).coeff
            ((((B.natDegree : ℕ)) : ℂ) * a j) = 0 := by
        intro hcon
        exact absurd (Finset.mem_univ _) hcon
      have hmain := Finset.sum_eq_single
        (⟨B.natDegree, Nat.lt_succ_self B.natDegree⟩
          : Fin (B.natDegree + 1)) h0 h1
      have htop : (AddMonoidAlgebra.single
            (((((⟨B.natDegree, Nat.lt_succ_self B.natDegree⟩
              : Fin (B.natDegree + 1)).val : ℕ)) : ℂ) * a j)
          (B.coeff (⟨B.natDegree, Nat.lt_succ_self B.natDegree⟩
            : Fin (B.natDegree + 1)).val)).coeff
          ((((B.natDegree : ℕ)) : ℂ) * a j)
          = B.coeff B.natDegree := by
        rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
          ite_eq_left rfl]
      exact hmain.trans htop
    have hcoeff_eq : (∑ i : Fin (B.natDegree + 1),
          AddMonoidAlgebra.single ((((i.val : ℕ)) : ℂ) * a j)
            (B.coeff i.val)).coeff
          ((((B.natDegree : ℕ)) : ℂ) * a j)
        = B.coeff B.natDegree := by
      rw [AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
      exact hsum
    intro h0j
    rw [h0j] at hcoeff_eq
    simp only [AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply] at hcoeff_eq
    exact hlead hcoeff_eq.symm
  have hP : (∏ j : Fin n, ∑ i : Fin (B.natDegree + 1),
      AddMonoidAlgebra.single ((((i.val : ℕ)) : ℂ) * a j)
        (B.coeff i.val)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => hEj j)
  have hexpand1 : (∏ j : Fin n, ∑ i : Fin (B.natDegree + 1),
        AddMonoidAlgebra.single ((((i.val : ℕ)) : ℂ) * a j)
          (B.coeff i.val))
      = ∑ k : Fin n → Fin (B.natDegree + 1), ∏ j,
        AddMonoidAlgebra.single ((((k j).val : ℕ) : ℂ) * a j)
          (B.coeff (k j).val) :=
    Fintype.prod_sum _
  have hsingle : ∀ k ∈ (Finset.univ
      : Finset (Fin n → Fin (B.natDegree + 1))),
      (∏ j, AddMonoidAlgebra.single ((((k j).val : ℕ) : ℂ) * a j)
        (B.coeff (k j).val))
      = AddMonoidAlgebra.single
        (∑ j, ((((k j).val : ℕ)) : ℂ) * a j)
        (∏ j, B.coeff (k j).val) := by
    intro k _
    rw [AddMonoidAlgebra.prod_single]
  have hexpand : (∏ j : Fin n, ∑ i : Fin (B.natDegree + 1),
        AddMonoidAlgebra.single ((((i.val : ℕ)) : ℂ) * a j)
          (B.coeff i.val))
      = ∑ k : Fin n → Fin (B.natDegree + 1),
        AddMonoidAlgebra.single
          (∑ j, ((((k j).val : ℕ)) : ℂ) * a j)
          (∏ j, B.coeff (k j).val) :=
    hexpand1.trans (Finset.sum_congr rfl hsingle)
  have hfiber : ∀ z : ℂ, (∑ k ∈ Finset.univ.filter
          (fun k : Fin n → Fin (B.natDegree + 1) =>
            (∑ j, ((((k j).val : ℕ)) : ℂ) * a j) = z),
          Finset.prod Finset.univ (fun j => B.coeff (k j).val))
        = (∑ k : Fin n → Fin (B.natDegree + 1),
          AddMonoidAlgebra.single
            (∑ j, ((((k j).val : ℕ)) : ℂ) * a j)
            (∏ j, B.coeff (k j).val)).coeff z := by
    intro z
    have hfilter : (∑ k ∈ Finset.univ.filter
            (fun k : Fin n → Fin (B.natDegree + 1) =>
              (∑ j, ((((k j).val : ℕ)) : ℂ) * a j) = z),
            Finset.prod Finset.univ (fun j => B.coeff (k j).val))
          = ∑ k : Fin n → Fin (B.natDegree + 1),
            (if (∑ j, ((((k j).val : ℕ)) : ℂ) * a j) = z
              then Finset.prod Finset.univ
                (fun j => B.coeff (k j).val)
              else 0) :=
      Finset.sum_filter _ _
    rw [hfilter, AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
    have hterm : ∀ k ∈ (Finset.univ
        : Finset (Fin n → Fin (B.natDegree + 1))),
        (if (∑ j, ((((k j).val : ℕ)) : ℂ) * a j) = z
          then Finset.prod Finset.univ (fun j => B.coeff (k j).val)
          else 0)
        = (AddMonoidAlgebra.single
          (∑ j, ((((k j).val : ℕ)) : ℂ) * a j)
          (∏ j, B.coeff (k j).val)).coeff z := by
      intro k _
      rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    exact Finset.sum_congr rfl hterm
  by_contra hcon
  push Not at hcon
  apply hP
  rw [hexpand]
  have hzero : (∑ k : Fin n → Fin (B.natDegree + 1),
      AddMonoidAlgebra.single
        (∑ j, ((((k j).val : ℕ)) : ℂ) * a j)
        (∏ j, B.coeff (k j).val)).coeff = 0 := by
    ext z
    rw [Finsupp.zero_apply]
    rw [← hfiber z]
    exact hcon z
  exact AddMonoidAlgebra.coeff_eq_zero.mp hzero

open Classical in
/-- N7: the zero-fiber weight is positive (a sum of squares). -/
private theorem hl_zero_fiber_weight_pos (n : ℕ) (a : Fin n → ℂ)
    (ha : ∀ j, a j ≠ 0) (B : Polynomial ℤ) (hB : B ≠ 0) :
    0 < ∑ u ∈ Finset.univ.filter
      (fun u : Fin n → Fin (B.natDegree + 1) × Fin (B.natDegree + 1) =>
        (∑ j, (((((u j).1.val : ℤ) - ((u j).2.val : ℤ) : ℤ) : ℂ)
          * a j)) = 0),
      Finset.prod Finset.univ
        (fun j => B.coeff (u j).1.val * B.coeff (u j).2.val) := by
  let E := Equiv.arrowProdEquivProdArrow (Fin n)
    (fun _ => Fin (B.natDegree + 1)) (fun _ => Fin (B.natDegree + 1))
  have hre : (∑ u : Fin n → Fin (B.natDegree + 1)
          × Fin (B.natDegree + 1),
        (if (∑ j, (((((u j).1.val : ℤ) - ((u j).2.val : ℤ) : ℤ)
            : ℂ) * a j)) = 0
          then Finset.prod Finset.univ
            (fun j => B.coeff (u j).1.val * B.coeff (u j).2.val)
          else 0))
      = ∑ p : (Fin n → Fin (B.natDegree + 1))
          × (Fin n → Fin (B.natDegree + 1)),
        (if (∑ j, (((((⇑E.symm p j).1.val : ℤ)
            - ((⇑E.symm p j).2.val : ℤ) : ℤ) : ℂ) * a j)) = 0
          then Finset.prod Finset.univ (fun j =>
            B.coeff (⇑E.symm p j).1.val
              * B.coeff (⇑E.symm p j).2.val)
          else 0) :=
    (Equiv.sum_comp E.symm _).symm
  have hpt : (∑ p : (Fin n → Fin (B.natDegree + 1))
        × (Fin n → Fin (B.natDegree + 1)),
      (if (∑ j, (((((⇑E.symm p j).1.val : ℤ)
          - ((⇑E.symm p j).2.val : ℤ) : ℤ) : ℂ) * a j)) = 0
        then Finset.prod Finset.univ (fun j =>
          B.coeff (⇑E.symm p j).1.val
            * B.coeff (⇑E.symm p j).2.val)
        else 0))
      = ∑ k : Fin n → Fin (B.natDegree + 1),
        ∑ l : Fin n → Fin (B.natDegree + 1),
        (if (∑ j, (((((⇑E.symm (k, l) j).1.val : ℤ)
            - ((⇑E.symm (k, l) j).2.val : ℤ) : ℤ) : ℂ) * a j))
            = 0
          then Finset.prod Finset.univ (fun j =>
            B.coeff (⇑E.symm (k, l) j).1.val
              * B.coeff (⇑E.symm (k, l) j).2.val)
          else 0) :=
    Fintype.sum_prod_type _
  have hγ : ∀ k l : Fin n → Fin (B.natDegree + 1),
      (∑ j, (((((⇑E.symm (k, l) j).1.val : ℤ)
          - ((⇑E.symm (k, l) j).2.val : ℤ) : ℤ) : ℂ) * a j))
      = (∑ j, (((k j).val : ℂ) * a j))
        - (∑ j, (((l j).val : ℂ) * a j)) := by
    intro k l
    change (∑ j, (((((k j).val : ℤ) - ((l j).val : ℤ) : ℤ) : ℂ)
        * a j))
      = (∑ j, (((k j).val : ℂ) * a j))
        - (∑ j, (((l j).val : ℂ) * a j))
    rw [← Finset.sum_sub_distrib]
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        (((((k j).val : ℤ) - ((l j).val : ℤ) : ℤ) : ℂ) * a j)
        = ((((k j).val : ℂ) * a j) - (((l j).val : ℂ) * a j)) := by
      intro j _
      push_cast
      ring
    exact Finset.sum_congr rfl hterm
  have hw : ∀ k l : Fin n → Fin (B.natDegree + 1),
      Finset.prod Finset.univ (fun j =>
          B.coeff (⇑E.symm (k, l) j).1.val
            * B.coeff (⇑E.symm (k, l) j).2.val)
      = (Finset.prod Finset.univ (fun j => B.coeff (k j).val))
        * (Finset.prod Finset.univ
          (fun j => B.coeff (l j).val)) := by
    intro k l
    change Finset.prod Finset.univ (fun j =>
        B.coeff (k j).val * B.coeff (l j).val)
      = (Finset.prod Finset.univ (fun j => B.coeff (k j).val))
        * (Finset.prod Finset.univ (fun j => B.coeff (l j).val))
    rw [Finset.prod_mul_distrib]
  have hfilter : (∑ u ∈ Finset.univ.filter
        (fun u : Fin n → Fin (B.natDegree + 1)
            × Fin (B.natDegree + 1) =>
          (∑ j, (((((u j).1.val : ℤ) - ((u j).2.val : ℤ) : ℤ)
            : ℂ) * a j)) = 0),
        Finset.prod Finset.univ
          (fun j => B.coeff (u j).1.val * B.coeff (u j).2.val))
      = ∑ u : Fin n → Fin (B.natDegree + 1)
          × Fin (B.natDegree + 1),
        (if (∑ j, (((((u j).1.val : ℤ) - ((u j).2.val : ℤ) : ℤ)
            : ℂ) * a j)) = 0
          then Finset.prod Finset.univ
            (fun j => B.coeff (u j).1.val * B.coeff (u j).2.val)
          else 0) :=
    Finset.sum_filter _ _
  have hstep1 : (∑ u ∈ Finset.univ.filter
        (fun u : Fin n → Fin (B.natDegree + 1)
            × Fin (B.natDegree + 1) =>
          (∑ j, (((((u j).1.val : ℤ) - ((u j).2.val : ℤ) : ℤ)
            : ℂ) * a j)) = 0),
        Finset.prod Finset.univ
          (fun j => B.coeff (u j).1.val * B.coeff (u j).2.val))
      = ∑ k : Fin n → Fin (B.natDegree + 1),
        ∑ l : Fin n → Fin (B.natDegree + 1),
        (if (∑ j, (((l j).val : ℂ) * a j))
            = (∑ j, (((k j).val : ℂ) * a j))
          then (Finset.prod Finset.univ (fun j => B.coeff (k j).val))
            * (Finset.prod Finset.univ (fun j => B.coeff (l j).val))
          else 0) := by
    rw [hfilter, hre, hpt]
    have hterm : ∀ k ∈ (Finset.univ
        : Finset (Fin n → Fin (B.natDegree + 1))),
        (∑ l : Fin n → Fin (B.natDegree + 1),
          (if (∑ j, (((((⇑E.symm (k, l) j).1.val : ℤ)
              - ((⇑E.symm (k, l) j).2.val : ℤ) : ℤ) : ℂ) * a j))
              = 0
            then Finset.prod Finset.univ (fun j =>
              B.coeff (⇑E.symm (k, l) j).1.val
                * B.coeff (⇑E.symm (k, l) j).2.val)
            else 0))
        = ∑ l : Fin n → Fin (B.natDegree + 1),
          (if (∑ j, (((l j).val : ℂ) * a j))
              = (∑ j, (((k j).val : ℂ) * a j))
            then (Finset.prod Finset.univ
                (fun j => B.coeff (k j).val))
              * (Finset.prod Finset.univ
                (fun j => B.coeff (l j).val))
            else 0) := by
      intro k _
      have hterm2 : ∀ l ∈ (Finset.univ
          : Finset (Fin n → Fin (B.natDegree + 1))),
          (if (∑ j, (((((⇑E.symm (k, l) j).1.val : ℤ)
                - ((⇑E.symm (k, l) j).2.val : ℤ) : ℤ) : ℂ)
                * a j)) = 0
              then Finset.prod Finset.univ (fun j =>
                B.coeff (⇑E.symm (k, l) j).1.val
                  * B.coeff (⇑E.symm (k, l) j).2.val)
              else 0)
          = (if (∑ j, (((l j).val : ℂ) * a j))
                = (∑ j, (((k j).val : ℂ) * a j))
              then (Finset.prod Finset.univ
                  (fun j => B.coeff (k j).val))
                * (Finset.prod Finset.univ
                  (fun j => B.coeff (l j).val))
              else 0) := by
        intro l _
        rw [hγ k l, hw k l]
        have hiff : ((∑ j, (((k j).val : ℂ) * a j))
            - (∑ j, (((l j).val : ℂ) * a j)) = 0)
            ↔ ((∑ j, (((l j).val : ℂ) * a j))
              = (∑ j, (((k j).val : ℂ) * a j))) :=
          sub_eq_zero.trans ⟨Eq.symm, Eq.symm⟩
        simp only [hiff]
      exact Finset.sum_congr rfl hterm2
    exact Finset.sum_congr rfl hterm
  have hinner : ∀ k : Fin n → Fin (B.natDegree + 1),
      (∑ l : Fin n → Fin (B.natDegree + 1),
        (if (∑ j, (((l j).val : ℂ) * a j))
            = (∑ j, (((k j).val : ℂ) * a j))
          then (Finset.prod Finset.univ (fun j => B.coeff (k j).val))
            * (Finset.prod Finset.univ (fun j => B.coeff (l j).val))
          else 0))
      = (Finset.prod Finset.univ (fun j => B.coeff (k j).val))
        * (∑ l ∈ Finset.univ.filter
          (fun l : Fin n → Fin (B.natDegree + 1) =>
            (∑ j, (((l j).val : ℂ) * a j))
              = (∑ j, (((k j).val : ℂ) * a j))),
          Finset.prod Finset.univ (fun j => B.coeff (l j).val)) := by
    intro k
    have hfilter2 : (∑ l : Fin n → Fin (B.natDegree + 1),
          (if (∑ j, (((l j).val : ℂ) * a j))
              = (∑ j, (((k j).val : ℂ) * a j))
            then (Finset.prod Finset.univ
                (fun j => B.coeff (k j).val))
              * (Finset.prod Finset.univ
                (fun j => B.coeff (l j).val))
            else 0))
        = ∑ l ∈ Finset.univ.filter
          (fun l : Fin n → Fin (B.natDegree + 1) =>
            (∑ j, (((l j).val : ℂ) * a j))
              = (∑ j, (((k j).val : ℂ) * a j))),
          (Finset.prod Finset.univ (fun j => B.coeff (k j).val))
            * (Finset.prod Finset.univ
              (fun j => B.coeff (l j).val)) :=
      (Finset.sum_filter _ _).symm
    rw [hfilter2, Finset.mul_sum]
  have hfib : (∑ z ∈ Finset.univ.image
        (fun k : Fin n → Fin (B.natDegree + 1) =>
          (∑ j, (((k j).val : ℂ) * a j))),
        ∑ k ∈ Finset.univ.filter
          (fun k : Fin n → Fin (B.natDegree + 1) =>
            (∑ j, (((k j).val : ℂ) * a j)) = z),
          (Finset.prod Finset.univ (fun j => B.coeff (k j).val))
            * (∑ l ∈ Finset.univ.filter
              (fun l : Fin n → Fin (B.natDegree + 1) =>
                (∑ j, (((l j).val : ℂ) * a j))
                  = (∑ j, (((k j).val : ℂ) * a j))),
              Finset.prod Finset.univ (fun j => B.coeff (l j).val)))
      = ∑ k : Fin n → Fin (B.natDegree + 1),
        (Finset.prod Finset.univ (fun j => B.coeff (k j).val))
          * (∑ l ∈ Finset.univ.filter
            (fun l : Fin n → Fin (B.natDegree + 1) =>
              (∑ j, (((l j).val : ℂ) * a j))
                = (∑ j, (((k j).val : ℂ) * a j))),
            Finset.prod Finset.univ (fun j => B.coeff (l j).val)) :=
    Finset.sum_fiberwise_of_maps_to
      (fun k _ => Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩) _
  have h1 : ∀ z : ℂ, (∑ k ∈ Finset.univ.filter
          (fun k : Fin n → Fin (B.natDegree + 1) =>
            (∑ j, (((k j).val : ℂ) * a j)) = z),
          (Finset.prod Finset.univ (fun j => B.coeff (k j).val))
            * (∑ l ∈ Finset.univ.filter
              (fun l : Fin n → Fin (B.natDegree + 1) =>
                (∑ j, (((l j).val : ℂ) * a j))
                  = (∑ j, (((k j).val : ℂ) * a j))),
              Finset.prod Finset.univ (fun j => B.coeff (l j).val)))
        = (∑ k ∈ Finset.univ.filter
            (fun k : Fin n → Fin (B.natDegree + 1) =>
              (∑ j, (((k j).val : ℂ) * a j)) = z),
            Finset.prod Finset.univ (fun j => B.coeff (k j).val))
          * (∑ k ∈ Finset.univ.filter
            (fun k : Fin n → Fin (B.natDegree + 1) =>
              (∑ j, (((k j).val : ℂ) * a j)) = z),
            Finset.prod Finset.univ (fun j => B.coeff (k j).val)) := by
    intro z
    have h2 : (∑ k ∈ Finset.univ.filter
            (fun k : Fin n → Fin (B.natDegree + 1) =>
              (∑ j, (((k j).val : ℂ) * a j)) = z),
            (Finset.prod Finset.univ (fun j => B.coeff (k j).val))
              * (∑ l ∈ Finset.univ.filter
                (fun l : Fin n → Fin (B.natDegree + 1) =>
                  (∑ j, (((l j).val : ℂ) * a j))
                    = (∑ j, (((k j).val : ℂ) * a j))),
                Finset.prod Finset.univ
                  (fun j => B.coeff (l j).val)))
          = (∑ k ∈ Finset.univ.filter
              (fun k : Fin n → Fin (B.natDegree + 1) =>
                (∑ j, (((k j).val : ℂ) * a j)) = z),
              Finset.prod Finset.univ (fun j => B.coeff (k j).val))
            * (∑ k ∈ Finset.univ.filter
              (fun k : Fin n → Fin (B.natDegree + 1) =>
                (∑ j, (((k j).val : ℂ) * a j)) = z),
              Finset.prod Finset.univ (fun j => B.coeff (k j).val)) := by
      rw [Finset.sum_mul]
      have hterm : ∀ k ∈ Finset.univ.filter
            (fun k : Fin n → Fin (B.natDegree + 1) =>
              (∑ j, (((k j).val : ℂ) * a j)) = z),
            (Finset.prod Finset.univ (fun j => B.coeff (k j).val))
              * (∑ l ∈ Finset.univ.filter
                (fun l : Fin n → Fin (B.natDegree + 1) =>
                  (∑ j, (((l j).val : ℂ) * a j))
                    = (∑ j, (((k j).val : ℂ) * a j))),
                Finset.prod Finset.univ
                  (fun j => B.coeff (l j).val))
            = (Finset.prod Finset.univ (fun j => B.coeff (k j).val))
              * (∑ l ∈ Finset.univ.filter
                (fun l : Fin n → Fin (B.natDegree + 1) =>
                  (∑ j, (((l j).val : ℂ) * a j)) = z),
                Finset.prod Finset.univ
                  (fun j => B.coeff (l j).val)) := by
        intro k hk
        have hkz : (∑ j, (((k j).val : ℂ) * a j)) = z :=
          (Finset.mem_filter.mp hk).2
        rw [hkz]
      exact Finset.sum_congr rfl hterm
    rw [h2]
  have hgroup : (∑ k : Fin n → Fin (B.natDegree + 1),
        (Finset.prod Finset.univ (fun j => B.coeff (k j).val))
          * (∑ l ∈ Finset.univ.filter
            (fun l : Fin n → Fin (B.natDegree + 1) =>
              (∑ j, (((l j).val : ℂ) * a j))
                = (∑ j, (((k j).val : ℂ) * a j))),
            Finset.prod Finset.univ (fun j => B.coeff (l j).val)))
      = ∑ z ∈ Finset.univ.image
        (fun k : Fin n → Fin (B.natDegree + 1) =>
          (∑ j, (((k j).val : ℂ) * a j))),
        (∑ k ∈ Finset.univ.filter
            (fun k : Fin n → Fin (B.natDegree + 1) =>
              (∑ j, (((k j).val : ℂ) * a j)) = z),
            Finset.prod Finset.univ (fun j => B.coeff (k j).val))
          * (∑ k ∈ Finset.univ.filter
            (fun k : Fin n → Fin (B.natDegree + 1) =>
              (∑ j, (((k j).val : ℂ) * a j)) = z),
            Finset.prod Finset.univ (fun j => B.coeff (k j).val)) := by
    rw [← hfib]
    exact Finset.sum_congr rfl (fun z _ => h1 z)
  obtain ⟨z0, hz0⟩ := hl_exists_fiber_sum_ne_zero n a ha B hB
  have hz0mem : z0 ∈ Finset.univ.image
      (fun k : Fin n → Fin (B.natDegree + 1) =>
        (∑ j, (((k j).val : ℂ) * a j))) := by
    by_contra hcon
    apply hz0
    have hemp : Finset.univ.filter
          (fun k : Fin n → Fin (B.natDegree + 1) =>
            (∑ j, (((k j).val : ℂ) * a j)) = z0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro k _ hkz
      apply hcon
      rw [Finset.mem_image]
      exact ⟨k, Finset.mem_univ k, hkz⟩
    rw [hemp, Finset.sum_empty]
  have hpos : 0 < ∑ z ∈ Finset.univ.image
      (fun k : Fin n → Fin (B.natDegree + 1) =>
        (∑ j, (((k j).val : ℂ) * a j))),
      (∑ k ∈ Finset.univ.filter
          (fun k : Fin n → Fin (B.natDegree + 1) =>
            (∑ j, (((k j).val : ℂ) * a j)) = z),
          Finset.prod Finset.univ (fun j => B.coeff (k j).val))
        * (∑ k ∈ Finset.univ.filter
          (fun k : Fin n → Fin (B.natDegree + 1) =>
            (∑ j, (((k j).val : ℂ) * a j)) = z),
          Finset.prod Finset.univ (fun j => B.coeff (k j).val)) :=
    Finset.sum_pos' (fun z _ => mul_self_nonneg _)
      ⟨z0, hz0mem, mul_self_pos.mpr hz0⟩
  have hkk : (∑ k : Fin n → Fin (B.natDegree + 1),
        ∑ l : Fin n → Fin (B.natDegree + 1),
        (if (∑ j, (((l j).val : ℂ) * a j))
            = (∑ j, (((k j).val : ℂ) * a j))
          then (Finset.prod Finset.univ (fun j => B.coeff (k j).val))
            * (Finset.prod Finset.univ (fun j => B.coeff (l j).val))
          else 0))
      = ∑ k : Fin n → Fin (B.natDegree + 1),
        (Finset.prod Finset.univ (fun j => B.coeff (k j).val))
          * (∑ l ∈ Finset.univ.filter
            (fun l : Fin n → Fin (B.natDegree + 1) =>
              (∑ j, (((l j).val : ℂ) * a j))
                = (∑ j, (((k j).val : ℂ) * a j))),
            Finset.prod Finset.univ (fun j => B.coeff (l j).val)) :=
    Finset.sum_congr rfl (fun k _ => hinner k)
  have hfinal : (∑ u ∈ Finset.univ.filter
        (fun u : Fin n → Fin (B.natDegree + 1)
            × Fin (B.natDegree + 1) =>
          (∑ j, (((((u j).1.val : ℤ) - ((u j).2.val : ℤ) : ℤ)
            : ℂ) * a j)) = 0),
        Finset.prod Finset.univ
          (fun j => B.coeff (u j).1.val * B.coeff (u j).2.val))
      = ∑ z ∈ Finset.univ.image
        (fun k : Fin n → Fin (B.natDegree + 1) =>
          (∑ j, (((k j).val : ℂ) * a j))),
        (∑ k ∈ Finset.univ.filter
            (fun k : Fin n → Fin (B.natDegree + 1) =>
              (∑ j, (((k j).val : ℂ) * a j)) = z),
            Finset.prod Finset.univ (fun j => B.coeff (k j).val))
          * (∑ k ∈ Finset.univ.filter
            (fun k : Fin n → Fin (B.natDegree + 1) =>
              (∑ j, (((k j).val : ℂ) * a j)) = z),
            Finset.prod Finset.univ (fun j => B.coeff (k j).val)) :=
    hstep1.trans (hkk.trans hgroup)
  rw [hfinal]
  exact hpos

open Filter Topology in
/-- N9: prime with factorial-dominated bound (Hermite size argument). -/
private theorem hl_exists_prime_gt_mul_pow_div_factorial_lt_one (C : ℝ) (hC : 0 ≤ C)
    (W : ℝ) (hW : 0 ≤ W) (A : ℕ) :
    ∃ p : ℕ, Nat.Prime p ∧ A < p ∧ W * C ^ p / ((p - 1).factorial : ℝ) < 1 := by
  have htend : Filter.Tendsto (fun n : ℕ => C ^ n / ((n.factorial : ℝ))) Filter.atTop (nhds 0) :=
    FloorSemiring.tendsto_pow_div_factorial_atTop C
  have htendW : Filter.Tendsto (fun n : ℕ => W * C * (C ^ n / ((n.factorial : ℝ))))
      Filter.atTop (nhds 0) := by
    have h0 : (0 : ℝ) = W * C * 0 := by ring
    rw [h0]
    exact Filter.Tendsto.const_mul _ htend
  rw [Metric.tendsto_atTop] at htendW
  obtain ⟨N0, hN0⟩ := htendW 1 (by norm_num)
  obtain ⟨p, hpge, hpprime⟩ := Nat.exists_infinite_primes (max N0 (A + 1) + 1)
  have hAle : A + 1 ≤ p := by
    have h1 : A + 1 ≤ max N0 (A + 1) := Nat.le_max_right _ _
    have h2 : max N0 (A + 1) ≤ p := by omega
    omega
  have hN0le : N0 ≤ p - 1 := by
    have h1 : N0 ≤ max N0 (A + 1) := Nat.le_max_left _ _
    have h2 : max N0 (A + 1) ≤ p - 1 := by omega
    omega
  refine ⟨p, hpprime, by omega, ?_⟩
  have hCeq : C ^ p = C * C ^ (p - 1) := by
    have hpeq : p = (p - 1) + 1 := by omega
    conv_lhs => rw [hpeq, pow_succ']
  have hrewrite : W * C ^ p / (((p - 1).factorial : ℕ) : ℝ)
      = W * C * (C ^ (p - 1) / ((((p - 1).factorial : ℕ)) : ℝ)) := by
    rw [hCeq]; ring
  rw [hrewrite]
  have hnn : 0 ≤ W * C * (C ^ (p - 1) / ((((p - 1).factorial : ℕ)) : ℝ)) := by
    apply mul_nonneg (mul_nonneg hW hC)
    apply div_nonneg (pow_nonneg hC _)
    positivity
  have hmem := hN0 (p - 1) hN0le
  rw [dist_zero_right, Real.norm_of_nonneg hnn] at hmem
  exact hmem

/-- N11: reduction to algebraic integers. -/
private theorem hl_exists_isIntegral_of_isAlgebraic_exp (α : ℂ) (hα : α ≠ 0)
    (halg : IsAlgebraic ℚ α) (hexp : IsAlgebraic ℚ (Complex.exp α)) :
    ∃ α' : ℂ, α' ≠ 0 ∧ IsIntegral ℤ α' ∧ IsAlgebraic ℚ (Complex.exp α') := by
  have halgZ : IsAlgebraic ℤ α := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr halg
  obtain ⟨y, hy, hint⟩ := IsAlgebraic.exists_integral_multiple halgZ
  have hN : (Int.natAbs y) ≠ 0 := Int.natAbs_ne_zero.mpr hy
  use ((Int.natAbs y : ℕ) : ℂ) * α
  refine ⟨?_, ?_, ?_⟩
  · apply mul_ne_zero _ hα
    exact Nat.cast_ne_zero.mpr hN
  · rcases Int.natAbs_eq y with h | h
    · have hsm : y • α = ((Int.natAbs y : ℕ) : ℂ) * α := by
        rw [h]; simp [zsmul_eq_mul]
      rw [← hsm]; exact hint
    · have hsm : y • α = -(((Int.natAbs y : ℕ) : ℂ) * α) := by
        rw [h]; simp [zsmul_eq_mul]
      have : ((Int.natAbs y : ℕ) : ℂ) * α = -(y • α) := by rw [hsm]; simp
      rw [this]
      exact hint.neg
  · have hexpN : IsAlgebraic ℚ ((Complex.exp α) ^ (Int.natAbs y)) := hexp.pow _
    have hexpeq : Complex.exp (((Int.natAbs y : ℕ) : ℂ) * α)
        = (Complex.exp α) ^ (Int.natAbs y) := by
      rw [← Complex.exp_nat_mul]
    rw [hexpeq]
    exact hexpN

open Classical in
/-- N8 (single factor): B(e^a)·B(e^{-a}) as a sum over index pairs. -/
private theorem hl_single_aeval_exp (B : Polynomial ℤ) (a : ℂ) :
    Polynomial.aeval (Complex.exp a) B * Polynomial.aeval (Complex.exp (-a)) B
    = ∑ p : Fin (B.natDegree + 1) × Fin (B.natDegree + 1),
      ((B.coeff (p.1.val) * B.coeff (p.2.val) : ℤ) : ℂ)
      * Complex.exp ((((p.1.val : ℤ) - (p.2.val : ℤ) : ℤ) : ℂ) * a) := by
  have hB : Polynomial.aeval (Complex.exp a) B
      = ∑ i : Fin (B.natDegree + 1), (((B.coeff (i.val) : ℤ)) : ℂ) * (Complex.exp a) ^ (i.val) := by
    rw [Polynomial.aeval_eq_sum_range]
    rw [← Fin.sum_univ_eq_sum_range (fun i => B.coeff i • (Complex.exp a) ^ i) (B.natDegree + 1)]
    apply Finset.sum_congr rfl
    intro i _
    rw [zsmul_eq_mul]
  have hBn : Polynomial.aeval (Complex.exp (-a)) B
      = ∑ i : Fin (B.natDegree + 1),
        (((B.coeff (i.val) : ℤ)) : ℂ) * (Complex.exp (-a)) ^ (i.val) := by
    rw [Polynomial.aeval_eq_sum_range]
    rw [← Fin.sum_univ_eq_sum_range (fun i => B.coeff i • (Complex.exp (-a)) ^ i) (B.natDegree + 1)]
    apply Finset.sum_congr rfl
    intro i _
    rw [zsmul_eq_mul]
  rw [hB, hBn, Finset.sum_mul_sum]
  have hprod : (∑ i : Fin (B.natDegree + 1), ∑ j : Fin (B.natDegree + 1),
      (((B.coeff (i.val) : ℤ)) : ℂ) * (Complex.exp a) ^ (i.val) *
      ((((B.coeff (j.val) : ℤ)) : ℂ) * (Complex.exp (-a)) ^ (j.val)))
      = ∑ p : Fin (B.natDegree + 1) × Fin (B.natDegree + 1),
      (((B.coeff (p.1.val) : ℤ)) : ℂ) * (Complex.exp a) ^ (p.1.val) *
      ((((B.coeff (p.2.val) : ℤ)) : ℂ) * (Complex.exp (-a)) ^ (p.2.val)) := by
    have h := (Fintype.sum_prod_type (fun p : Fin (B.natDegree + 1) × Fin (B.natDegree + 1) =>
      (((B.coeff (p.1.val) : ℤ)) : ℂ) * (Complex.exp a) ^ (p.1.val) *
        ((((B.coeff (p.2.val) : ℤ)) : ℂ) * (Complex.exp (-a)) ^ (p.2.val)))).symm
    simpa using h
  rw [hprod]
  apply Finset.sum_congr rfl
  intro p _
  have hexp : (Complex.exp a) ^ (p.1.val) * (Complex.exp (-a)) ^ (p.2.val)
      = Complex.exp ((((p.1.val : ℤ) - (p.2.val : ℤ) : ℤ) : ℂ) * a) := by
    have h1 : (Complex.exp a) ^ (p.1.val) = Complex.exp (((p.1.val : ℕ) : ℂ) * a) := by
      rw [Complex.exp_nat_mul]
    have h2 : (Complex.exp (-a)) ^ (p.2.val) = Complex.exp (((p.2.val : ℕ) : ℂ) * (-a)) := by
      rw [Complex.exp_nat_mul]
    rw [h1, h2, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc (((B.coeff ↑p.1 : ℤ) : ℂ) * Complex.exp a ^ ↑p.1)
        * (((B.coeff ↑p.2 : ℤ) : ℂ) * Complex.exp (-a) ^ ↑p.2)
      = ((B.coeff ↑p.1 * B.coeff ↑p.2 : ℤ) : ℂ)
        * ((Complex.exp a) ^ (p.1.val)
          * (Complex.exp (-a)) ^ (p.2.val)) := by
        push_cast
        ring
    _ = _ := by rw [hexp]

/-- N3: enumerate roots of a monic integer polynomial killing a nonzero integral α. -/
private theorem hl_exists_root_enum_of_isIntegral (α : ℂ) (hα : α ≠ 0) (hint : IsIntegral ℤ α) :
    ∃ (n : ℕ) (a : Fin n → ℂ) (f : Polynomial ℤ), f.Monic ∧
    (Finset.prod Finset.univ (fun j => Polynomial.X - Polynomial.C (a j))
      = Polynomial.map (algebraMap ℤ ℂ) f) ∧
    (∀ j, a j ≠ 0) ∧ (∀ j, IsIntegral ℤ (a j)) ∧ (∃ j0, a j0 = α) := by
  obtain ⟨p, hpmonic, hpeval⟩ := hint
  have hp0 : p ≠ 0 := hpmonic.ne_zero
  obtain ⟨f, hf_eq, hf_ndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 0
  have hX0 : (Polynomial.X - Polynomial.C (0 : ℤ)) = Polynomial.X := by simp
  rw [hX0] at hf_eq hf_ndvd
  have hXpow_monic : ((Polynomial.X : Polynomial ℤ) ^ Polynomial.rootMultiplicity 0 p).Monic :=
    Polynomial.monic_X_pow _
  have hf_monic : f.Monic := by
    have hprod_monic :
        ((Polynomial.X : Polynomial ℤ) ^ Polynomial.rootMultiplicity 0 p
          * f).Monic := by
      rw [← hf_eq]; exact hpmonic
    exact Polynomial.Monic.of_mul_monic_left hXpow_monic hprod_monic
  have hf_coeff0 : f.coeff 0 ≠ 0 := fun hcoeff => hf_ndvd (Polynomial.X_dvd_iff.mpr hcoeff)
  have hf_eval : Polynomial.aeval α f = 0 := by
    have hpeval_a : Polynomial.aeval α p = 0 := hpeval
    have haeval : Polynomial.aeval α p = Polynomial.aeval α
        ((Polynomial.X : Polynomial ℤ) ^ Polynomial.rootMultiplicity 0 p * f) := by rw [← hf_eq]
    rw [map_mul, map_pow, Polynomial.aeval_X] at haeval
    rw [hpeval_a] at haeval
    have hxr : α ^ Polynomial.rootMultiplicity 0 p ≠ 0 := pow_ne_zero _ hα
    rcases mul_eq_zero.mp haeval.symm with h1 | h1
    · exact absurd h1 hxr
    · exact h1
  let F : Polynomial ℂ := Polynomial.map (algebraMap ℤ ℂ) f
  have hFmonic : F.Monic := hf_monic.map _
  have hFne : F ≠ 0 := hFmonic.ne_zero
  have hcard : F.roots.card = F.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hprod : (F.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod = F :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hFmonic hcard
  refine ⟨F.roots.toList.length, fun j => F.roots.toList[j.val], f, hf_monic, ?_, ?_, ?_, ?_⟩
  · have hofn : List.ofFn
        (fun j : Fin F.roots.toList.length => F.roots.toList[j.val])
        = F.roots.toList :=
      List.ofFn_getElem
    have hmap : Multiset.map
        (fun j : Fin F.roots.toList.length =>
          Polynomial.X - Polynomial.C (F.roots.toList[j.val]))
        Finset.univ.val
        = F.roots.map (fun r => Polynomial.X - Polynomial.C r) := by
      rw [Fin.univ_val_map]
      have hstep : (List.ofFn fun j : Fin F.roots.toList.length =>
            Polynomial.X - Polynomial.C (F.roots.toList[j.val]))
          = List.map (fun r => Polynomial.X - Polynomial.C r)
            (List.ofFn fun j : Fin F.roots.toList.length =>
              F.roots.toList[j.val]) := by
        rw [List.map_ofFn]
        rfl
      rw [hstep, hofn, ← Multiset.map_coe, Multiset.coe_toList]
    have hfin : Finset.prod Finset.univ
          (fun j : Fin F.roots.toList.length =>
            Polynomial.X - Polynomial.C (F.roots.toList[j.val]))
        = (Multiset.map
          (fun j : Fin F.roots.toList.length =>
            Polynomial.X - Polynomial.C (F.roots.toList[j.val]))
          Finset.univ.val).prod := rfl
    rw [hfin, hmap, hprod]
  · intro j
    have hmem : (F.roots.toList[j.val] : ℂ) ∈ F.roots := by
      have hlt : (j.val : ℕ) < F.roots.toList.length := j.isLt
      have h := List.getElem_mem hlt
      rwa [Multiset.mem_toList] at h
    have hroot : F.IsRoot (F.roots.toList[j.val]) := (Polynomial.mem_roots hFne).mp hmem
    simp only at hroot ⊢
    intro hz
    simp only [hz] at hroot
    have heval0 : Polynomial.eval 0 F = 0 := hroot
    have hcast : Polynomial.eval 0 F = ((f.coeff 0 : ℤ) : ℂ) := by simp [F, Polynomial.eval_map]
    rw [hcast] at heval0
    have h0 : (f.coeff 0 : ℤ) = 0 := by exact_mod_cast heval0
    exact hf_coeff0 h0
  · intro j
    have hmem : (F.roots.toList[j.val] : ℂ) ∈ F.roots := by
      have hlt : (j.val : ℕ) < F.roots.toList.length := j.isLt
      have h := List.getElem_mem hlt
      rwa [Multiset.mem_toList] at h
    have hroot : F.IsRoot (F.roots.toList[j.val]) := (Polynomial.mem_roots hFne).mp hmem
    refine ⟨f, hf_monic, ?_⟩
    have heval : Polynomial.eval (F.roots.toList[j.val]) F = 0 := hroot
    have heval2 : Polynomial.eval₂ (algebraMap ℤ ℂ) (F.roots.toList[j.val]) f = 0 := by
      have h1 : Polynomial.eval (F.roots.toList[j.val]) F
          = Polynomial.eval₂ (algebraMap ℤ ℂ) (F.roots.toList[j.val])
            f := by
        simp [F, Polynomial.eval_map]
      rwa [h1] at heval
    have haeval : Polynomial.aeval (F.roots.toList[j.val]) f = 0 := by
      rw [Polynomial.aeval_def]
      exact heval2
    exact haeval
  · have hFroot : F.IsRoot α := by
      change Polynomial.eval α F = 0
      have h1 : Polynomial.eval α F = Polynomial.eval₂ (algebraMap ℤ ℂ) α f := by
        simp [F, Polynomial.eval_map]
      rw [h1]
      have h2 : Polynomial.eval₂ (algebraMap ℤ ℂ) α f = Polynomial.aeval α f := by
        rw [Polynomial.aeval_def]
      rw [h2, hf_eval]
    have hmem : α ∈ F.roots := (Polynomial.mem_roots hFne).mpr hFroot
    have hmemL : α ∈ F.roots.toList := Multiset.mem_toList.mpr hmem
    rw [List.mem_iff_getElem] at hmemL
    obtain ⟨n, hn, hnth⟩ := hmemL
    exact ⟨⟨n, hn⟩, by simpa using hnth⟩

/-- N8-full: product over conjugates as a sum over index functions. -/
private theorem hl_prod_aeval_exp (n : ℕ) (a : Fin n → ℂ) (B : Polynomial ℤ) :
    Finset.prod Finset.univ (fun j =>
      Polynomial.aeval (Complex.exp (a j)) B
        * Polynomial.aeval (Complex.exp (-(a j))) B)
    = ∑ u : Fin n → Fin (B.natDegree + 1) × Fin (B.natDegree + 1),
      (((Finset.prod Finset.univ
        (fun j => B.coeff ((u j).1.val) * B.coeff ((u j).2.val))
          : ℤ) : ℂ)
      * Complex.exp (∑ j, (((((u j).1.val : ℤ) - ((u j).2.val : ℤ)
        : ℤ) : ℂ) * a j))) := by
  have hsingle : ∀ j : Fin n,
      Polynomial.aeval (Complex.exp (a j)) B
        * Polynomial.aeval (Complex.exp (-(a j))) B
      = ∑ p : Fin (B.natDegree + 1) × Fin (B.natDegree + 1),
        ((B.coeff (p.1.val) * B.coeff (p.2.val) : ℤ) : ℂ)
        * Complex.exp (((((p.1.val : ℤ) - (p.2.val : ℤ) : ℤ) : ℂ)) * a j) := fun j =>
    hl_single_aeval_exp B (a j)
  conv_lhs => rw [Finset.prod_congr rfl (fun j _ => hsingle j)]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro u _
  have hexp_prod : (Finset.prod Finset.univ (fun j =>
        Complex.exp (((((u j).1.val : ℤ) - ((u j).2.val : ℤ) : ℤ)
          : ℂ) * a j)))
      = Complex.exp (∑ j, (((((u j).1.val : ℤ) - ((u j).2.val : ℤ)
        : ℤ) : ℂ) * a j)) := by
    rw [Complex.exp_sum]
  have hsplit : (Finset.prod Finset.univ (fun j =>
      (((B.coeff ((u j).1.val) * B.coeff ((u j).2.val) : ℤ) : ℂ)
      * Complex.exp (((((u j).1.val : ℤ) - ((u j).2.val : ℤ) : ℤ)
        : ℂ) * a j))))
      = (((Finset.prod Finset.univ
        (fun j => B.coeff ((u j).1.val) * B.coeff ((u j).2.val))
          : ℤ) : ℂ)
      * Complex.exp (∑ j, (((((u j).1.val : ℤ) - ((u j).2.val : ℤ)
        : ℤ) : ℂ) * a j))) := by
    rw [Finset.prod_mul_distrib, hexp_prod]
    congr 1
    rw [Int.cast_prod]
  exact hsplit

open Classical in
/-- N10: the Lindemann core contradiction. -/
private theorem hl_lindemann_core (ι : Type*) [Fintype ι]
    (w : ι → ℤ) (γ : ι → ℂ)
    (h1 : (∑ i, ((w i : ℤ) : ℂ) * Complex.exp (γ i)) = 0)
    (h2 : (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i) ≠ 0)
    (h3 : ∃ F : Polynomial ℤ, F.Monic ∧ Polynomial.eval 0 F ≠ 0 ∧
      ∀ i, γ i ≠ 0 → Polynomial.aeval (γ i) F = 0)
    (h4 : ∀ g : Polynomial ℤ, ∃ z : ℤ,
      (∑ i, ((w i : ℤ) : ℂ) * Polynomial.aeval (γ i) g) = (z : ℂ)) :
    False := by
  obtain ⟨F, hFmonic, hF0, hFvan⟩ := h3
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx F hF0
  obtain ⟨p, hpprime, hpA, hplt⟩ :=
    hl_exists_prime_gt_mul_pow_div_factorial_lt_one |c| (abs_nonneg c)
      (∑ i, |(w i : ℝ)|)
      (Finset.sum_nonneg (fun i _ => abs_nonneg _))
      (max (Polynomial.eval 0 F).natAbs
        (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i).natAbs)
  have hpF : (Polynomial.eval 0 F).natAbs < p :=
    lt_of_le_of_lt (Nat.le_max_left _ _) hpA
  have hpq : (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i).natAbs
      < p :=
    lt_of_le_of_lt (Nat.le_max_right _ _) hpA
  obtain ⟨np, hnp, gp, _, hgpbound⟩ := hc p hpF hpprime
  obtain ⟨z, hz⟩ := h4 gp
  have hkey : (∑ i, ((w i : ℤ) : ℂ)
        * (((np : ℂ) * Complex.exp (γ i))
          - ((p : ℂ) * Polynomial.aeval (γ i) gp)))
      = -((p : ℂ) * ((z : ℤ) : ℂ)) := by
    have hnp_mul : (∑ i, (np : ℂ)
          * (((w i : ℤ) : ℂ) * Complex.exp (γ i))) = 0 := by
      rw [← Finset.mul_sum, h1, mul_zero]
    have hsub : (∑ i, ((w i : ℤ) : ℂ)
            * (((np : ℂ) * Complex.exp (γ i))
              - ((p : ℂ) * Polynomial.aeval (γ i) gp)))
          = (∑ i, (np : ℂ) * (((w i : ℤ) : ℂ) * Complex.exp (γ i)))
            - (∑ i, (p : ℂ)
              * (((w i : ℤ) : ℂ) * Polynomial.aeval (γ i) gp)) := by
      rw [← Finset.sum_sub_distrib]
      have hterm : ∀ i ∈ (Finset.univ : Finset ι),
          ((w i : ℤ) : ℂ)
            * (((np : ℂ) * Complex.exp (γ i))
              - ((p : ℂ) * Polynomial.aeval (γ i) gp))
          = ((np : ℂ) * (((w i : ℤ) : ℂ) * Complex.exp (γ i))
            - (p : ℂ) * (((w i : ℤ) : ℂ)
              * Polynomial.aeval (γ i) gp)) := by
        intro i _
        ring
      exact Finset.sum_congr rfl hterm
    have hgp_sum : (∑ i, (p : ℂ)
          * (((w i : ℤ) : ℂ) * Polynomial.aeval (γ i) gp))
        = ((p : ℂ) * ((z : ℤ) : ℂ)) := by
      rw [← Finset.mul_sum, hz]
    rw [hsub, hnp_mul, hgp_sum, zero_sub]
  have hsplit : (∑ i ∈ Finset.univ.filter (fun i => γ i = 0),
          ((w i : ℤ) : ℂ)
            * (((np : ℂ) * Complex.exp (γ i))
              - ((p : ℂ) * Polynomial.aeval (γ i) gp)))
        + (∑ i ∈ Finset.univ.filter (fun i => ¬γ i = 0),
          ((w i : ℤ) : ℂ)
            * (((np : ℂ) * Complex.exp (γ i))
              - ((p : ℂ) * Polynomial.aeval (γ i) gp)))
        = ∑ i, ((w i : ℤ) : ℂ)
          * (((np : ℂ) * Complex.exp (γ i))
            - ((p : ℂ) * Polynomial.aeval (γ i) gp)) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hzero : (∑ i ∈ Finset.univ.filter (fun i => γ i = 0),
        ((w i : ℤ) : ℂ)
          * (((np : ℂ) * Complex.exp (γ i))
            - ((p : ℂ) * Polynomial.aeval (γ i) gp)))
      = (((∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i
        : ℤ)) : ℂ)
        * (((np : ℂ)) - ((p : ℂ)) * ((((gp.eval 0 : ℤ))) : ℂ)) := by
    have hterm : ∀ i ∈ Finset.univ.filter (fun i => γ i = 0),
        ((w i : ℤ) : ℂ)
          * (((np : ℂ) * Complex.exp (γ i))
            - ((p : ℂ) * Polynomial.aeval (γ i) gp))
        = ((w i : ℤ) : ℂ)
          * (((np : ℂ)) - ((p : ℂ)) * ((((gp.eval 0 : ℤ))) : ℂ)) := by
      intro i hi
      have hzi : γ i = 0 := (Finset.mem_filter.mp hi).2
      have h1 : Polynomial.aeval (0 : ℂ) gp
          = ((((gp.eval 0 : ℤ))) : ℂ) := by
        have h := Polynomial.coeff_zero_eq_aeval_zero' (R := ℤ)
          (A := ℂ) gp
        have halg : (algebraMap ℤ ℂ) (gp.coeff 0)
            = ((((gp.coeff 0 : ℤ))) : ℂ) := by simp
        rw [halg, Polynomial.coeff_zero_eq_eval_zero] at h
        exact h.symm
      rw [hzi, Complex.exp_zero, mul_one, h1]
    have hstep : (∑ i ∈ Finset.univ.filter (fun i => γ i = 0),
          ((w i : ℤ) : ℂ)
            * (((np : ℂ) * Complex.exp (γ i))
              - ((p : ℂ) * Polynomial.aeval (γ i) gp)))
        = ∑ i ∈ Finset.univ.filter (fun i => γ i = 0),
          ((w i : ℤ) : ℂ)
            * (((np : ℂ)) - ((p : ℂ))
              * ((((gp.eval 0 : ℤ))) : ℂ)) :=
      Finset.sum_congr rfl hterm
    have hcast : (∑ i ∈ Finset.univ.filter (fun i => γ i = 0),
          ((w i : ℤ) : ℂ))
        = (((∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i
          : ℤ)) : ℂ) :=
      (Int.cast_sum _ _).symm
    rw [hstep, ← Finset.sum_mul, hcast]
  have hmapne : F.map (algebraMap ℤ ℂ) ≠ 0 :=
    (hFmonic.map _).ne_zero
  have hFpos : (0 : ℝ) < ((((p - 1).factorial : ℕ)) : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hcp : c ^ p ≤ |c| ^ p := by
    rw [← abs_pow]
    exact le_abs_self _
  have hbound : ‖(∑ i ∈ Finset.univ.filter (fun i => ¬γ i = 0),
        ((w i : ℤ) : ℂ)
          * (((np : ℂ) * Complex.exp (γ i))
            - ((p : ℂ) * Polynomial.aeval (γ i) gp)))‖
      ≤ (∑ i, |(w i : ℝ)|) * |c| ^ p
        / ((((p - 1).factorial : ℕ)) : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    have hper : ∀ i ∈ Finset.univ.filter (fun i => ¬γ i = 0),
        ‖((w i : ℤ) : ℂ)
          * (((np : ℂ) * Complex.exp (γ i))
            - ((p : ℂ) * Polynomial.aeval (γ i) gp))‖
        ≤ |(w i : ℝ)|
          * (|c| ^ p / ((((p - 1).factorial : ℕ)) : ℝ)) := by
      intro i hi
      have hmem : γ i ≠ 0 := (Finset.mem_filter.mp hi).2
      have hroot : γ i ∈ F.aroots ℂ := by
        rw [Polynomial.mem_aroots']
        exact ⟨hmapne, hFvan i hmem⟩
      have hb := hgpbound hroot
      rw [zsmul_eq_mul, nsmul_eq_mul] at hb
      have hle : ‖((np : ℂ) * Complex.exp (γ i)
            - (p : ℂ) * Polynomial.aeval (γ i) gp)‖
          ≤ |c| ^ p / ((((p - 1).factorial : ℕ)) : ℝ) := by
        refine hb.trans ?_
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hcp
          (inv_nonneg.mpr (le_of_lt hFpos))
      rw [norm_mul, Complex.norm_intCast]
      exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)
    refine (Finset.sum_le_sum hper).trans ?_
    have hsub : (∑ i ∈ Finset.univ.filter (fun i => ¬γ i = 0),
          |(w i : ℝ)| * (|c| ^ p / ((((p - 1).factorial : ℕ)) : ℝ)))
        ≤ ∑ i, |(w i : ℝ)|
          * (|c| ^ p / ((((p - 1).factorial : ℕ)) : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun x _ => Finset.mem_univ x)
        (fun i _ _ => by positivity)
    have hfac : (∑ i, |(w i : ℝ)|
          * (|c| ^ p / ((((p - 1).factorial : ℕ)) : ℝ)))
        = (∑ i, |(w i : ℝ)|) * |c| ^ p
          / ((((p - 1).factorial : ℕ)) : ℝ) := by
      rw [← Finset.sum_mul, mul_div_assoc]
    exact hsub.trans (le_of_eq hfac)
  have hNS : ((np * (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
        + (p : ℤ) * (z - (∑ i ∈ Finset.univ.filter (fun i => γ i = 0),
          w i) * gp.eval 0) : ℤ) : ℂ)
      + (∑ i ∈ Finset.univ.filter (fun i => ¬γ i = 0),
        ((w i : ℤ) : ℂ)
          * (((np : ℂ) * Complex.exp (γ i))
            - ((p : ℂ) * Polynomial.aeval (γ i) gp))) = 0 := by
    have h3 := hsplit
    rw [hkey, hzero] at h3
    have hexpand : ((np * (∑ i ∈ Finset.univ.filter (fun i => γ i = 0),
            w i) + (p : ℤ) * (z - (∑ i ∈ Finset.univ.filter
            (fun i => γ i = 0), w i) * gp.eval 0) : ℤ) : ℂ)
        = ((np : ℂ))
          * (((∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i
            : ℤ)) : ℂ) + ((p : ℂ))
          * ((((z : ℤ)) : ℂ) - (((∑ i ∈ Finset.univ.filter
            (fun i => γ i = 0), w i : ℤ)) : ℂ)
            * ((((gp.eval 0 : ℤ))) : ℂ)) := by
      simp only [Int.cast_add, Int.cast_mul, Int.cast_sub,
        Int.cast_natCast]
    rw [hexpand]
    linear_combination h3
  have hNeq : ((np * (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
        + (p : ℤ) * (z - (∑ i ∈ Finset.univ.filter (fun i => γ i = 0),
          w i) * gp.eval 0) : ℤ) : ℂ)
      = -(∑ i ∈ Finset.univ.filter (fun i => ¬γ i = 0),
        ((w i : ℤ) : ℂ)
          * (((np : ℂ) * Complex.exp (γ i))
            - ((p : ℂ) * Polynomial.aeval (γ i) gp))) :=
    eq_neg_of_add_eq_zero_left hNS
  have hnorm_lt : ‖((np * (∑ i ∈ Finset.univ.filter (fun i => γ i = 0),
        w i) + (p : ℤ) * (z - (∑ i ∈ Finset.univ.filter
        (fun i => γ i = 0), w i) * gp.eval 0) : ℤ) : ℂ)‖ < 1 := by
    rw [hNeq, norm_neg]
    exact lt_of_le_of_lt hbound hplt
  have hpN : ¬ (p : ℤ) ∣ (np * (∑ i ∈ Finset.univ.filter
        (fun i => γ i = 0), w i) + (p : ℤ) * (z -
        (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
          * gp.eval 0)) := by
    intro hdiv
    have hdvd : (p : ℤ) ∣ np * (∑ i ∈ Finset.univ.filter
        (fun i => γ i = 0), w i) := by
      have h1 : (p : ℤ) ∣ (np * (∑ i ∈ Finset.univ.filter
          (fun i => γ i = 0), w i) + (p : ℤ) * (z -
          (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
            * gp.eval 0)) := hdiv
      have h2 : (p : ℤ) ∣ (p : ℤ) * (z -
          (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
            * gp.eval 0) :=
        dvd_mul_right _ _
      have h3 := dvd_sub h1 h2
      have heq : (np * (∑ i ∈ Finset.univ.filter (fun i => γ i = 0),
          w i) + (p : ℤ) * (z - (∑ i ∈ Finset.univ.filter
          (fun i => γ i = 0), w i) * gp.eval 0))
          - (p : ℤ) * (z - (∑ i ∈ Finset.univ.filter
          (fun i => γ i = 0), w i) * gp.eval 0)
          = np * (∑ i ∈ Finset.univ.filter (fun i => γ i = 0),
            w i) := by ring
      rwa [heq] at h3
    have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpprime
    rcases hprime.dvd_mul.mp hdvd with hnp' | hq0'
    · exact hnp hnp'
    · have hlt : (∑ i ∈ Finset.univ.filter (fun i => γ i = 0),
          w i).natAbs < p := hpq
      have hpos : 0 < (∑ i ∈ Finset.univ.filter (fun i => γ i = 0),
          w i).natAbs :=
        Int.natAbs_pos.mpr h2
      have hle : p ≤ (∑ i ∈ Finset.univ.filter (fun i => γ i = 0),
          w i).natAbs := by
        have h1 : (p : ℤ).natAbs ∣ (∑ i ∈ Finset.univ.filter
            (fun i => γ i = 0), w i).natAbs :=
          Int.natAbs_dvd_natAbs.mpr hq0'
        rw [Int.natAbs_natCast] at h1
        exact Nat.le_of_dvd hpos h1
      omega
  have hNne : (np * (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
      + (p : ℤ) * (z - (∑ i ∈ Finset.univ.filter (fun i => γ i = 0),
        w i) * gp.eval 0)) ≠ 0 := by
    intro h0
    apply hpN
    rw [h0]
    exact dvd_zero _
  have hNlt : (((|np * (∑ i ∈ Finset.univ.filter (fun i => γ i = 0),
      w i) + (p : ℤ) * (z - (∑ i ∈ Finset.univ.filter
      (fun i => γ i = 0), w i) * gp.eval 0)| : ℤ)) : ℝ) < 1 := by
    have h1 := hnorm_lt
    rw [Complex.norm_intCast, ← Int.cast_abs] at h1
    exact h1
  have h1le : (1 : ℝ) ≤ (((|np * (∑ i ∈ Finset.univ.filter
      (fun i => γ i = 0), w i) + (p : ℤ) * (z -
      (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
        * gp.eval 0)| : ℤ)) : ℝ) :=
    by exact_mod_cast Int.one_le_abs hNne
  linarith

/--
**Hermite–Lindemann theorem.** If $\alpha$ is a nonzero complex number that is algebraic over
$\mathbb{Q}$, then $e^{\alpha}$ is transcendental over $\mathbb{Q}$.

Proves `Wanted` entry `hermite_lindemann`.

Source: C. Hermite, Sur la fonction exponentielle, C. R. Acad. Sci. Paris 77 (1873) for e; F. von
Lindemann, Über die Zahl π, Math. Ann. 20 (1882) 213–225 extension to π; textbook in Baker,
Transcendental Number Theory
-/
theorem hermite_lindemann :
    ∀ (α : ℂ), α ≠ 0 → IsAlgebraic ℚ α → Transcendental ℚ (Complex.exp α) := by
  intro α hα halg hexp
  obtain ⟨α', hα'0, hα'int, hexp'⟩ :=
    hl_exists_isIntegral_of_isAlgebraic_exp α hα halg hexp
  have hexp'Z : IsAlgebraic ℤ (Complex.exp α') :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr hexp'
  obtain ⟨B, hB0, hBeval⟩ := hexp'Z
  obtain ⟨n, a, f, _, hprod, ha0, haint, j0, hj0⟩ :=
    hl_exists_root_enum_of_isIntegral α' hα'0 hα'int
  refine hl_lindemann_core (Fin n → Fin (B.natDegree + 1)
      × Fin (B.natDegree + 1))
    (fun u => Finset.prod Finset.univ
      (fun j => B.coeff (u j).1.val * B.coeff (u j).2.val))
    (fun u => ∑ j, (((((u j).1.val : ℤ) - ((u j).2.val : ℤ) : ℤ)
      : ℂ) * a j))
    ?h1 ?h2 ?h3 ?h4
  · have h8 := hl_prod_aeval_exp n a B
    have hfac : Polynomial.aeval (Complex.exp (a j0)) B
        * Polynomial.aeval (Complex.exp (-(a j0))) B = 0 := by
      rw [hj0, hBeval, zero_mul]
    have hprod0 : Finset.prod Finset.univ (fun j =>
          Polynomial.aeval (Complex.exp (a j)) B
            * Polynomial.aeval (Complex.exp (-(a j))) B) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j0) hfac
    rw [h8] at hprod0
    exact hprod0
  · exact ne_of_gt (hl_zero_fiber_weight_pos n a ha0 B hB0)
  · have hint : ∀ u : Fin n → Fin (B.natDegree + 1)
        × Fin (B.natDegree + 1),
        IsIntegral ℤ (∑ j, (((((u j).1.val : ℤ)
          - ((u j).2.val : ℤ) : ℤ) : ℂ) * a j)) := by
      intro u
      have hterm : ∀ j ∈ (Finset.univ : Finset (Fin n)),
          IsIntegral ℤ (((((u j).1.val : ℤ)
            - ((u j).2.val : ℤ) : ℤ) : ℂ) * a j) := by
        intro j _
        have h1 : (((((u j).1.val : ℤ) - ((u j).2.val : ℤ) : ℤ)
            : ℂ) * a j)
            = (((u j).1.val : ℤ) - ((u j).2.val : ℤ)) • a j :=
          (zsmul_eq_mul _ _).symm
        rw [h1]
        exact IsIntegral.zsmul (haint j) _
      exact IsIntegral.sum _ hterm
    obtain ⟨F, hFmonic, hF0, hFvan⟩ :=
      hl_exists_int_poly_eval_zero_ne_zero_of_isIntegral
        (fun u : Fin n → Fin (B.natDegree + 1)
          × Fin (B.natDegree + 1) =>
          ∑ j, (((((u j).1.val : ℤ) - ((u j).2.val : ℤ) : ℤ)
            : ℂ) * a j))
        hint
    exact ⟨F, hFmonic, hF0, hFvan⟩
  · intro g
    have hW : ∀ (σ : Equiv.Perm (Fin n))
        (u : Fin n → Fin (B.natDegree + 1)
          × Fin (B.natDegree + 1)),
        (fun u => Finset.prod Finset.univ
            (fun j => B.coeff (u j).1.val * B.coeff (u j).2.val))
          (u ∘ ⇑σ)
        = (fun u => Finset.prod Finset.univ
            (fun j => B.coeff (u j).1.val * B.coeff (u j).2.val))
          u := by
      intro σ u
      change Finset.prod Finset.univ (fun j =>
          B.coeff (u (σ j)).1.val * B.coeff (u (σ j)).2.val)
        = Finset.prod Finset.univ
          (fun j => B.coeff (u j).1.val * B.coeff (u j).2.val)
      exact Equiv.prod_comp σ (fun j =>
        B.coeff (u j).1.val * B.coeff (u j).2.val)
    obtain ⟨zz, hzz⟩ := hl_sum_weight_aeval_linearForm_eq_intCast n
      (Fin (B.natDegree + 1) × Fin (B.natDegree + 1))
      (fun u => Finset.prod Finset.univ
        (fun j => B.coeff (u j).1.val * B.coeff (u j).2.val))
      hW
      (fun p : Fin (B.natDegree + 1) × Fin (B.natDegree + 1) =>
        (p.1.val : ℤ) - (p.2.val : ℤ))
      a f hprod g
    exact ⟨zz, hzz⟩

end MathlibExt.NumberTheory.LindemannWanted
end
