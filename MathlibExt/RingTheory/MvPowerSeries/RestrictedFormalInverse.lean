/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MvPowerSeries_eventually_coeff_mem_span_pow_of_subst_eq_X_of_
exists_polynomial_inverse_mod.lean`
and
`P2M/Sol/S_MvPowerSeries_eventually_coeff_mem_span_pow_of_subst_eq_X_of_
exists_polynomial_inverse_mod.lean`
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

public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

universe u

open MvPowerSeries

namespace MvPowerSeries

/-- The linear part of a family of multivariate power series: the matrix of
its degree-one coefficients. -/
public noncomputable def linearPart {R : Type u} [CommRing R] {d : ℕ}
    (φ : Fin d → MvPowerSeries (Fin d) R) : Matrix (Fin d) (Fin d) R :=
  Matrix.of fun i j => coeff (Finsupp.single j 1) (φ i)

theorem linearPart_apply {R : Type u} [CommRing R] {d : ℕ}
    (φ : Fin d → MvPowerSeries (Fin d) R) (i j : Fin d) :
    linearPart φ i j = coeff (Finsupp.single j 1) (φ i) := rfl

end MvPowerSeries

namespace RestrictedFormalInverseAux

section CoefIdeal

variable {R : Type u} [CommRing R] {σ : Type*}

private def coefIdeal (σ : Type*) (a : R) : Ideal (MvPowerSeries σ R) where
  carrier := {f | ∀ n, coeff n f ∈ Ideal.span {a}}
  add_mem' := fun hf hg n => by rw [map_add]; exact Ideal.add_mem _ (hf n) (hg n)
  zero_mem' := fun n => by rw [map_zero]; exact Ideal.zero_mem _
  smul_mem' := fun c f hf n => by
    classical
    rw [smul_eq_mul, coeff_mul]
    exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ (hf x.2)

private theorem mem_coefIdeal {a : R} {f : MvPowerSeries σ R} :
    f ∈ coefIdeal σ a ↔ ∀ n, coeff n f ∈ Ideal.span {a} := Iff.rfl

private theorem coefIdeal_mul_le (a b : R) : coefIdeal σ a * coefIdeal σ b ≤ coefIdeal σ (a * b) :=
  by
  classical
  rw [Ideal.mul_le]
  intro f hf g hg n
  rw [coeff_mul]
  refine Ideal.sum_mem _ fun x _ => ?_
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp (hf x.1)
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp (hg x.2)
  rw [← hu, ← hv]
  exact Ideal.mem_span_singleton'.mpr ⟨u * v, by ring⟩

private theorem coefIdeal_sq_le (a : R) : coefIdeal σ a ^ 2 ≤ coefIdeal σ (a ^ 2) := by
  rw [pow_two, pow_two]; exact coefIdeal_mul_le a a

private theorem coefIdeal_mono {a b : R} (h : Ideal.span {a} ≤ Ideal.span {b}) :
    coefIdeal σ a ≤ coefIdeal σ b := fun _ hf n => h (hf n)

end CoefIdeal

section Taylor

variable {B : Type*} [CommRing B] {σ : Type*}

private theorem add_pow_of_sq_eq_zero (x y : B) (hy : y * y = 0) (k : ℕ) :
    (x + y) ^ k = x ^ k + (k : B) * x ^ (k - 1) * y := by
  induction k with
  | zero => simp
  | succ k IH =>
    rcases k with _ | k
    · simp
    · rw [pow_succ, IH]
      have : (x ^ (k + 1) + ((k + 1 : ℕ) : B) * x ^ (k + 1 - 1) * y) * (x + y)
          = x ^ (k + 1 + 1) + ((k + 1 + 1 : ℕ) : B) * x ^ (k + 1 + 1 - 1) * y
            + ((k + 1 : ℕ) : B) * x ^ k * (y * y) := by
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
        ring
      rw [this, hy, mul_zero, add_zero]

private theorem prod_add_pow_eq [DecidableEq σ] (h δ : σ → B) (hδ : ∀ j k, δ j * δ k = 0) (m : σ →
  ℕ)
    (s : Finset σ) :
    ∏ j ∈ s, (h j + δ j) ^ m j =
      ∏ j ∈ s, h j ^ m j + ∑ j ∈ s, (m j : B) * h j ^ (m j - 1) * (∏ j' ∈ s.erase j, h j' ^ m j') *
        δ j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb IH =>
    rw [Finset.prod_insert hb, Finset.prod_insert hb, Finset.sum_insert hb, IH,
      add_pow_of_sq_eq_zero _ _ (hδ b b), Finset.erase_insert hb]

    have hs : ∑ j ∈ s, (m j : B) * h j ^ (m j - 1) * (∏ j' ∈ (insert b s).erase j, h j' ^ m j') * δ
      j
        = h b ^ m b * ∑ j ∈ s, (m j : B) * h j ^ (m j - 1) * (∏ j' ∈ s.erase j, h j' ^ m j') * δ j
          := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hbj : b ≠ j := fun h => hb (h ▸ hj)
      rw [Finset.erase_insert_of_ne hbj, Finset.prod_insert (fun h => hb (Finset.mem_of_mem_erase
        h))]
      ring
    rw [hs]

    have hcross : (∑ j ∈ s, (m j : B) * h j ^ (m j - 1) * (∏ j' ∈ s.erase j, h j' ^ m j') * δ j) *
      δ b = 0 := by
      rw [Finset.sum_mul]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [mul_assoc, hδ j b, mul_zero]
    have key : (h b ^ m b + (m b : B) * h b ^ (m b - 1) * δ b) *
        (∏ j ∈ s, h j ^ m j + ∑ j ∈ s, (m j : B) * h j ^ (m j - 1) * (∏ j' ∈ s.erase j, h j' ^ m
          j') * δ j)
        = h b ^ m b * ∏ j ∈ s, h j ^ m j
          + ((m b : B) * h b ^ (m b - 1) * (∏ j ∈ s, h j ^ m j) * δ b
            + h b ^ m b * ∑ j ∈ s, (m j : B) * h j ^ (m j - 1) * (∏ j' ∈ s.erase j, h j' ^ m j') *
              δ j)
          + (m b : B) * h b ^ (m b - 1) *
            ((∑ j ∈ s, (m j : B) * h j ^ (m j - 1) * (∏ j' ∈ s.erase j, h j' ^ m j') * δ j) * δ b)
              := by
      ring
    rw [key, hcross, mul_zero, add_zero]

private theorem finsuppProd_sub_sub_sum_mem_sq {A : Type*} [CommRing A] [DecidableEq σ] (𝔇 : Ideal
  A)
    (g h : σ → A) (hgh : ∀ j, g j - h j ∈ 𝔇) (m : σ →₀ ℕ) :
    (m.prod fun j e => g j ^ e) - (m.prod fun j e => h j ^ e)
      - ∑ j ∈ m.support, (m j : A) * h j ^ (m j - 1) * (∏ j' ∈ m.support.erase j, h j' ^ m j') * (g
        j - h j)
      ∈ 𝔇 ^ 2 := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  set π := Ideal.Quotient.mk (𝔇 ^ 2) with hπ
  have hδ : ∀ j k, π (g j - h j) * π (g k - h k) = 0 := fun j k => by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_two]
    exact Ideal.mul_mem_mul (hgh j) (hgh k)
  have key := prod_add_pow_eq (fun j => π (h j)) (fun j => π (g j - h j)) hδ m m.support
  have e1 : ∀ j, π (h j) + π (g j - h j) = π (g j) := fun j => by rw [← map_add]; congr 1; ring
  simp only [e1] at key
  rw [map_sub, map_sub, map_sum]
  simp only [Finsupp.prod, map_prod, map_pow, map_mul, map_natCast]
  rw [key]
  ring

private theorem finsuppProd_sub_finsuppProd_mem {A : Type*} [CommRing A] (𝔇 : Ideal A)
    (g h : σ → A) (hgh : ∀ j, g j - h j ∈ 𝔇) (m : σ →₀ ℕ) :
    (m.prod fun j e => g j ^ e) - (m.prod fun j e => h j ^ e) ∈ 𝔇 := by
  classical
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  simp only [Finsupp.prod, map_prod, map_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  rw [Ideal.Quotient.eq]
  exact hgh j

end Taylor

section StepMod

variable {R : Type u} [CommRing R] {d : ℕ}

private theorem eq_single_of_degree_eq_one {m : Fin d →₀ ℕ} (h1 : m.degree = 1) :
    ∃ k, m = Finsupp.single k 1 := by
  have hne : m ≠ 0 := fun h => by rw [h, map_zero] at h1; omega
  obtain ⟨k, hk⟩ : ∃ k, m k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (Finsupp.ext hcon)
  have hle : Finsupp.single k 1 ≤ m := by rw [Finsupp.single_le_iff]; omega
  obtain ⟨e', he'⟩ := exists_add_of_le hle
  have hdeg : e'.degree = 0 := by
    have := congrArg Finsupp.degree he'
    rw [map_add, Finsupp.degree_single] at this
    omega
  rw [(Finsupp.degree_eq_zero_iff _).mp hdeg, add_zero] at he'
  exact ⟨k, he'⟩

private theorem mul_mem_span_pow_succ (p : R) (r : ℕ) {a b : R} (ha : a ∈ Ideal.span {p})
    (hb : b ∈ Ideal.span {p ^ r}) : a * b ∈ Ideal.span {p ^ (r + 1)} := by
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  exact Ideal.mem_span_singleton'.mpr ⟨u * v, by ring⟩

private theorem coeff_subst_sub_mem (p : R) (i : Fin d) (φi : MvPowerSeries (Fin d) R)
    (hlin : ∀ k, coeff (Finsupp.single k 1) φi = if i = k then 1 else 0)
    (hJi : ∀ (j : Fin d) (m : Fin d →₀ ℕ), 2 ≤ m.degree → ((m j : ℕ) : R) * coeff m φi ∈ Ideal.span
      {p})
    (H E : Fin d → MvPowerSeries (Fin d) R) (hH0 : ∀ j, (H j).constantCoeff = 0)
    (hE0 : ∀ j, (E j).constantCoeff = 0) (r : ℕ) (hr : 1 ≤ r)
    (hE : ∀ j, E j ∈ coefIdeal (Fin d) (p ^ r)) (n : Fin d →₀ ℕ) :
    coeff n (subst (H - E) φi) - coeff n (subst H φi) + coeff n (E i) ∈ Ideal.span {p ^ (r + 1)} :=
      by
  classical
  have hG0 : ∀ j, ((H - E) j).constantCoeff = 0 := fun j => by
    rw [Pi.sub_apply, map_sub, hH0, hE0, sub_zero]
  have hGS := hasSubst_of_constantCoeff_zero hG0
  have hHS := hasSubst_of_constantCoeff_zero hH0
  rw [coeff_subst hGS, coeff_subst hHS]

  let f1 : (Fin d →₀ ℕ) → R := fun m => coeff m φi • coeff n (m.prod fun j e => (H - E) j ^ e)
  let f2 : (Fin d →₀ ℕ) → R := fun m => coeff m φi • coeff n (m.prod fun j e => H j ^ e)
  have hf1 : (Function.support f1).Finite := coeff_subst_finite hGS φi n
  have hf2 : (Function.support f2).Finite := coeff_subst_finite hHS φi n
  let S : Finset (Fin d →₀ ℕ) := hf1.toFinset ∪ hf2.toFinset ∪ {Finsupp.single i 1}
  have hS1 : Function.support f1 ⊆ (S : Set (Fin d →₀ ℕ)) := by
    intro m hm; simp only [S, Finset.coe_union, Finset.coe_singleton]
    exact Or.inl (Or.inl (hf1.mem_toFinset.mpr hm))
  have hS2 : Function.support f2 ⊆ (S : Set (Fin d →₀ ℕ)) := by
    intro m hm; simp only [S, Finset.coe_union, Finset.coe_singleton]
    exact Or.inl (Or.inr (hf2.mem_toFinset.mpr hm))
  have hSi : Finsupp.single i 1 ∈ S := by simp [S]
  rw [finsum_eq_sum_of_support_subset f1 hS1, finsum_eq_sum_of_support_subset f2 hS2]

  have hind : coeff n (E i) = ∑ m ∈ S, if m = Finsupp.single i 1 then coeff n (E i) else 0 := by
    rw [Finset.sum_ite_eq' S, if_pos hSi]
  rw [hind, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Ideal.sum_mem _ fun m _ => ?_

  simp only [f1, f2, smul_eq_mul]
  rcases Nat.lt_or_ge m.degree 1 with h0 | h1
  · have hm : m = 0 := (Finsupp.degree_eq_zero_iff m).mp (by omega)
    subst hm
    rw [Finsupp.prod_zero_index, Finsupp.prod_zero_index, sub_self, zero_add,
      if_neg (Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero))]
    exact Ideal.zero_mem _
  rcases Nat.lt_or_ge m.degree 2 with h2 | h2
  · obtain ⟨k, rfl⟩ := eq_single_of_degree_eq_one (show m.degree = 1 by omega)
    rw [Finsupp.prod_single_index (h := fun j e => (H - E) j ^ e) (pow_zero _),
      Finsupp.prod_single_index (h := fun j e => H j ^ e) (pow_zero _), pow_one, pow_one, hlin,
      Pi.sub_apply, map_sub]
    by_cases hik : i = k
    · subst hik; rw [if_pos rfl, if_pos rfl]; ring_nf; exact Ideal.zero_mem _
    · rw [if_neg hik, if_neg (fun h => hik (Finsupp.single_left_injective one_ne_zero h).symm)]
      ring_nf; exact Ideal.zero_mem _
  · rw [if_neg (fun h => by rw [h, Finsupp.degree_single] at h2; omega), add_zero, ← mul_sub, ←
      map_sub]
    have hT := finsuppProd_sub_sub_sum_mem_sq (coefIdeal (Fin d) (p ^ r)) (H - E) H
      (fun j => by rw [Pi.sub_apply, sub_sub_cancel_left]; exact (neg_mem (hE j))) m
    set T := ∑ j ∈ m.support, ((m j : ℕ) : MvPowerSeries (Fin d) R) * H j ^ (m j - 1) *
      (∏ j' ∈ m.support.erase j, H j' ^ m j') * ((H - E) j - H j) with hTdef
    have hQ : (m.prod fun j e => (H - E) j ^ e) - (m.prod fun j e => H j ^ e) =
        T + ((m.prod fun j e => (H - E) j ^ e) - (m.prod fun j e => H j ^ e) - T) := by ring
    rw [hQ, map_add, mul_add]
    refine Ideal.add_mem _ ?_ ?_
    · rw [hTdef, map_sum, Finset.mul_sum]
      refine Ideal.sum_mem _ fun j hj => ?_
      have hfac : ((m j : ℕ) : MvPowerSeries (Fin d) R) * H j ^ (m j - 1) *
          (∏ j' ∈ m.support.erase j, H j' ^ m j') * ((H - E) j - H j)
          = ((m j : ℕ) : MvPowerSeries (Fin d) R) *
            (H j ^ (m j - 1) * (∏ j' ∈ m.support.erase j, H j' ^ m j') * (-E j)) := by
        rw [Pi.sub_apply, sub_sub_cancel_left]; ring
      rw [hfac, show ((m j : ℕ) : MvPowerSeries (Fin d) R) = C (m j : R) by
        rw [map_natCast], coeff_C_mul, ← mul_assoc, mul_comm (coeff m φi)]
      refine mul_mem_span_pow_succ p r (hJi j m h2) ?_
      have hmem : H j ^ (m j - 1) * (∏ j' ∈ m.support.erase j, H j' ^ m j') * (-E j)
          ∈ coefIdeal (Fin d) (p ^ r) :=
        Ideal.mul_mem_left _ _ ((neg_mem (hE j)))
      exact hmem n
    · have h2r : Ideal.span {(p ^ r) ^ 2} ≤ Ideal.span {p ^ (r + 1)} := by
        rw [Ideal.span_singleton_le_span_singleton, ← pow_mul]
        exact pow_dvd_pow p (by omega)
      have hmem := coefIdeal_mono (σ := Fin d) h2r (coefIdeal_sq_le (σ := Fin d) (p ^ r) hT) n
      exact Ideal.mul_mem_left _ _ hmem

end StepMod

section Restricted

variable {R : Type u} [CommRing R] {d : ℕ}

private def Restricted (p : R) (f : MvPowerSeries (Fin d) R) : Prop :=
  ∀ N : ℕ, ∀ᶠ n in Filter.cofinite, coeff n f ∈ Ideal.span {p ^ N}

private theorem Restricted.sub {p : R} {f g : MvPowerSeries (Fin d) R} (hf : Restricted p f)
    (hg : Restricted p g) : Restricted p (f - g) := fun N =>
  ((hf N).and (hg N)).mono fun n hn => by rw [map_sub]; exact Ideal.sub_mem _ hn.1 hn.2

private theorem restricted_coe (p : R) (χ : MvPolynomial (Fin d) R) :
    Restricted p (χ : MvPowerSeries (Fin d) R) := fun N => by
  refine Filter.eventually_cofinite.mpr (χ.support.finite_toSet.subset fun n hn => ?_)
  rw [Set.mem_setOf_eq, MvPolynomial.coeff_coe] at hn
  by_contra h
  exact hn (by rw [MvPolynomial.notMem_support_iff.mp h]; exact Ideal.zero_mem _)

private theorem restricted_X (p : R) (k : Fin d) : Restricted p (X k : MvPowerSeries (Fin d) R) :=
  by
  have := restricted_coe p (MvPolynomial.X k : MvPolynomial (Fin d) R)
  rwa [MvPolynomial.coe_X] at this

private theorem finsuppProd_pow_eq_prod_sigma (G : Fin d → MvPowerSeries (Fin d) R) (a : Fin d →₀
  ℕ) :
    (a.prod fun l e => G l ^ e) = ∏ x ∈ a.support.sigma fun l => Finset.range (a l), G x.1 := by
  rw [Finset.prod_sigma]
  refine Finset.prod_congr rfl fun l _ => ?_
  dsimp only
  rw [Finset.prod_const, Finset.card_range]

private theorem card_sigma_range (a : Fin d →₀ ℕ) :
    (a.support.sigma fun l => Finset.range (a l)).card = a.degree := by
  rw [Finset.card_sigma, Finsupp.degree_apply]
  exact Finset.sum_congr rfl fun l _ => Finset.card_range _

private theorem restricted_subst {p : R} {f : MvPowerSeries (Fin d) R} (hf : Restricted p f)
    {G : Fin d → MvPowerSeries (Fin d) R} (hG : ∀ j, Restricted p (G j))
    (hG0 : ∀ j, (G j).constantCoeff = 0) : Restricted p (MvPowerSeries.subst G f) := by
  classical
  intro N
  have hGS := hasSubst_of_constantCoeff_zero hG0

  have hSf := Filter.eventually_cofinite.mp (hf N)
  set M₀ : ℕ := hSf.toFinset.sup Finsupp.degree with hM₀
  have hTG : ∀ j, {n : Fin d →₀ ℕ | ¬ coeff n (G j) ∈ Ideal.span {p ^ N}}.Finite := fun j =>
    Filter.eventually_cofinite.mp (hG j N)
  set K : ℕ := Finset.univ.sup fun j => (hTG j).toFinset.sup Finsupp.degree with hK

  have key : ∀ n : Fin d →₀ ℕ, M₀ * K < n.degree → coeff n (MvPowerSeries.subst G f) ∈ Ideal.span
    {p ^ N} := by
    intro n hn
    rw [coeff_subst hGS]
    have hfin := coeff_subst_finite hGS f n
    rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by simp)]
    refine Ideal.sum_mem _ fun m _ => ?_
    rw [smul_eq_mul]
    by_cases hm : coeff m f ∈ Ideal.span {p ^ N}
    · exact Ideal.mul_mem_right _ _ hm
    · have hmdeg : m.degree ≤ M₀ := by
        rw [hM₀]; exact Finset.le_sup (hSf.mem_toFinset.mpr hm)
      refine Ideal.mul_mem_left _ _ ?_
      rw [finsuppProd_pow_eq_prod_sigma, coeff_prod]
      refine Ideal.sum_mem _ fun v hv => ?_
      rw [Finset.mem_finsuppAntidiag] at hv
      obtain ⟨hsum, -⟩ := hv
      set I := m.support.sigma fun l => Finset.range (m l) with hI

      obtain ⟨x, hxI, hxK⟩ : ∃ x ∈ I, K < (v x).degree := by
        by_contra hcon
        push Not at hcon
        have h1 : ∑ x ∈ I, (v x).degree ≤ I.card * K := by
          have := Finset.sum_le_card_nsmul I (fun x => (v x).degree) K hcon
          simpa using this
        have h2 : ∑ x ∈ I, (v x).degree = n.degree := by rw [← map_sum, hsum]
        have h3 : I.card = m.degree := card_sigma_range m
        rw [h2, h3] at h1
        have : m.degree * K ≤ M₀ * K := Nat.mul_le_mul_right _ hmdeg
        omega
      have hx : coeff (v x) (G x.1) ∈ Ideal.span {p ^ N} := by
        by_contra hcon
        have h1 : (v x).degree ≤ (hTG x.1).toFinset.sup Finsupp.degree :=
          Finset.le_sup ((hTG x.1).mem_toFinset.mpr hcon)
        have h2 : (hTG x.1).toFinset.sup Finsupp.degree ≤ K := by
          rw [hK]; exact Finset.le_sup (f := fun j => (hTG j).toFinset.sup Finsupp.degree)
            (Finset.mem_univ _)
        omega
      rw [← Finset.mul_prod_erase _ _ hxI]
      exact Ideal.mul_mem_right _ _ hx
  refine Filter.eventually_cofinite.mpr ((Finsupp.finite_of_degree_le (M₀ * K)).subset fun n hn =>
    ?_)
  by_contra hcon
  exact hn (key n (by simpa using hcon))

end Restricted



end RestrictedFormalInverseAux

open RestrictedFormalInverseAux in
/-- A formal inverse of a restricted family of power series is restricted,
given a polynomial inverse modulo `p` and the stated derivative divisibility. -/
public theorem
    MvPowerSeries.eventually_coeff_mem_span_pow_of_subst_eq_X_of_exists_polynomial_inverse_mod
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) {d : ℕ}
    (φ ψ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0) (hφ1 : linearPart φ = 1)
    (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hJ : ∀ (i j : Fin d) (m : Fin d →₀ ℕ), 2 ≤ m.degree →
      ((m j : ℕ) : 𝓞) * (φ i).coeff m ∈ Ideal.span {(p : 𝓞)})
    (hψφ : ∀ i, subst φ (ψ i) = X i)
    (χ : Fin d → MvPolynomial (Fin d) 𝓞) (hχ0 : ∀ i, MvPolynomial.constantCoeff (χ i) = 0)
    (hχ : ∀ (i : Fin d) (m : Fin d →₀ ℕ),
      (subst (fun j => (χ j : MvPowerSeries (Fin d) 𝓞)) (φ i)).coeff m -
        (X i : MvPowerSeries (Fin d) 𝓞).coeff m ∈ Ideal.span {(p : 𝓞)}) :
    ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (ψ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N} := by

  classical

  have hφS : HasSubst φ := hasSubst_of_constantCoeff_zero hφ0
  have hlin : ∀ i k, coeff (Finsupp.single k 1) (φ i) = if i = k then 1 else 0 := fun i k => by
    have := congrFun (congrFun hφ1 i) k
    simpa [MvPowerSeries.linearPart, Matrix.one_apply] using this

  let G : ℕ → Fin d → MvPowerSeries (Fin d) 𝓞 := fun r =>
    Nat.rec (fun j => (χ j : MvPowerSeries (Fin d) 𝓞))
      (fun _ Gr j => Gr j - (subst Gr (φ j) - X j)) r
  have hG0 : G 0 = fun j => (χ j : MvPowerSeries (Fin d) 𝓞) := rfl
  have hGs : ∀ r, G (r + 1) = fun j => G r j - (subst (G r) (φ j) - X j) := fun r => rfl

  have claim : ∀ r : ℕ, (∀ j, (G r j).constantCoeff = 0) ∧ (∀ j,
    RestrictedFormalInverseAux.Restricted (p : 𝓞) (G r j)) ∧
      (∀ (j : Fin d) (n : Fin d →₀ ℕ),
        coeff n (subst (G r) (φ j) - X j) ∈ Ideal.span {(p : 𝓞) ^ (r + 1)}) := by
    intro r
    induction r with
    | zero =>
      refine ⟨fun j => ?_, fun j => ?_, fun j n => ?_⟩
      · rw [hG0]; show constantCoeff ((χ j : MvPowerSeries (Fin d) 𝓞)) = 0
        rw [← coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
        exact hχ0 j
      · rw [hG0]; exact RestrictedFormalInverseAux.restricted_coe _ _
      · rw [hG0, pow_one, map_sub]; exact hχ j n
    | succ r IH =>
      obtain ⟨IH0, IHT, IHc⟩ := IH

      have hE0 : ∀ j, (subst (G r) (φ j) - X j).constantCoeff = 0 := fun j => by
        rw [map_sub, constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero IH0) IH0 (hφ0 j),
          constantCoeff_X, sub_zero]
      have hE : ∀ j, subst (G r) (φ j) - X j ∈ RestrictedFormalInverseAux.coefIdeal (Fin d) ((p :
        𝓞) ^ (r + 1)) :=
        fun j n => IHc j n
      refine ⟨fun j => ?_, fun j => ?_, fun j n => ?_⟩
      · rw [hGs]; show constantCoeff (G r j - (subst (G r) (φ j) - X j)) = 0
        rw [map_sub, IH0, hE0, sub_zero]
      · rw [hGs]
        exact (IHT j).sub ((RestrictedFormalInverseAux.restricted_subst (hφT · j) IHT IH0).sub
          (RestrictedFormalInverseAux.restricted_X _ j))
      · have hstep := RestrictedFormalInverseAux.coeff_subst_sub_mem (p : 𝓞) j (φ j) (hlin j) (hJ
          j) (G r)
          (fun k => subst (G r) (φ k) - X k) IH0 hE0 (r + 1) (by omega) hE n
        have hGr1 : G (r + 1) = G r - fun k => subst (G r) (φ k) - X k := by
          rw [hGs]; rfl
        rw [hGr1]
        have : coeff n (subst (G r - fun k => subst (G r) (φ k) - X k) (φ j) - X j)
            = coeff n (subst (G r - fun k => subst (G r) (φ k) - X k) (φ j)) - coeff n (subst (G r)
              (φ j))
              + coeff n (subst (G r) (φ j) - X j) := by
          rw [map_sub, map_sub]; ring
        rw [this]
        exact hstep

  have hψG : ∀ (r : ℕ) (i : Fin d) (n : Fin d →₀ ℕ),
      coeff n (ψ i) - coeff n (G r i) ∈ Ideal.span {(p : 𝓞) ^ (r + 1)} := by
    intro r i n
    obtain ⟨hr0, -, hrc⟩ := claim r
    have hGS : HasSubst (G r) := hasSubst_of_constantCoeff_zero hr0

    have h1 : G r i = subst (fun j => subst (G r) (φ j)) (ψ i) := by
      rw [← subst_comp_subst_apply hφS hGS, hψφ i, subst_X hGS]
    have hF0 : ∀ j, (subst (G r) (φ j)).constantCoeff = 0 := fun j =>
      constantCoeff_subst_eq_zero hGS hr0 (hφ0 j)
    have hFS : HasSubst (fun j => subst (G r) (φ j)) := hasSubst_of_constantCoeff_zero hF0
    have hXS : HasSubst (X : Fin d → MvPowerSeries (Fin d) 𝓞) := hasSubst_of_constantCoeff_zero fun
      j => constantCoeff_X j
    have h2 : coeff n (ψ i) = coeff n (subst (X : Fin d → MvPowerSeries (Fin d) 𝓞) (ψ i)) := by
      rw [subst_self]; rfl
    rw [h1, h2, coeff_subst hXS, coeff_subst hFS]
    have hfX := coeff_subst_finite hXS (ψ i) n
    have hfF := coeff_subst_finite hFS (ψ i) n
    let S : Finset (Fin d →₀ ℕ) := hfX.toFinset ∪ hfF.toFinset
    have hS1 : (Function.support fun m => coeff m (ψ i) • coeff n (m.prod fun s e => (X s :
      MvPowerSeries (Fin d) 𝓞) ^ e))
        ⊆ (S : Set (Fin d →₀ ℕ)) := fun m hm =>
      Finset.mem_coe.mpr (Finset.mem_union_left _ (hfX.mem_toFinset.mpr hm))
    have hS2 : (Function.support fun m => coeff m (ψ i) • coeff n (m.prod fun s e => subst (G r) (φ
      s) ^ e))
        ⊆ (S : Set (Fin d →₀ ℕ)) := fun m hm =>
      Finset.mem_coe.mpr (Finset.mem_union_right _ (hfF.mem_toFinset.mpr hm))
    rw [finsum_eq_sum_of_support_subset _ hS1, finsum_eq_sum_of_support_subset _ hS2,
      ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun m _ => ?_
    rw [smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub]
    refine Ideal.mul_mem_left _ _ ?_
    have hdiff : ∀ j, (X j : MvPowerSeries (Fin d) 𝓞) - subst (G r) (φ j)
        ∈ RestrictedFormalInverseAux.coefIdeal (Fin d) ((p : 𝓞) ^ (r + 1)) := fun j => by
      rw [← neg_sub]
      exact neg_mem (fun n' => hrc j n')
    exact RestrictedFormalInverseAux.finsuppProd_sub_finsuppProd_mem
      (RestrictedFormalInverseAux.coefIdeal (Fin d) ((p : 𝓞) ^ (r + 1)))
      (X : Fin d → MvPowerSeries (Fin d) 𝓞) (fun j => subst (G r) (φ j)) hdiff m n

  intro N i
  obtain ⟨-, hT, -⟩ := claim N
  refine (hT i N).mono fun n hn => ?_
  have h := hψG N i n
  have hle : Ideal.span {(p : 𝓞) ^ (N + 1)} ≤ Ideal.span {(p : 𝓞) ^ N} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ N))
  have : coeff n (ψ i) = (coeff n (ψ i) - coeff n (G N i)) + coeff n (G N i) := by ring
  rw [this]
  exact Ideal.add_mem _ (hle h) hn
