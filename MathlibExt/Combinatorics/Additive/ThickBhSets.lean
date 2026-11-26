/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
public import MathlibExt.Combinatorics.Additive.BhSet
public import MathlibExt.Combinatorics.Additive.SingerSet
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.List.Perm.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

open Polynomial

private noncomputable def linePolynomial {F : Type*} [Field F] : Option F → F[X]
  | none => 1
  | some t => X - C t

private theorem linePolynomial_monic {F : Type*} [Field F] (t : Option F) :
    (linePolynomial t).Monic := by
  cases t <;> simp [linePolynomial, monic_X_sub_C, monic_one]

private theorem linePolynomial_degree {F : Type*} [Field F] (t : Option F) :
    (linePolynomial t).natDegree ≤ 1 := by
  cases t <;> simp [linePolynomial]

private theorem product_degree {F : Type*} [Field F] (l : List (Option F)) :
    (l.map linePolynomial).prod.natDegree ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    exact (natDegree_mul_le ..).trans (by have := linePolynomial_degree a; omega)

private theorem product_monic {F : Type*} [Field F] (l : List (Option F)) :
    (l.map linePolynomial).prod.Monic := by
  induction l with
  | nil => simp
  | cons a l ih => simpa using (linePolynomial_monic a).mul ih

private theorem product_roots {F : Type*} [Field F] (l : List (Option F)) :
    (l.map linePolynomial).prod.roots = (l.filterMap id : Multiset F) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, roots_mul
      (mul_ne_zero (linePolynomial_monic a).ne_zero (product_monic l).ne_zero), ih]
    cases a <;> simp [linePolynomial]

private theorem option_perm {F : Type*} (l₁ l₂ : List (Option F))
    (hlen : l₁.length = l₂.length)
    (hroots : (l₁.filterMap id : Multiset F) = (l₂.filterMap id : Multiset F)) :
    l₁.Perm l₂ := by
  classical
  have hcount (l : List (Option F)) (a : F) :
      l.count (some a) = (l.filterMap id).count a := by
    induction l with
    | nil => simp
    | cons b l ih =>
      cases b with
      | none => simp [ih]
      | some b =>
        by_cases h : a = b
        · subst b; simp [ih]
        · simp [ih, Ne.symm h]
  have hlength (l : List (Option F)) :
      l.length = l.count none + (l.filterMap id).length := by
    induction l with
    | nil => simp
    | cons b l ih => cases b <;> simp [ih, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]
  have hp : (l₁.filterMap id).Perm (l₂.filterMap id) := Quotient.exact hroots
  apply List.perm_iff_count.mpr
  intro a
  cases a with
  | none => have := hp.length_eq; have := hlength l₁; have := hlength l₂; omega
  | some a => rw [hcount, hcount]; exact hp.count_eq a

private theorem polynomial_eq_of_aeval {F K : Type*} [Field F] [Field K] [Algebra F K]
    {x : K} {d : ℕ} (hx : (minpoly F x).natDegree = d + 1)
    {p q : F[X]} (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (he : aeval x p = aeval x q) : p = q := by
  apply sub_eq_zero.mp
  by_contra hn
  have hd := natDegree_le_of_dvd (minpoly.dvd F x (by simpa using sub_eq_zero.mpr he)) hn
  have hsub := natDegree_sub_le p q
  rw [hx] at hd
  omega

private theorem sumNE_eq_sum {G : Type*} [AddCommMonoid G] (l : List G) (e : l ≠ []) :
    AdditiveCombinatorics.sumNE l e = l.sum := by
  cases l with
  | nil => exact (e rfl).elim
  | cons a l =>
    change l.foldl (· + ·) a = a + l.sum
    induction l generalizing a with
    | nil => simp
    | cons b l ih => simp [ih, add_assoc]

private theorem exists_pow {K : Type*} [Field K] [Fintype K] {θ c : K}
    (hθ₀ : θ ≠ 0) (hθ : orderOf θ = Fintype.card K - 1) (hc : c ≠ 0) :
    ∃ k : ℕ, θ ^ k = c := by
  classical
  let g := Units.mk0 θ hθ₀
  have hg : Subgroup.zpowers g = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top _).mp
    rw [Nat.card_zpowers, ← orderOf_units, Nat.card_eq_fintype_card, Fintype.card_units]
    exact hθ
  have hmem : Units.mk0 c hc ∈ Submonoid.powers g := by
    rw [mem_powers_iff_mem_zpowers, hg]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := hmem
  exact ⟨k, congrArg Units.val hk⟩

private theorem pow_decompose {F K : Type*} [Field F] [Field K] [Algebra F K]
    {θ : K} {ν : F} {M : ℕ} (hnorm : algebraMap F K ν = θ ^ M) (a : ℕ) :
    θ ^ a = algebraMap F K (ν ^ (a / M)) * θ ^ (a % M) := by
  rw [map_pow, hnorm, ← pow_mul, ← pow_add, Nat.div_add_mod]

private theorem pow_scale {F K : Type*} [Field F] [Field K] [Algebra F K]
    {θ : K} {ν : F} {M a b : ℕ} (hν : ν ≠ 0)
    (hnorm : algebraMap F K ν = θ ^ M) (hab : (a : ZMod M) = b) :
    ∃ c : F, c ≠ 0 ∧ θ ^ a = algebraMap F K c * θ ^ b := by
  have hm := (ZMod.natCast_eq_natCast_iff' a b M).mp hab
  refine ⟨ν ^ (a / M) / ν ^ (b / M), div_ne_zero (pow_ne_zero _ hν)
    (pow_ne_zero _ hν), ?_⟩
  rw [pow_decompose hnorm a, pow_decompose hnorm b, map_div₀, ← mul_assoc,
    div_mul_cancel₀ _ ((map_ne_zero_iff _ (algebraMap F K).injective).mpr (pow_ne_zero _ hν)), hm]

private theorem cast_eq_of_scale {F K : Type*} [Field F] [Fintype F] [Field K]
    [Fintype K] [Algebra F K] {θ : K} {M a b : ℕ}
    (hθ : orderOf θ = Fintype.card K - 1)
    (hM : M * (Fintype.card F - 1) = Fintype.card K - 1)
    {c : F} (hc : c ≠ 0) (he : θ ^ a = algebraMap F K c * θ ^ b) :
    (a : ZMod M) = b := by
  have hord : 0 < orderOf θ := by rw [hθ]; exact Nat.sub_pos_of_lt Fintype.one_lt_card
  have hp := congrArg (fun z : K => z ^ (Fintype.card F - 1)) he
  rw [mul_pow, ← map_pow, FiniteField.pow_card_sub_one_eq_one c hc, map_one,
    one_mul, ← pow_mul, ← pow_mul] at hp
  have hm := (orderOf_pos_iff.mp hord).pow_eq_pow_iff_modEq.mp hp
  rw [hθ, ← hM] at hm
  exact (ZMod.natCast_eq_natCast_iff a b M).mpr
    (Nat.ModEq.mul_right_cancel' (by have : 1 < Fintype.card F := Fintype.one_lt_card; omega) hm)

private theorem line_eval_ne_zero {F K : Type*} [Field F] [Field K] [Algebra F K]
    {x : K} (hx : x ∉ (algebraMap F K).range) (t : Option F) :
    aeval x (linePolynomial t) ≠ 0 := by
  cases t with
  | none => simp [linePolynomial]
  | some t => simpa [linePolynomial, sub_eq_zero] using fun h => hx ⟨t, h.symm⟩

private theorem product_eval {F K : Type*} [Field F] [Field K] [Algebra F K]
    {θ x : K} (k : Option F → ℕ)
    (hk : ∀ t, θ ^ k t = aeval x (linePolynomial t)) (l : List (Option F)) :
    θ ^ (l.map k).sum = aeval x (l.map linePolynomial).prod := by
  induction l with
  | nil => simp
  | cons t l ih => simp [pow_add, hk, ih]

private theorem lift_list {A B : Type*} (f : A → B) (l : List B)
    (hl : ∀ a ∈ l, ∃ t, f t = a) : ∃ L : List A, L.map f = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a l ih =>
    obtain ⟨t, ht⟩ := hl a (by simp)
    obtain ⟨L, hL⟩ := ih (fun a ha => hl a (by simp [ha]))
    exact ⟨t :: L, by simp [ht, hL]⟩

@[expose] public section

/-- **Singer's construction of $B_h$-sets.** Let $h \ge 2$, let $F$ be a finite field with $q$
elements, let $K$ be a field extension of $F$ of degree $h + 1$, let $\theta$ be a generator of
the multiplicative group $K^\times$, and let $b$ be a natural number such that $\theta^b$ has
degree $h + 1$ over $F$. Then the generalized Singer set $\mathrm{Singer}_h(q, b)$, a subset of
$\mathbb{Z}/M\mathbb{Z}$ with $M = (q^{h+1} - 1)/(q - 1)$, is a $B_h$-set with exactly $q + 1$
elements.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 3 (second sentence) (`jis-2024-24.1.2-thm-3`). -/
public theorem isBhSet_singerSet {F K : Type*} [Field F] [Fintype F] [Field K]
    [Fintype K] [Algebra F K] {h : ℕ} (hh : 2 ≤ h) (hK : Module.finrank F K = h + 1) {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) {b : ℕ}
    (hb : (minpoly F (θ ^ b)).natDegree = h + 1) :
    AdditiveCombinatorics.IsBhSet (singerSet F h θ b) h ∧
      (singerSet F h θ b).ncard = Fintype.card F + 1 := by
  classical
  let q := Fintype.card F
  let M := (q ^ (h + 1) - 1) / (q - 1)
  have hq : 1 < q := Fintype.one_lt_card
  have hcard : Fintype.card K = q ^ (h + 1) := by
    rw [Module.card_eq_pow_finrank (K := F), hK]
  have hM : M * (Fintype.card F - 1) = Fintype.card K - 1 := by
    rw [hcard]
    exact Nat.div_mul_cancel (Nat.sub_one_dvd_pow_sub_one q (h + 1))
  have : NeZero M := ⟨(Nat.div_pos
    (Nat.sub_le_sub_right (Nat.le_pow (by omega)) 1) (by omega)).ne'⟩
  have hord : 0 < orderOf θ := by
    rw [hθ]
    exact Nat.sub_pos_of_lt Fintype.one_lt_card
  have hθ₀ : θ ≠ 0 := by rintro rfl; simp at hord
  have hx : θ ^ b ∉ (algebraMap F K).range := fun hx => by
    have := minpoly.natDegree_eq_one_iff.mpr hx
    omega
  let ν := Algebra.norm F θ
  have hν : ν ≠ 0 := Algebra.norm_ne_zero_iff.mpr hθ₀
  have hnorm : algebraMap F K ν = θ ^ M := by
    rw [FiniteField.algebraMap_norm_eq_pow, Module.natCard_eq_pow_finrank (K := F) (V := K),
      hK, Nat.card_eq_fintype_card]
  choose k hk using fun t : Option F => exists_pow hθ₀ hθ (line_eval_ne_zero hx t)
  let f : Option F → ZMod M := fun t => k t
  have hf : Function.Injective f := by
    intro t s hts
    obtain ⟨c, hc, he⟩ := pow_scale hν hnorm hts
    rw [hk t, hk s] at he
    have hp : linePolynomial t = C c * linePolynomial s :=
      polynomial_eq_of_aeval hb ((linePolynomial_degree t).trans (by omega))
        ((natDegree_C_mul_le c _).trans ((linePolynomial_degree s).trans (by omega)))
        (by simpa using he)
    have hr := congrArg Polynomial.roots hp
    rw [roots_C_mul _ hc] at hr
    cases t <;> cases s <;>
      simp only [linePolynomial, roots_one, Multiset.empty_eq_zero, roots_X_sub_C,
        Multiset.zero_ne_singleton, Multiset.singleton_ne_zero, Multiset.singleton_inj,
        Option.some.injEq] at hr ⊢
    exact hr
  have hmem (t : Option F) : f t ∈ singerSet F h θ b := by
    obtain ⟨c, hc, he⟩ := pow_scale hν hnorm (a := (f t).val) (b := k t)
      (ZMod.natCast_zmod_val (f t))
    rw [hk t] at he
    cases t with
    | none => exact ⟨0, c, by simpa [linePolynomial] using he⟩
    | some t =>
      refine ⟨c, -c * t, ?_⟩
      rw [he]
      simp only [linePolynomial, map_sub, aeval_X, aeval_C, map_mul, map_neg]
      ring
  have hsurj (a : ZMod M) (ha : a ∈ singerSet F h θ b) : ∃ t, f t = a := by
    obtain ⟨u, v, huv⟩ := ha
    by_cases hu : u = 0
    · subst u
      have hv : v ≠ 0 := by
        intro hv
        apply pow_ne_zero a.val hθ₀
        simpa only [hv, map_zero, zero_mul, add_zero] using huv
      refine ⟨none, ?_⟩
      have he : θ ^ a.val = algebraMap F K v * θ ^ k none := by
        simpa [hk, linePolynomial] using huv
      have heq := cast_eq_of_scale hθ hM hv he
      simpa [f] using heq.symm
    · refine ⟨some (-v / u), ?_⟩
      have he : θ ^ a.val = algebraMap F K u * θ ^ k (some (-v / u)) := by
        rw [hk, linePolynomial]
        simp only [map_sub, aeval_X, aeval_C, map_neg, map_div₀]
        rw [huv, neg_div, sub_neg_eq_add, mul_add,
          mul_comm (algebraMap F K u) (algebraMap F K v / algebraMap F K u),
          div_mul_cancel₀ _ ((map_ne_zero_iff _ (algebraMap F K).injective).mpr hu)]
      have heq := cast_eq_of_scale hθ hM hu he
      simpa [f] using heq.symm
  have hset : singerSet F h θ b = Set.range f := by
    ext a
    exact ⟨hsurj a, fun ⟨t, ht⟩ => ht ▸ hmem t⟩
  refine ⟨⟨⟨f none, hmem none⟩, by omega, ?_⟩, ?_⟩
  · intro l₁ l₂ hl₁ hl₂ hlen₁ hlen₂ e₁ e₂ he
    obtain ⟨L₁, rfl⟩ := lift_list f l₁ (fun a ha => hsurj a (hl₁ a ha))
    obtain ⟨L₂, rfl⟩ := lift_list f l₂ (fun a ha => hsurj a (hl₂ a ha))
    have hL₁ : L₁.length = h := by simpa using hlen₁
    have hL₂ : L₂.length = h := by simpa using hlen₂
    rw [sumNE_eq_sum, sumNE_eq_sum] at he
    have hcast (L : List (Option F)) : ((L.map k).sum : ZMod M) = (L.map f).sum := by
      induction L with
      | nil => simp
      | cons t L ih => simp [f, ih]
    obtain ⟨c, hc, heval⟩ := pow_scale hν hnorm
      ((hcast L₁).trans (he.trans (hcast L₂).symm))
    rw [product_eval k hk, product_eval k hk] at heval
    have hp : (L₁.map linePolynomial).prod = C c * (L₂.map linePolynomial).prod :=
      polynomial_eq_of_aeval hb (by simpa [hL₁] using product_degree L₁)
        ((natDegree_C_mul_le c _).trans (by simpa [hL₂] using product_degree L₂))
        (by simpa using heval)
    have hr := congrArg Polynomial.roots hp
    rw [roots_C_mul _ hc, product_roots, product_roots] at hr
    exact (option_perm L₁ L₂ (hL₁.trans hL₂.symm) hr).map f
  · rw [hset, Set.ncard_range_of_injective hf, Nat.card_eq_fintype_card, Fintype.card_option]

end

end MetaMathlibExt
