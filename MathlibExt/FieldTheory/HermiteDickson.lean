/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Div
public import MathlibExt.FieldTheory.Finite.PermutationPolynomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

@[expose] public section

namespace MathlibExt.FieldTheory.HermiteDickson

/-!
# Hermite–Dickson criterion for permutation polynomials

A polynomial `f` over a finite field `F_q` of characteristic `p` permutes `F_q` if and only if
it has exactly one root in `F_q` and, for every `1 ≤ t ≤ q - 2` with `p ∤ t`, the reduction of
`f ^ t` modulo `X ^ q - X` has degree at most `q - 2`.
-/

-- Helper: `X ^ q - X` is monic for `q ≥ 2`.
private theorem hd_monic {Fq : Type*} [Field Fq] [Fintype Fq]
    (hq : 2 ≤ Fintype.card Fq) :
    (Polynomial.X ^ Fintype.card Fq - Polynomial.X : Polynomial Fq).Monic := by
  refine Polynomial.monic_X_pow_sub ?_
  rw [Polynomial.degree_X]
  norm_cast

-- Helper: `X ^ q - X` vanishes on all of `Fq` (Fermat).
private theorem hd_eval_zero {Fq : Type*} [Field Fq] [Fintype Fq]
    (x : Fq) : Polynomial.eval x
      (Polynomial.X ^ Fintype.card Fq - Polynomial.X : Polynomial Fq) = 0 := by
  simp [Polynomial.eval_sub, Polynomial.eval_pow, FiniteField.pow_card]

-- Helper: reduction mod `X ^ q - X` preserves evaluation on `Fq`.
private theorem hd_mod_eval {Fq : Type*} [Field Fq] [Fintype Fq]
    (hq : 2 ≤ Fintype.card Fq)
    (g : Polynomial Fq) (x : Fq) :
    Polynomial.eval x (g % (Polynomial.X ^ Fintype.card Fq - Polynomial.X : Polynomial Fq))
      = Polynomial.eval x g := by
  have hmonic : (Polynomial.X ^ Fintype.card Fq - Polynomial.X : Polynomial Fq).Monic :=
    hd_monic hq
  rw [← Polynomial.modByMonic_eq_mod _ hmonic]
  have h := Polynomial.eval₂_modByMonic_eq_self_of_root (R := Fq) (S := Fq)
    (f := RingHom.id Fq) (p := g)
    (q := (Polynomial.X ^ Fintype.card Fq - Polynomial.X : Polynomial Fq)) (x := x)
  simpa using h (by simpa using hd_eval_zero x)

-- Helper: a polynomial of `natDegree ≤ q - 2` sums to zero over `Fq`.
private theorem hd_sum_eval_eq_zero_of_natDegree_le {Fq : Type*} [Field Fq] [Fintype Fq]
    (g : Polynomial Fq)
    (hdeg : g.natDegree ≤ Fintype.card Fq - 2)
    (hq : 2 ≤ Fintype.card Fq) :
    ∑ x : Fq, g.eval x = 0 := by
  conv_lhs => arg 2; ext x; rw [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Finset.mem_range] at hi
  have hi_lt : i < Fintype.card Fq - 1 := by omega
  have hsum : (∑ x : Fq, x ^ i) = 0 :=
    FiniteField.sum_pow_lt_card_sub_one Fq i hi_lt
  rw [← Finset.mul_sum, hsum, mul_zero]

-- Helper: a bijective evaluation map has exactly one root.
private theorem hd_card_roots_eq_one_of_bijective {Fq : Type*} [Field Fq] [Fintype Fq]
    [DecidableEq Fq] (f : Polynomial Fq)
    (hbij : Function.Bijective fun x => f.eval x) :
    (Finset.univ.filter (fun x => Polynomial.eval x f = 0)).card = 1 := by
  obtain ⟨a, ha⟩ := hbij.2 0
  have huniq : ∀ x, Polynomial.eval x f = 0 → x = a := by
    intro x hx
    have hx' : (fun x => f.eval x) x = (fun x => f.eval x) a := by
      simpa [ha] using hx
    exact hbij.1 hx'
  have hfilter : Finset.univ.filter (fun x => Polynomial.eval x f = 0) = {a} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hx; exact huniq x hx
    · intro hx; rw [hx]; simpa using ha
  rw [hfilter, Finset.card_singleton]

-- Helper: power sums reindex along a permutation polynomial.
private theorem hd_sum_pow_comp_bij {Fq : Type*} [Field Fq] [Fintype Fq]
    (f : Polynomial Fq) (t : ℕ)
    (hbij : Function.Bijective fun x => f.eval x) :
    (∑ x : Fq, (f.eval x) ^ t) = ∑ y : Fq, y ^ t := by
  let e : Fq ≃ Fq := Equiv.ofBijective (fun x => f.eval x) hbij
  have he : ∀ x, e x = f.eval x := fun x => rfl
  have h := Equiv.sum_comp e (fun y => y ^ t)
  simpa [e, he] using h

-- Helper: `natDegree (X ^ q - X) = q`.
private theorem hd_natDegree_X_pow_sub {Fq : Type*} [Field Fq] [Fintype Fq]
    (hq : 2 ≤ Fintype.card Fq) :
    (Polynomial.X ^ Fintype.card Fq - Polynomial.X : Polynomial Fq).natDegree =
      Fintype.card Fq := by
  have hlt : (Polynomial.X : Polynomial Fq).natDegree <
      ((Polynomial.X : Polynomial Fq) ^ Fintype.card Fq).natDegree := by
    rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]
    omega
  have h := Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt
  rwa [Polynomial.natDegree_X_pow] at h

-- Helper: the field size vanishes in the field.
private theorem hd_card_cast_eq_zero {p : ℕ} {Fq : Type*} [Field Fq] [Fintype Fq]
    [CharP Fq p] [Fact p.Prime] :
    (Fintype.card Fq : Fq) = 0 := by
  obtain ⟨n, _, hcard⟩ := FiniteField.card Fq p
  rw [hcard]
  simp

-- Helper: the `(q - 1)`-st power sum over the whole field is `-1`.
private theorem hd_sum_pow_card_sub_one {p : ℕ} {Fq : Type*} [Field Fq] [Fintype Fq]
    [CharP Fq p] [Fact p.Prime]
    (hq : 2 ≤ Fintype.card Fq) :
    (∑ x : Fq, x ^ (Fintype.card Fq - 1)) = -1 := by
  classical
  have hq1 : Fintype.card Fq - 1 ≠ 0 := by omega
  have hfun : ∀ x : Fq, x ^ (Fintype.card Fq - 1) = if x = 0 then 0 else 1 := by
    intro x
    by_cases hx : x = 0
    · simp [hx, zero_pow hq1]
    · simp [hx, FiniteField.pow_card_sub_one_eq_one x hx]
  simp_rw [hfun]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_const, Finset.filter_ne']
  simp only [nsmul_eq_mul, mul_one]
  have hcard0 : (Fintype.card Fq : Fq) = 0 := hd_card_cast_eq_zero
  have hcard_erase : (Finset.univ.erase (0 : Fq)).card = Fintype.card Fq - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
  rw [hcard_erase]
  have hcast : ((Fintype.card Fq - 1 : ℕ) : Fq) = -1 := by
    have h1 : ((Fintype.card Fq : ℕ) : Fq) =
        (((Fintype.card Fq - 1 : ℕ) : Fq) + 1) := by
      have h2 : Fintype.card Fq = (Fintype.card Fq - 1) + 1 := by omega
      conv_lhs => rw [h2]
      simp
    rw [hcard0] at h1
    have h2 := eq_neg_of_add_eq_zero_left h1.symm
    simpa using h2
  exact hcast

-- Helper: if `natDegree g = q - 1` then the sum of `g` is the negated top coefficient.
private theorem hd_sum_eq_neg_coeff_top {p : ℕ} {Fq : Type*} [Field Fq] [Fintype Fq]
    [CharP Fq p] [Fact p.Prime]
    (hq : 2 ≤ Fintype.card Fq) (g : Polynomial Fq)
    (hdeg : g.natDegree = Fintype.card Fq - 1) :
    ∑ x : Fq, g.eval x = - g.coeff (Fintype.card Fq - 1) := by
  have hsum_mid : ∀ i : ℕ, i < Fintype.card Fq - 1 → (∑ x : Fq, x ^ i) = 0 :=
    fun i hi => FiniteField.sum_pow_lt_card_sub_one Fq i hi
  have hsum_top : (∑ x : Fq, x ^ (Fintype.card Fq - 1)) = -1 :=
    hd_sum_pow_card_sub_one hq
  conv_lhs => arg 2; ext x; rw [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_comm]
  rw [hdeg, Finset.sum_range_succ]
  have hrest :
      (∑ i ∈ Finset.range (Fintype.card Fq - 1),
        ∑ x : Fq, g.coeff i * x ^ i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [← Finset.mul_sum, hsum_mid i (by omega), mul_zero]
  rw [hrest, zero_add, ← Finset.mul_sum, hsum_top, mul_neg, mul_one]

-- Helper: power sums `∑ f(x)^t` vanish for `1 ≤ t ≤ q - 2` under the degree hypothesis.
private theorem hd_sum_pow_eq_zero_of_hyp {p : ℕ} {Fq : Type*} [Field Fq] [Fintype Fq]
    [CharP Fq p] [Fact p.Prime]
    (f : Polynomial Fq) (hq : 2 ≤ Fintype.card Fq)
    (hdeg : ∀ t : ℕ, 1 ≤ t → t ≤ Fintype.card Fq - 2 → ¬ p ∣ t →
      ((f ^ t) % (Polynomial.X ^ Fintype.card Fq - Polynomial.X :
        Polynomial Fq)).natDegree ≤ Fintype.card Fq - 2)
    (t : ℕ) (h1 : 1 ≤ t) (h2 : t ≤ Fintype.card Fq - 2) :
    ∑ x : Fq, (f.eval x) ^ t = 0 := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases hpdvd : p ∣ t
    · obtain ⟨s, hs⟩ := hpdvd
      have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
      have hs_pos : 1 ≤ s := by
        by_contra hcon
        push Not at hcon
        have hs0 : s = 0 := by omega
        rw [hs0, mul_zero] at hs
        omega
      have hs_lt : s < t := by
        have h0 : 0 < s := by omega
        have hlt : s < p * s := lt_mul_of_one_lt_left h0 hp1
        omega
      have hs_le : s ≤ Fintype.card Fq - 2 := le_trans (le_of_lt hs_lt) h2
      have ihs := ih s hs_lt hs_pos hs_le
      have hfro : (∑ x : Fq, (f.eval x) ^ s) ^ p =
          ∑ x : Fq, ((f.eval x) ^ s) ^ p := by
        have h2 := map_sum (frobenius Fq p) (fun x => (f.eval x) ^ s) Finset.univ
        rw [frobenius_def] at h2
        simp only [frobenius_def] at h2
        exact h2
      have hexp : ∀ x : Fq, ((f.eval x) ^ s) ^ p = (f.eval x) ^ t := by
        intro x
        rw [← pow_mul, hs, mul_comm]
      simp_rw [hexp] at hfro
      have hpne : p ≠ 0 := by omega
      rw [ihs, zero_pow hpne] at hfro
      exact hfro.symm
    · have hmod : ∀ x : Fq,
          Polynomial.eval x ((f ^ t) %
            (Polynomial.X ^ Fintype.card Fq - Polynomial.X : Polynomial Fq)) =
            (f.eval x) ^ t := by
        intro x
        rw [hd_mod_eval hq]
        simp [Polynomial.eval_pow]
      have hsum : ∑ x : Fq, Polynomial.eval x ((f ^ t) %
          (Polynomial.X ^ Fintype.card Fq - Polynomial.X : Polynomial Fq)) = 0 := by
        apply hd_sum_eval_eq_zero_of_natDegree_le _ _ hq
        exact hdeg t h1 h2 hpdvd
      simp_rw [hmod] at hsum
      exact hsum

-- Helper: the `(q - 1)`-st power sum of `f` is `-1` when `f` has exactly one root.
private theorem hd_sum_f_pow_card_sub_one_of_roots {p : ℕ} {Fq : Type*} [Field Fq] [Fintype Fq]
    [DecidableEq Fq] [CharP Fq p] [Fact p.Prime]
    (hq : 2 ≤ Fintype.card Fq)
    (f : Polynomial Fq)
    (hroots : (Finset.univ.filter (fun x => Polynomial.eval x f = 0)).card = 1) :
    ∑ x : Fq, (f.eval x) ^ (Fintype.card Fq - 1) = -1 := by
  have hq1 : Fintype.card Fq - 1 ≠ 0 := by omega
  have hfun : ∀ x : Fq, (f.eval x) ^ (Fintype.card Fq - 1) =
      if Polynomial.eval x f = 0 then 0 else 1 := by
    intro x
    by_cases hx : Polynomial.eval x f = 0
    · simp [hx, zero_pow hq1]
    · simp [hx, FiniteField.pow_card_sub_one_eq_one _ hx]
  simp_rw [hfun]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_const]
  simp only [nsmul_eq_mul, mul_one]
  have hcompl : (Finset.univ.filter (fun x => ¬Polynomial.eval x f = 0)).card =
      Fintype.card Fq - 1 := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset Fq)) (p := fun x => Polynomial.eval x f = 0)
    simp only [Finset.card_univ] at hpart
    omega
  rw [hcompl]
  have hcard0 : (Fintype.card Fq : Fq) = 0 := hd_card_cast_eq_zero
  have hcast : ((Fintype.card Fq - 1 : ℕ) : Fq) = -1 := by
    have h1 : ((Fintype.card Fq : ℕ) : Fq) =
        (((Fintype.card Fq - 1 : ℕ) : Fq) + 1) := by
      have h2 : Fintype.card Fq = (Fintype.card Fq - 1) + 1 := by omega
      conv_lhs => rw [h2]
      simp
    rw [hcard0] at h1
    have h2 := eq_neg_of_add_eq_zero_left h1.symm
    simpa using h2
  exact hcast

-- Helper: the degree bound follows from bijectivity (forward direction).
private theorem hd_deg_le_of_bij {p : ℕ} {Fq : Type*} [Field Fq] [Fintype Fq]
    [CharP Fq p] [Fact p.Prime]
    (hq : 2 ≤ Fintype.card Fq)
    (f : Polynomial Fq)
    (hbij : Function.Bijective fun x => f.eval x)
    (t : ℕ) (_h1 : 1 ≤ t) (h2 : t ≤ Fintype.card Fq - 2) :
    ((f ^ t) % (Polynomial.X ^ Fintype.card Fq - Polynomial.X :
      Polynomial Fq)).natDegree ≤ Fintype.card Fq - 2 := by
  by_contra hcon
  push Not at hcon
  have hdivdeg : (Polynomial.X ^ Fintype.card Fq - Polynomial.X :
      Polynomial Fq).natDegree = Fintype.card Fq :=
    hd_natDegree_X_pow_sub hq
  have hmodlt : ((f ^ t) % (Polynomial.X ^ Fintype.card Fq - Polynomial.X :
      Polynomial Fq)).natDegree < Fintype.card Fq := by
    have hne : (Polynomial.X ^ Fintype.card Fq - Polynomial.X :
        Polynomial Fq).natDegree ≠ 0 := by
      rw [hdivdeg]
      omega
    have h := Polynomial.natDegree_mod_lt (f ^ t) hne
    rwa [hdivdeg] at h
  have heq : ((f ^ t) % (Polynomial.X ^ Fintype.card Fq - Polynomial.X :
      Polynomial Fq)).natDegree = Fintype.card Fq - 1 := by
    omega
  have hcoeff : ((f ^ t) % (Polynomial.X ^ Fintype.card Fq - Polynomial.X :
      Polynomial Fq)).coeff (Fintype.card Fq - 1) ≠ 0 := by
    intro h0
    have hle : ((f ^ t) % (Polynomial.X ^ Fintype.card Fq - Polynomial.X :
        Polynomial Fq)).natDegree ≤ Fintype.card Fq - 2 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      by_cases hNq : N = Fintype.card Fq - 1
      · rw [hNq]
        exact h0
      · have hlt : ((f ^ t) % (Polynomial.X ^ Fintype.card Fq - Polynomial.X :
            Polynomial Fq)).natDegree < N := by
          omega
        exact Polynomial.coeff_eq_zero_of_natDegree_lt hlt
    omega
  have hsum1 : ∑ x : Fq, Polynomial.eval x ((f ^ t) %
      (Polynomial.X ^ Fintype.card Fq - Polynomial.X : Polynomial Fq))
      = - (((f ^ t) % (Polynomial.X ^ Fintype.card Fq - Polynomial.X :
        Polynomial Fq)).coeff (Fintype.card Fq - 1)) :=
    hd_sum_eq_neg_coeff_top hq _ heq
  have hsumne : (∑ x : Fq, Polynomial.eval x ((f ^ t) %
      (Polynomial.X ^ Fintype.card Fq - Polynomial.X : Polynomial Fq))) ≠ 0 := by
    rw [hsum1]
    exact neg_ne_zero.mpr hcoeff
  have hsum0 : (∑ x : Fq, Polynomial.eval x ((f ^ t) %
      (Polynomial.X ^ Fintype.card Fq - Polynomial.X : Polynomial Fq))) = 0 := by
    have heval : ∀ x : Fq, Polynomial.eval x ((f ^ t) %
        (Polynomial.X ^ Fintype.card Fq - Polynomial.X : Polynomial Fq)) =
        (f.eval x) ^ t := by
      intro x
      rw [hd_mod_eval hq]
      simp [Polynomial.eval_pow]
    simp_rw [heval]
    rw [hd_sum_pow_comp_bij f t hbij]
    apply FiniteField.sum_pow_lt_card_sub_one
    omega
  exact hsumne hsum0

/--
**Hermite–Dickson criterion.** Let $\mathbb{F}_q$ be a finite field with $q$ elements and
characteristic $p$, and let $f \in \mathbb{F}_q[X]$. Then $f$ is a permutation polynomial of
$\mathbb{F}_q$, that is, $x \mapsto f(x)$ is a bijection of $\mathbb{F}_q$, if and only if $f$
has exactly one root in $\mathbb{F}_q$ and, for every integer $t$ with $1 \le t \le q - 2$ and
$p \nmid t$, the remainder of $f^t$ upon division by $X^q - X$ has degree at most $q - 2$.

Proves `Wanted` entry `hermite_dickson_permutation_criterion`.

Source: Brian G. Kronenthal, "An Integer Sequence Motivated by Generalized
Quadrangles", Journal of Integer Sequences 18 (2015), Article 15.7.8.
Source URL: https://cs.uwaterloo.ca/journals/JIS/VOL18/Kronenthal/kron3.tex
Hermite–Dickson statement at source lines 120–126.
Full source SHA-256: 4968a89e5a6c165ef1c2ab57a9eb6be1a4852e1bc905ec796b3c9abf2158a78d
Normalized no-final-newline source-span SHA-256:
ddd646ddcecd21e43eeb4e08d3c2405988e7ff842268dd6020ed2d7e603314af
-/
theorem hermite_dickson_permutation_criterion
    {p : ℕ} {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq Fq] [CharP Fq p]
    [Fact p.Prime] (hq : 2 ≤ Fintype.card Fq) (f : Polynomial Fq) :
    let q := Fintype.card Fq
    Polynomial.IsPermutationPolynomial f ↔
      (Finset.univ.filter (fun x => Polynomial.eval x f = 0)).card = 1 ∧
        ∀ t : ℕ, 1 ≤ t → t ≤ q - 2 → ¬ p ∣ t →
          Polynomial.natDegree ((f ^ t) % (Polynomial.X ^ q - Polynomial.X)) ≤ q - 2 := by
  constructor
  · intro hbij
    have hbij' : Function.Bijective fun x => f.eval x := hbij
    refine ⟨hd_card_roots_eq_one_of_bijective f hbij', fun t h1 h2 hnt => ?_⟩
    exact hd_deg_le_of_bij hq f hbij' t h1 h2
  · intro h
    obtain ⟨hroots, hdeg⟩ := h
    have hdeg_card : ∀ t : ℕ, 1 ≤ t → t ≤ Fintype.card Fq - 2 → ¬ p ∣ t →
        (((f ^ t) % (Polynomial.X ^ Fintype.card Fq - Polynomial.X :
          Polynomial Fq)).natDegree ≤ Fintype.card Fq - 2) := hdeg
    have hS : ∀ j : ℕ, 1 ≤ j → j ≤ Fintype.card Fq - 2 →
        ∑ x : Fq, (f.eval x) ^ j = 0 :=
      fun j h1 h2 => hd_sum_pow_eq_zero_of_hyp f hq hdeg_card j h1 h2
    have hS0 : ∑ x : Fq, (f.eval x) ^ 0 = 0 := by
      simp only [pow_zero]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      have hcard0 : (Fintype.card Fq : Fq) = 0 := hd_card_cast_eq_zero
      simp [hcard0]
    have hStop : ∑ x : Fq, (f.eval x) ^ (Fintype.card Fq - 1) = -1 :=
      hd_sum_f_pow_card_sub_one_of_roots hq f hroots
    change Function.Bijective fun x => f.eval x
    rw [← Finite.surjective_iff_bijective]
    intro a
    by_contra hcon
    push Not at hcon
    have hne : ∀ x : Fq, f.eval x ≠ a := by
      intro x hx
      exact hcon x hx
    have hone : ∀ x : Fq, (f.eval x - a) ^ (Fintype.card Fq - 1) = 1 := by
      intro x
      apply FiniteField.pow_card_sub_one_eq_one
      intro hzero
      have hfa : f.eval x = a := sub_eq_zero.mp hzero
      exact hne x hfa
    have hsumLHS : ∑ x : Fq, (f.eval x - a) ^ (Fintype.card Fq - 1) = 0 := by
      simp_rw [hone]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      have hcard0 : (Fintype.card Fq : Fq) = 0 := hd_card_cast_eq_zero
      simp [hcard0]
    have hexpand : ∀ x : Fq, (f.eval x - a) ^ (Fintype.card Fq - 1)
        = ∑ j ∈ Finset.range (Fintype.card Fq - 1 + 1),
            (f.eval x) ^ j * (-a) ^ (Fintype.card Fq - 1 - j) *
              ((Fintype.card Fq - 1).choose j : Fq) := by
      intro x
      have hsub : f.eval x - a = f.eval x + (-a) := by abel
      rw [hsub]
      exact add_pow (f.eval x) (-a) (Fintype.card Fq - 1)
    have hsumEq : ∑ x : Fq, (f.eval x - a) ^ (Fintype.card Fq - 1)
        = ∑ x : Fq, (f.eval x) ^ (Fintype.card Fq - 1) := by
      simp_rw [hexpand]
      rw [Finset.sum_comm, Finset.sum_range_succ]
      have hrest : (∑ j ∈ Finset.range (Fintype.card Fq - 1),
          ∑ x : Fq, (f.eval x) ^ j * (-a) ^ (Fintype.card Fq - 1 - j) *
            ((Fintype.card Fq - 1).choose j : Fq)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        simp only [Finset.mem_range] at hj
        have hfactor : ∀ x : Fq, (f.eval x) ^ j * (-a) ^ (Fintype.card Fq - 1 - j) *
            ((Fintype.card Fq - 1).choose j : Fq)
            = (f.eval x) ^ j * (((-a) ^ (Fintype.card Fq - 1 - j) *
              ((Fintype.card Fq - 1).choose j : Fq))) := by
          intro x
          ring
        simp_rw [hfactor, ← Finset.sum_mul]
        by_cases hj0 : j = 0
        · subst hj0
          rw [hS0, zero_mul]
        · have hj1 : 1 ≤ j := by omega
          have hj2 : j ≤ Fintype.card Fq - 2 := by omega
          rw [hS j hj1 hj2, zero_mul]
      rw [hrest, zero_add]
      have htop : (∑ x : Fq, (f.eval x) ^ (Fintype.card Fq - 1) *
          (-a) ^ (Fintype.card Fq - 1 - (Fintype.card Fq - 1)) *
            (((Fintype.card Fq - 1).choose (Fintype.card Fq - 1) : ℕ) : Fq))
          = ∑ x : Fq, (f.eval x) ^ (Fintype.card Fq - 1) := by
        simp [Nat.choose_self]
      exact htop
    rw [hsumEq] at hsumLHS
    rw [hStop] at hsumLHS
    exact neg_ne_zero.mpr one_ne_zero hsumLHS

end MathlibExt.FieldTheory.HermiteDickson
