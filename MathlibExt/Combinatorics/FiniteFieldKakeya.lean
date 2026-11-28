/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.FraserKakeya
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Finite-field Kakeya sets in dimension three

Every set containing a line in each direction in a three-dimensional finite vector space
over a field of order `q` has at least `q ^ 3 / 27` points. The proof uses Dvir's polynomial
method: evaluation on the set is injective on polynomials of total degree less than `q`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.FiniteFieldKakeyaThreeAIMCombinatoricsProblem245Wanted

open MathlibExt.Combinatorics.FraserKakeyaWanted.Combinatorics.FraserKakeyaProblem in
/-- **Statement of the finite field Kakeya bound in dimension three.** This is the statement that
there is a real number $c > 0$ such that for every finite field $F$ and every Kakeya set
$E \subseteq F^3$, that is, a set such that for every $x \in F^3$ there is $y \in F^3$ with
$\{y + a x : a \in F\} \subseteq E$, we have $|E| \ge c\,|F|^3$.

This is Dvir's form of Tao's question (AIM, Recent trends in additive combinatorics, Problem 3.8),
which asks for $|E| \gtrsim |F|^{5/2 + \varepsilon}$ for some $\varepsilon > 0$; the exponent $3$
gives $\varepsilon = 1/2$. -/
def finiteFieldKakeyaCubeLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (E : Finset (Fin 3 → F)),
    IsKakeya (F := F) (d := 3) (E : Set (Fin 3 → F)) → c * (Fintype.card F : ℝ) ^ 3 ≤ E.card

open MvPolynomial
open MathlibExt.Combinatorics.FraserKakeyaWanted.Combinatorics.FraserKakeyaProblem

variable {F : Type*} [Field F] {n : ℕ}

/-- Restricting a monomial to a line gives a univariate polynomial whose coefficient at
the degree of the monomial is its value at the direction vector. -/
private theorem line_monomial (s : Finset (Fin n)) (d : Fin n →₀ ℕ) (x y : Fin n → F) :
    let m := ∑ i ∈ s, d i
    let p := ∏ i ∈ s, (Polynomial.C (x i) * Polynomial.X + Polynomial.C (y i)) ^ d i
    p.natDegree ≤ m ∧ p.coeff m = ∏ i ∈ s, x i ^ d i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    dsimp only at ih ⊢
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    have hlin : (Polynomial.C (x i) * Polynomial.X + Polynomial.C (y i)).natDegree ≤ 1 :=
      Polynomial.natDegree_linear_le
    have hpow := Polynomial.natDegree_pow_le_of_le (d i) hlin
    rw [Nat.mul_one] at hpow
    refine ⟨Polynomial.natDegree_mul_le.trans (Nat.add_le_add hpow ih.1), ?_⟩
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hpow ih.1, ih.2]
    apply congrArg (· * ∏ j ∈ s, x j ^ d j)
    simpa using Polynomial.coeff_pow_of_natDegree_le (m := d i) hlin

/-- A polynomial of degree less than the field size that vanishes on a Kakeya set is zero. -/
private theorem eq_zero_of_eval_eq_zero_on_kakeya [Fintype F] (E : Finset (Fin n → F))
    (hE : IsKakeya (E : Set (Fin n → F))) (p : MvPolynomial (Fin n) F)
    (hdeg : p.totalDegree < Fintype.card F) (hp : ∀ z ∈ E, eval z p = 0) : p = 0 := by
  classical
  by_contra hne
  obtain ⟨d, hd, htop⟩ := Finset.exists_mem_eq_sup p.support (support_nonempty.mpr hne)
    (fun d => d.degree)
  change p.totalDegree = d.degree at htop
  suffices hz : homogeneousComponent p.totalDegree p = 0 by
    have h := congrArg (fun f : MvPolynomial (Fin n) F => f.coeff d) hz
    simp [coeff_homogeneousComponent, ← htop, mem_support_iff.mp hd] at h
  apply (homogeneousComponent_isHomogeneous _ _).eq_zero_of_forall_eval_eq_zero_of_le_card
  · intro x
    obtain ⟨y, hy⟩ := hE x
    let L (i : Fin n) := Polynomial.C (x i) * Polynomial.X + Polynomial.C (y i)
    let P := p.eval₂ Polynomial.C L
    have hbound : P.natDegree ≤ p.totalDegree := by
      rw [show P = _ from eval₂_eq Polynomial.C L p]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro m hm
      exact (Polynomial.natDegree_C_mul_le _ _).trans
        ((line_monomial m.support m x y).1.trans (le_totalDegree hm))
    have hzero : P = 0 := by
      by_contra hP
      obtain ⟨a, ha⟩ := P.exists_eval_ne_zero_of_natDegree_lt_card hP
        (by rw [Cardinal.mk_fintype]; exact_mod_cast hbound.trans_lt hdeg)
      apply ha
      have hval := hp (y + a • x) (hy ⟨a, rfl⟩)
      rw [show P = _ from eval₂_eq Polynomial.C L p, Polynomial.eval_finsetSum]
      rw [eval_eq] at hval
      simpa only [L, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
        Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, add_comm, mul_comm] using hval
    have hcoeff : P.coeff p.totalDegree = eval x (homogeneousComponent p.totalDegree p) := by
      rw [show P = _ from eval₂_eq Polynomial.C L p, Polynomial.finsetSum_coeff,
        homogeneousComponent_apply, map_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m hm
      have hmon := line_monomial m.support m x y
      rw [Polynomial.coeff_C_mul]
      by_cases h : m.degree = p.totalDegree
      · rw [ite_eq_left h, eval_monomial, ← h]
        exact congrArg (p.coeff m * ·) hmon.2
      · have hlt : m.degree < p.totalDegree := lt_of_le_of_ne (le_totalDegree hm) h
        simp [h, Polynomial.coeff_eq_zero_of_natDegree_lt (hmon.1.trans_lt hlt), L]
    rw [← hcoeff, hzero, Polynomial.coeff_zero]
  · rw [Cardinal.mk_fintype]
    exact_mod_cast hdeg.le

/--
**Finite field Kakeya sets in dimension three have cubic size.** There is a real number $c > 0$
such that for every finite field $F$ and every Kakeya set $E \subseteq F^3$, that is, a set such
that for every $x \in F^3$ there is $y \in F^3$ with $\{y + a x : a \in F\} \subseteq E$, we have
$|E| \ge c\,|F|^3$.

Dvir proved by the polynomial method that every Kakeya set $K \subseteq F^n$ over a finite field
$F$ with $q$ elements has $|K| \ge C_n q^n$, with $C_n$ depending only on $n$ (Theorem 3, the
Alon–Tao form of his Theorem 1). For $n = 3$ this answers Tao's question, which asks for
$|E| \gtrsim |F|^{5/2 + \varepsilon}$ for some $\varepsilon > 0$, beyond Wolff's bound
$|F|^{5/2}$, with $\varepsilon = 1/2$.

Source: AIM workshop Recent trends in additive combinatorics (2004), problem list collected by E.
Croot and V. F. Lev, https://aimath.org/WWN/additivecomb/additivecomb.pdf, Problem 3.8 (T. Tao);
resolution: Z. Dvir, On the size of Kakeya sets in finite fields, J. Amer. Math. Soc. 22 (2009),
1093-1097, arXiv:0803.2336, Theorem 3 (Section 1.1, the Alon-Tao improvement of Theorem 1): every
Kakeya set K ⊂ Fⁿ satisfies |K| ≥ C_n qⁿ with C_n depending only on n; for n = 3 this is |K| ≫ q³,
https://doi.org/10.1090/S0894-0347-08-00607-3.
-/
public theorem finiteFieldKakeyaCubeLowerBound_holds : finiteFieldKakeyaCubeLowerBound := by
  classical
  refine ⟨1 / 27, by norm_num, ?_⟩
  intro F _ _ _ E hE
  let m := (Fintype.card F - 1) / 3
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hsmall : 3 * m < Fintype.card F := by dsimp [m]; omega
  let V := restrictTotalDegree (Fin 3) F (3 * m)
  let ev : V →ₗ[F] (E → F) := LinearMap.pi fun z =>
    (aeval (R := F) (z : Fin 3 → F)).toLinearMap.comp V.subtype
  have hinj : Function.Injective ev := by
    apply (injective_iff_map_eq_zero ev).2
    intro p hp
    apply Subtype.ext
    have hpdeg := (mem_restrictTotalDegree _ _ _).mp p.property
    apply eq_zero_of_eval_eq_zero_on_kakeya E hE p.val (hpdeg.trans_lt hsmall)
    intro z hz
    exact congrFun hp ⟨z, hz⟩
  -- Monomials with each exponent at most m have total degree at most 3m.
  let index (v : Fin 3 → Fin (m + 1)) : {d : Fin 3 →₀ ℕ | d.degree ≤ 3 * m} :=
    ⟨Finsupp.equivFunOnFinite.symm (fun i => (v i : ℕ)), by
      simp only [Set.mem_ofPred_eq, Finsupp.degree_eq_sum]
      calc
        _ ≤ ∑ _ : Fin 3, m := Finset.sum_le_sum fun i _ => Nat.le_of_lt_succ (v i).isLt
        _ = 3 * m := by simp⟩
  have hindex : Function.Injective index := by
    intro u v huv
    funext i
    exact Fin.ext (congrArg (fun d => (d : Fin 3 →₀ ℕ) i) (congrArg Subtype.val huv))
  have hb := (basisRestrictSupport F {d : Fin 3 →₀ ℕ | d.degree ≤ 3 * m}).linearIndependent
  have hcard : (m + 1) ^ 3 ≤ E.card := by
    have hind := (hb.comp index hindex).map' ev (LinearMap.ker_eq_bot.mpr hinj)
    simpa using hind.fintype_card_le_finrank
  have hsize : (Fintype.card F : ℝ) ≤ 3 * ((m : ℝ) + 1) := by
    exact_mod_cast (show Fintype.card F ≤ 3 * (m + 1) by dsimp [m]; omega)
  calc
    1 / 27 * (Fintype.card F : ℝ) ^ 3 ≤ 1 / 27 * (3 * ((m : ℝ) + 1)) ^ 3 := by gcongr
    _ = ((m : ℝ) + 1) ^ 3 := by ring
    _ ≤ (E.card : ℝ) := by exact_mod_cast hcard

end MathlibExt.Combinatorics.FiniteFieldKakeyaThreeAIMCombinatoricsProblem245Wanted
