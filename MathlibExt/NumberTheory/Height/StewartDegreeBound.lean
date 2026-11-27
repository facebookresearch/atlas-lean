/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Height.PrimitiveMahler
public import Mathlib.GroupTheory.OrderOfElement
import MathlibExt.LinearAlgebra.Matrix.HadamardDeterminant
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.NumberTheory.Bertrand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Stewart's lower bound for the Mahler measure

This file proves `MathlibExt.NumberTheory.AsymptoticDobrowolski.stewart_degreeBound`: a nonzero
complex number $\alpha$, algebraic over $\mathbb{Q}$ of degree $d \ge 2$ and not a root of unity,
has algebraic Mahler measure $M(\alpha) > 1 + \frac{1}{10000\, d \log d}$. This is Stewart's
degree-dependent bound, cited in the theorem's `Source:` paragraph. The theorem was a wanted
statement of `WantedExt/NumberTheory/Height/AsymptoticDobrowolskiWanted.lean` and keeps its name,
statement and docstring.

The proof does not follow Stewart's transcendence argument; it is elementary. If the positive
primitive integral minimal polynomial $P$ of $\alpha$ is not monic, then $M(\alpha) \ge 2$.
Otherwise $\alpha$ is an algebraic integer with conjugates $\alpha_1, \dots, \alpha_d$, and
Bertrand's postulate gives a prime $p$ with $6d < p \le 12d$.

* Since $p \ge d + 2$, the powers $\alpha_i^p$ are pairwise distinct (by the irreducibility
  criterion for $X^p - a$), so they are the roots of a monic integer polynomial $Q$ of degree $d$.
* Since $\alpha$ is not a root of unity, no $\alpha_i^p$ is a conjugate of $\alpha$, and the
  congruence $P(X^p) \equiv P(X)^p \pmod p$ shows that $\prod_i P(\alpha_i^p)$ is a nonzero
  integer divisible by $p^d$. This is Dobrowolski's lemma, which states the resulting bound
  $|\prod_i P(\alpha_i^p)| \ge p^d$ (E. Dobrowolski, "On a question of Lehmer and the number of
  irreducible factors of a polynomial", Acta Arith. 34 (1979), 391–401, Lemma 2 and its proof,
  p. 395).
* For $F = PQ$, whose $2d$ roots are distinct, the product of $|F'(z)|$ over the roots $z$ of $F$
  equals $|\prod_i P'(\alpha_i)| \cdot |\prod_i P(\alpha_i^p)|^2 \cdot |\prod_i Q'(\alpha_i^p)|$,
  a product of nonzero integers (products of values at the roots of $P$ are resultants), so it is
  at least $p^{2d}$.
* Hadamard's inequality for the Vandermonde matrix of the roots of $F$ bounds the same product
  by $(2d)^{2d} M(F)^{2(2d-1)}$, where $M(F) = M(\alpha)^{p+1}$. This is Mahler's discriminant
  inequality $|D(F)| \le m^m M(F)^{2m-2}$ with $m = \deg F$ (K. Mahler, "An inequality for the
  discriminant of a polynomial", Michigan Math. J. 11 (1964), 257–262, Theorem 1, p. 261), which
  Mahler also derives from Hadamard's inequality (his Lemma 1).

Comparing the two bounds gives $9^d < M(\alpha)^{(p+1) \cdot 2(2d-1)}$, which is incompatible
with $M(\alpha) \le 1 + \frac{1}{10000\, d \log d}$.
-/

public section

namespace MathlibExt.NumberTheory.AsymptoticDobrowolski

section Auxiliary

open Polynomial Finset

/-! ### Hadamard's inequality for Vandermonde matrices -/

/-- The squared absolute value of a Vandermonde determinant is the product of `‖v j - v i‖` over
all ordered pairs `(i, j)` of distinct indices. -/
private theorem norm_det_vandermonde_sq {n : ℕ} (v : Fin n → ℂ) :
    ‖(Matrix.vandermonde v).det‖ ^ 2 = ∏ i, ∏ j ∈ ({i}ᶜ : Finset (Fin n)), ‖v j - v i‖ := by
  rw [Matrix.det_vandermonde, ← Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag, norm_prod,
    ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [norm_prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [norm_sub_rev (v i) (v j), sq]

/-- Hadamard's inequality for the Vandermonde matrix with nodes `v i`: each row
`(1, v i, ..., v i ^ (n - 1))` has squared length at most `n * max 1 ‖v i‖ ^ (2 * (n - 1))`. -/
private theorem norm_det_vandermonde_sq_le {n : ℕ} (v : Fin n → ℂ) :
    ‖(Matrix.vandermonde v).det‖ ^ 2 ≤ (n : ℝ) ^ n * (∏ i, max 1 ‖v i‖) ^ (2 * (n - 1)) := by
  have hrow : ∀ i, ∑ j : Fin n, Complex.normSq (Matrix.vandermonde v i j) ≤
      n * (max 1 ‖v i‖) ^ (2 * (n - 1)) := by
    intro i
    calc ∑ j : Fin n, Complex.normSq (Matrix.vandermonde v i j)
        ≤ ∑ _j : Fin n, (max 1 ‖v i‖) ^ (2 * (n - 1)) := by
          gcongr with j
          rw [Matrix.vandermonde_apply, Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul]
          calc ‖v i‖ ^ ((j : ℕ) * 2) ≤ (max 1 ‖v i‖) ^ ((j : ℕ) * 2) := by
                gcongr
                exact le_max_right _ _
            _ ≤ (max 1 ‖v i‖) ^ (2 * (n - 1)) := by
                apply pow_le_pow_right₀ (le_max_left _ _)
                have := j.isLt
                omega
      _ = n * (max 1 ‖v i‖) ^ (2 * (n - 1)) := by
          simp
  have hH := MathlibExt.LinearAlgebra.Matrix.HadamardDeterminant.hadamard_determinant_inequality
    (Matrix.vandermonde v)
  have hnonneg : ∀ i, 0 ≤ ∑ j : Fin n, Complex.normSq (Matrix.vandermonde v i j) :=
    fun i => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  calc ‖(Matrix.vandermonde v).det‖ ^ 2
      ≤ (∏ i : Fin n, Real.sqrt (∑ j : Fin n, Complex.normSq (Matrix.vandermonde v i j))) ^ 2 := by
        gcongr
    _ = ∏ i : Fin n, ∑ j : Fin n, Complex.normSq (Matrix.vandermonde v i j) := by
        rw [← Finset.prod_pow]
        exact Finset.prod_congr rfl fun i _ => Real.sq_sqrt (hnonneg i)
    _ ≤ ∏ i : Fin n, ((n : ℝ) * (max 1 ‖v i‖) ^ (2 * (n - 1))) :=
        Finset.prod_le_prod₀ (fun i _ => hnonneg i) (fun i _ => hrow i)
    _ = (n : ℝ) ^ n * (∏ i, max 1 ‖v i‖) ^ (2 * (n - 1)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Finset.prod_pow]

/-- The product of the distances between distinct nodes is at most
`n ^ n * (∏ i, max 1 ‖v i‖) ^ (2 * (n - 1))`. -/
private theorem prod_prod_ne_norm_sub_le {n : ℕ} (v : Fin n → ℂ) :
    ∏ i, ∏ j ∈ ({i}ᶜ : Finset (Fin n)), ‖v j - v i‖ ≤
      (n : ℝ) ^ n * (∏ i, max 1 ‖v i‖) ^ (2 * (n - 1)) := by
  rw [← norm_det_vandermonde_sq]
  exact norm_det_vandermonde_sq_le v

/-- The bound of `prod_prod_ne_norm_sub_le`, phrased with the derivative of
`∏ j, (X - C (v j))` at the nodes, for injective `v`. -/
private theorem prod_norm_derivative_le_aux {n : ℕ} (v : Fin n → ℂ)
    (hvinj : Function.Injective v) :
    ((univ.val.map v).map fun z =>
        ‖(((univ.val.map v).map fun a => X - C a).prod).derivative.eval z‖).prod ≤
      (n : ℝ) ^ n * ((univ.val.map v).map fun z => max 1 ‖z‖).prod ^ (2 * (n - 1)) := by
  classical
  have hderiv : ∀ i : Fin n,
      (∏ j, (X - C (v j))).derivative.eval (v i) =
        ∏ j ∈ ({i}ᶜ : Finset (Fin n)), (v i - v j) := by
    intro i
    have hprod : (∏ j, (X - C (v j))) = ((univ.val.map v).map fun a => X - C a).prod := by
      rw [Multiset.map_map]
      rfl
    rw [hprod,
      eval_multiset_prod_X_sub_C_derivative (Multiset.mem_map_of_mem v (Finset.mem_univ i)),
      ← Multiset.map_erase v hvinj, Finset.compl_singleton, ← Finset.erase_val, Multiset.map_map]
    rfl
  simp only [Multiset.map_map, Function.comp_def, Finset.prod_map_val, hderiv, norm_prod]
  calc ∏ i : Fin n, ∏ j ∈ ({i}ᶜ : Finset (Fin n)), ‖v i - v j‖
      = ∏ i : Fin n, ∏ j ∈ ({i}ᶜ : Finset (Fin n)), ‖v j - v i‖ := by
        simp_rw [norm_sub_rev (v _) (v _)]
    _ ≤ _ := prod_prod_ne_norm_sub_le v

/-- For a multiset `Z` of distinct complex numbers with `n` elements and
`F = ∏ z ∈ Z, (X - C z)`, the product of `‖F'(z)‖` over `z ∈ Z` is at most
`n ^ n * (∏ z ∈ Z, max 1 ‖z‖) ^ (2 * (n - 1))`. -/
private theorem prod_norm_derivative_le (Z : Multiset ℂ) (hZ : Z.Nodup) :
    (Z.map fun z => ‖((Z.map fun a => X - C a).prod).derivative.eval z‖).prod ≤
      (Z.card : ℝ) ^ Z.card * (Z.map fun z => max 1 ‖z‖).prod ^ (2 * (Z.card - 1)) := by
  have hZv : Z = univ.val.map Z.toList.get := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  have hvinj : Function.Injective Z.toList.get :=
    List.nodup_iff_injective_get.mp (Multiset.coe_nodup.mp (by
      rw [Multiset.coe_toList]; exact hZ))
  have h := prod_norm_derivative_le_aux Z.toList.get hvinj
  rw [← hZv, Multiset.length_toList] at h
  exact h


/-! ### Products over roots are integers -/

/-- For a monic integer polynomial `P` and an integer polynomial `g`, the product of the values of
`g` at the complex roots of `P` is the integer `resultant P g`. -/
private theorem prod_roots_eval_eq_resultant (P g : ℤ[X]) (hP : P.Monic) :
    ((P.map (Int.castRingHom ℂ)).roots.map fun x => (g.map (Int.castRingHom ℂ)).eval x).prod =
      ((resultant P g P.natDegree g.natDegree : ℤ) : ℂ) := by
  have h := resultant_eq_prod_eval (P.map (Int.castRingHom ℂ)) (g.map (Int.castRingHom ℂ))
    g.natDegree natDegree_map_le (IsAlgClosed.splits _)
  rw [(hP.map _).leadingCoeff, one_pow, one_mul, hP.natDegree_map, resultant_map_map] at h
  exact h.symm

/-- A nonzero product of values of an integer polynomial at the complex roots of a monic integer
polynomial has absolute value at least `1`. -/
private theorem one_le_norm_prod_roots_eval (P g : ℤ[X]) (hP : P.Monic)
    (hne : ((P.map (Int.castRingHom ℂ)).roots.map
      fun x => (g.map (Int.castRingHom ℂ)).eval x).prod ≠ 0) :
    1 ≤ ‖((P.map (Int.castRingHom ℂ)).roots.map
      fun x => (g.map (Int.castRingHom ℂ)).eval x).prod‖ := by
  rw [prod_roots_eval_eq_resultant P g hP] at hne ⊢
  have hz : resultant P g P.natDegree g.natDegree ≠ 0 := by exact_mod_cast hne
  rw [Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs hz

/-! ### Powers of distinct conjugates stay distinct -/

/-- Let `x, y ∈ ℂ` be roots of a monic irreducible `f ∈ ℚ[X]` of degree `d`, with `x ≠ 0`, and let
`p` be a prime with `d + 2 ≤ p`. If `x ^ p = y ^ p`, then `x = y`: if not, then `x ∉ ℚ(x ^ p)`, and
by the irreducibility criterion for `X ^ p - a` either `p ≤ d` or `ℚ(x)` contains a primitive
`p`-th root of unity, so that `p - 1 ≤ d`. -/
private theorem pow_inj_of_aeval_eq_zero {f : ℚ[X]} (hf : Irreducible f) (hfm : f.Monic) {x y : ℂ}
    (hx : aeval x f = 0) (hy : aeval y f = 0) (hx0 : x ≠ 0) {p : ℕ} (hp : p.Prime)
    (hdp : f.natDegree + 2 ≤ p) (hxy : x ^ p = y ^ p) : x = y := by
  by_contra hne
  have hmx : minpoly ℚ x = f := (minpoly.eq_of_irreducible_of_monic hf hx hfm).symm
  have hxint : IsIntegral ℚ x := ⟨f, hfm, by rwa [aeval_def] at hx⟩
  set L := IntermediateField.adjoin ℚ {x ^ p} with hL
  have hxL : x ∉ L := by
    intro hxL
    have hβint : IsIntegral ℚ (x ^ p) := hxint.pow p
    have hmem : x ∈ L.toSubalgebra := hxL
    rw [hL, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hβint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hmem
    obtain ⟨r, hr⟩ := hmem
    have hr' : aeval (x ^ p) r = x := hr
    have hS : aeval x (X - expand ℚ p r) = 0 := by
      rw [map_sub, aeval_X, expand_aeval, hr', sub_self]
    have hdvd : f ∣ X - expand ℚ p r := hmx ▸ minpoly.dvd ℚ x hS
    have hSy : aeval y (X - expand ℚ p r) = 0 := by
      obtain ⟨q, hq⟩ := hdvd
      rw [hq, map_mul, hy, zero_mul]
    rw [map_sub, aeval_X, expand_aeval, ← hxy, hr', sub_eq_zero] at hSy
    exact hne hSy.symm
  have hβL : x ^ p ∈ L := IntermediateField.mem_adjoin_simple_self ℚ (x ^ p)
  by_cases hpow : ∀ b : L, b ^ p ≠ ⟨x ^ p, hβL⟩
  · have hirr : Irreducible (X ^ p - C (⟨x ^ p, hβL⟩ : L)) :=
      irreducible_X_pow_sub_C_of_prime hp hpow
    have hmon : (X ^ p - C (⟨x ^ p, hβL⟩ : L)).Monic := monic_X_pow_sub_C _ hp.ne_zero
    have hroot : aeval x (X ^ p - C (⟨x ^ p, hβL⟩ : L)) = 0 := by
      simp
    have hmin := minpoly.eq_of_irreducible_of_monic hirr hroot hmon
    have hdvd := minpoly.dvd_map_of_isScalarTower ℚ L x
    rw [← hmin, hmx] at hdvd
    have hle := natDegree_le_of_dvd hdvd (Polynomial.map_ne_zero hfm.ne_zero)
    rw [natDegree_X_pow_sub_C, natDegree_map] at hle
    omega
  · push Not at hpow
    obtain ⟨b, hb⟩ := hpow
    have hγp : (b : ℂ) ^ p = x ^ p := by
      have := congrArg Subtype.val hb
      simpa using this
    have hγ0 : (b : ℂ) ≠ 0 := by
      intro h
      rw [h, zero_pow hp.ne_zero] at hγp
      exact hx0 (pow_eq_zero_iff hp.ne_zero |>.mp hγp.symm)
    have hζp : (x / b) ^ p = 1 := by
      rw [div_pow, hγp, div_self (pow_ne_zero p hx0)]
    have hζ1 : x / b ≠ 1 := by
      intro h
      rw [div_eq_one_iff_eq hγ0] at h
      exact hxL (h ▸ b.2)
    have := Fact.mk hp
    have hprim : IsPrimitiveRoot (x / b) p := by
      rw [← orderOf_eq_prime hζp hζ1]
      exact IsPrimitiveRoot.orderOf _
    have hLle : L ≤ IntermediateField.adjoin ℚ {x} := by
      rw [hL, IntermediateField.adjoin_simple_le_iff]
      exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ x) p
    have hζmem : x / b ∈ IntermediateField.adjoin ℚ {x} :=
      div_mem (IntermediateField.mem_adjoin_simple_self ℚ x) (hLle b.2)
    have := IntermediateField.adjoin.finiteDimensional hxint
    have hdeg := minpoly.natDegree_le (A := ℚ) (⟨x / b, hζmem⟩ : IntermediateField.adjoin ℚ {x})
    rw [IntermediateField.minpoly_eq, IntermediateField.adjoin.finrank hxint, hmx] at hdeg
    rw [← cyclotomic_eq_minpoly_rat hprim hp.pos, natDegree_cyclotomic,
      Nat.totient_prime hp] at hdeg
    omega

/-! ### Powers of a non-root of unity are not conjugates -/

/-- If `α ≠ 0` is algebraic and not a root of unity, `p ≥ 2` and `x` is a conjugate of `α`, then
`x ^ p` is not a conjugate of `α`: otherwise all `α ^ (p ^ k)` would be among the finitely many
conjugates of `α`. -/
private theorem aeval_pow_ne_zero {α : ℂ} (hα0 : α ≠ 0) (hroot : ¬IsOfFinOrder α)
    (hint : IsIntegral ℚ α) {p : ℕ} (hp : 2 ≤ p) {x : ℂ} (hx : aeval x (minpoly ℚ α) = 0) :
    aeval (x ^ p) (minpoly ℚ α) ≠ 0 := by
  intro hxp
  have hfx : minpoly ℚ α = minpoly ℚ x :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hx (minpoly.monic hint)
  have hdvd : minpoly ℚ x ∣ expand ℚ p (minpoly ℚ α) :=
    minpoly.dvd ℚ x (by rw [expand_aeval]; exact hxp)
  rw [← hfx] at hdvd
  have hclosed : ∀ z : ℂ, aeval z (minpoly ℚ α) = 0 → aeval (z ^ p) (minpoly ℚ α) = 0 := by
    intro z hz
    obtain ⟨q, hq⟩ := hdvd
    rw [← expand_aeval, hq, map_mul, hz, zero_mul]
  have hall : ∀ k : ℕ, α ^ (p ^ k) ∈ (minpoly ℚ α).rootSet ℂ := by
    intro k
    rw [mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_mul]
      exact hclosed _ ih
  obtain ⟨a, b, hab, heq⟩ :=
    Set.Finite.exists_lt_map_eq_of_forall_mem hall ((minpoly ℚ α).rootSet_finite ℂ)
  apply hroot
  rw [isOfFinOrder_iff_pow_eq_one]
  have hlt : p ^ a < p ^ b := Nat.pow_lt_pow_right hp hab
  refine ⟨p ^ b - p ^ a, Nat.sub_pos_of_lt hlt, ?_⟩
  have hsplit : α ^ (p ^ b) = α ^ (p ^ a) * α ^ (p ^ b - p ^ a) := by
    rw [← pow_add, Nat.add_sub_cancel' hlt.le]
  rw [← heq] at hsplit
  have hne : α ^ (p ^ a) ≠ 0 := pow_ne_zero _ hα0
  have := mul_left_cancel₀ hne (hsplit.symm.trans (mul_one _).symm)
  exact this

/-! ### The Frobenius congruence -/

/-- For a prime `p` and `P ∈ ℤ[X]`, `P(X ^ p) = P(X) ^ p + p * g(X)` for some `g ∈ ℤ[X]`. -/
private theorem exists_expand_eq_pow_add (P : ℤ[X]) {p : ℕ} (hp : p.Prime) :
    ∃ g : ℤ[X], expand ℤ p P = P ^ p + C (p : ℤ) * g := by
  have := Fact.mk hp
  have hmod : (expand ℤ p P - P ^ p).map (Int.castRingHom (ZMod p)) = 0 := by
    rw [Polynomial.map_sub, map_expand, Polynomial.map_pow, ZMod.expand_card, sub_self]
  have hdvd : C (p : ℤ) ∣ expand ℤ p P - P ^ p := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    have := congrArg (fun q => q.coeff i) hmod
    simp only [coeff_map, coeff_zero, eq_intCast] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp this
  obtain ⟨g, hg⟩ := hdvd
  exact ⟨g, by rw [← hg]; ring⟩

/-! ### The polynomial whose roots are the `p`-th powers of the conjugates -/

/-- If the `p`-th powers of the conjugates of an algebraic integer `α` are distinct, they are the
complex roots of a monic integer polynomial (the minimal polynomial of `α ^ p` over `ℤ`). -/
private theorem exists_pow_poly (α : ℂ) (hαZ : IsIntegral ℤ α) {p : ℕ}
    (hnodup : (((minpoly ℚ α).aroots ℂ).map (· ^ p)).Nodup) :
    ∃ Q : ℤ[X], Q.Monic ∧
      (Q.map (Int.castRingHom ℂ)).roots = ((minpoly ℚ α).aroots ℂ).map (· ^ p) := by
  have hαQ : IsIntegral ℚ α := hαZ.tower_top
  have hβZ : IsIntegral ℤ (α ^ p) := hαZ.pow p
  refine ⟨minpoly ℤ (α ^ p), minpoly.monic hβZ, ?_⟩
  have hQQ : (minpoly ℤ (α ^ p)).map (algebraMap ℤ ℚ) = minpoly ℚ (α ^ p) :=
    (minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hβZ).symm
  have hQC : (minpoly ℤ (α ^ p)).map (Int.castRingHom ℂ) =
      (minpoly ℚ (α ^ p)).map (algebraMap ℚ ℂ) := by
    rw [← hQQ, Polynomial.map_map]
    congr 1
  rw [hQC, ← aroots_def]
  symm
  apply Multiset.eq_of_le_of_card_le
  · rw [Multiset.le_iff_subset hnodup]
    intro w hw
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hw
    rw [mem_aroots] at hx ⊢
    refine ⟨minpoly.ne_zero hβZ.tower_top, ?_⟩
    have hdvd : minpoly ℚ α ∣ expand ℚ p (minpoly ℚ (α ^ p)) :=
      minpoly.dvd ℚ α (by rw [expand_aeval]; exact minpoly.aeval ℚ (α ^ p))
    obtain ⟨q, hq⟩ := hdvd
    rw [← expand_aeval, hq, map_mul, hx.2, zero_mul]
  · rw [Multiset.card_map]
    have := IntermediateField.adjoin.finiteDimensional hαQ
    have hmem : α ^ p ∈ IntermediateField.adjoin ℚ {α} :=
      pow_mem (IntermediateField.mem_adjoin_simple_self ℚ α) p
    have hdeg := minpoly.natDegree_le (A := ℚ) (⟨α ^ p, hmem⟩ : IntermediateField.adjoin ℚ {α})
    rw [IntermediateField.minpoly_eq, IntermediateField.adjoin.finrank hαQ] at hdeg
    have hsp := IsAlgClosed.splits ((minpoly ℚ α).map (algebraMap ℚ ℂ))
    calc ((minpoly ℚ (α ^ p)).aroots ℂ).card
        ≤ ((minpoly ℚ (α ^ p)).map (algebraMap ℚ ℂ)).natDegree := card_roots' _
      _ ≤ (minpoly ℚ (α ^ p)).natDegree := natDegree_map_le
      _ ≤ (minpoly ℚ α).natDegree := hdeg
      _ = ((minpoly ℚ α).aroots ℂ).card := by
          rw [aroots_def, ← hsp.natDegree_eq_card_roots, natDegree_map]


/-- The product of the absolute values of the values of an integer polynomial `g` at the complex
roots of a monic integer polynomial `P` is at least `1` when none of these values vanishes. -/
private theorem one_le_prod_norm_roots_eval (P g : ℤ[X]) (hP : P.Monic)
    (hne : ∀ x ∈ (P.map (Int.castRingHom ℂ)).roots, (g.map (Int.castRingHom ℂ)).eval x ≠ 0) :
    1 ≤ ((P.map (Int.castRingHom ℂ)).roots.map
      fun x => ‖(g.map (Int.castRingHom ℂ)).eval x‖).prod := by
  have h0 : ((P.map (Int.castRingHom ℂ)).roots.map
      fun x => (g.map (Int.castRingHom ℂ)).eval x).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro h
    obtain ⟨x, hx, hx0⟩ := Multiset.mem_map.mp h
    exact hne x hx hx0
  have := one_le_norm_prod_roots_eval P g hP h0
  simpa only [Multiset.norm_prod, Multiset.map_map, Function.comp_def] using this

/-- `max 1 (t ^ n) = (max 1 t) ^ n` for `t ≥ 0`. -/
private theorem max_one_pow_eq (t : ℝ) (ht : 0 ≤ t) (n : ℕ) : max 1 (t ^ n) = (max 1 t) ^ n := by
  rcases le_total t 1 with h | h
  · rw [max_eq_left h, one_pow, max_eq_left (pow_le_one₀ ht h)]
  · rw [max_eq_right h, max_eq_right (one_le_pow₀ h)]

/-! ### Assembly -/

/-- **The main inequality.** Let `P ∈ ℤ[X]` be monic of degree `d` with rational image the minimal
polynomial of a nonzero `α ∈ ℂ` that is not a root of unity, and let `p` be a prime with
`d + 2 ≤ p`. Then `p ^ (2 * d) ≤ (2 * d) ^ (2 * d) * M ^ ((p + 1) * (2 * (2 * d - 1)))`, where
`M` is the product of `max 1 ‖x‖` over the complex roots `x` of `P`. -/
private theorem main_ineq (α : ℂ) (P : ℤ[X]) (hP : P.Monic)
    (hPf : P.map (Int.castRingHom ℚ) = minpoly ℚ α) (hα0 : α ≠ 0) (hroot : ¬IsOfFinOrder α)
    {p : ℕ} (hp : p.Prime) (hdp : P.natDegree + 2 ≤ p) :
    (p : ℝ) ^ (2 * P.natDegree) ≤ ((2 * P.natDegree : ℕ) : ℝ) ^ (2 * P.natDegree) *
      ((P.map (Int.castRingHom ℂ)).roots.map fun x => max 1 ‖x‖).prod ^
        ((p + 1) * (2 * (2 * P.natDegree - 1))) := by
  classical
  have hαZ : IsIntegral ℤ α := by
    refine ⟨P, hP, ?_⟩
    have h1 : aeval α (P.map (algebraMap ℤ ℚ)) = 0 := by
      rw [algebraMap_int_eq, hPf]
      exact minpoly.aeval ℚ α
    rw [aeval_map_algebraMap, aeval_def] at h1
    exact h1
  have hαQ : IsIntegral ℚ α := hαZ.tower_top
  have hPφ : P.map (Int.castRingHom ℂ) = (minpoly ℚ α).map (algebraMap ℚ ℂ) := by
    rw [← hPf, Polynomial.map_map]
    congr 1
  have hPeval : ∀ z, (P.map (Int.castRingHom ℂ)).eval z = aeval z (minpoly ℚ α) := by
    intro z
    rw [hPφ, eval_map_algebraMap]
  have hPeval' : ∀ z, (P.map (Int.castRingHom ℂ)).derivative.eval z =
      aeval z (derivative (minpoly ℚ α)) := by
    intro z
    rw [hPφ, derivative_map, eval_map_algebraMap]
  rw [show ((p : ℝ) ^ (2 * P.natDegree)) = (p : ℝ) ^ P.natDegree * (p : ℝ) ^ P.natDegree by
    rw [← pow_add, two_mul]]
  obtain ⟨R, hRdef⟩ : ∃ R, (P.map (Int.castRingHom ℂ)).roots = R := ⟨_, rfl⟩
  rw [hRdef]
  have hRaroots : R = (minpoly ℚ α).aroots ℂ := by
    rw [← hRdef, hPφ, aroots_def]
  have hRmem : ∀ x, x ∈ R ↔ aeval x (minpoly ℚ α) = 0 := by
    intro x
    rw [hRaroots, mem_aroots]
    exact ⟨fun h => h.2, fun h => ⟨minpoly.ne_zero hαQ, h⟩⟩
  have hsepf : (minpoly ℚ α).Separable := (minpoly.irreducible hαQ).separable
  have hRnodup : R.Nodup := by
    rw [hRaroots, aroots_def]
    exact nodup_roots hsepf.map
  have hRcard : R.card = P.natDegree := by
    rw [← hRdef, ← (IsAlgClosed.splits _).natDegree_eq_card_roots, hP.natDegree_map]
  have hfd : (minpoly ℚ α).natDegree = P.natDegree := by
    rw [← hPf, hP.natDegree_map]
  have hx0 : ∀ x ∈ R, x ≠ 0 := by
    intro x hx hx0
    rw [hRmem, hx0] at hx
    have hX : minpoly ℚ α = X := by
      rw [← minpoly.zero ℚ ℂ]
      exact minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hαQ) hx (minpoly.monic hαQ)
    have := minpoly.aeval ℚ α
    rw [hX, aeval_X] at this
    exact hα0 this
  have hRp : (R.map (· ^ p)).Nodup := by
    refine Multiset.Nodup.map_on ?_ hRnodup
    intro x hx y hy hxy
    exact pow_inj_of_aeval_eq_zero (minpoly.irreducible hαQ) (minpoly.monic hαQ)
      ((hRmem x).mp hx) ((hRmem y).mp hy) (hx0 x hx) hp (by omega) hxy
  have hPxp : ∀ x ∈ R, aeval (x ^ p) (minpoly ℚ α) ≠ 0 := fun x hx =>
    aeval_pow_ne_zero hα0 hroot hαQ hp.two_le ((hRmem x).mp hx)
  obtain ⟨Q, hQ, hQroots⟩ := exists_pow_poly α hαZ (hRaroots ▸ hRp)
  rw [← hRaroots] at hQroots
  have hdisj : Disjoint R (R.map (· ^ p)) := by
    rw [Multiset.disjoint_left]
    intro x hx hxmem
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hxmem
    exact hPxp y hy ((hRmem _).mp hx)
  have hZnodup : (R + R.map (· ^ p)).Nodup := (Multiset.Nodup.add_iff hRnodup hRp).mpr hdisj
  have hZcard : (R + R.map (· ^ p)).card = 2 * P.natDegree := by
    rw [Multiset.card_add, Multiset.card_map, hRcard]
    ring
  have hPprod : (R.map fun a => X - C a).prod = P.map (Int.castRingHom ℂ) := by
    rw [← hRdef]
    exact ((IsAlgClosed.splits _).eq_prod_roots_of_monic (hP.map _)).symm
  have hQprod : ((R.map (· ^ p)).map fun a => X - C a).prod = Q.map (Int.castRingHom ℂ) := by
    rw [← hQroots]
    exact ((IsAlgClosed.splits _).eq_prod_roots_of_monic (hQ.map _)).symm
  have hF : ((R + R.map (· ^ p)).map fun a => X - C a).prod =
      P.map (Int.castRingHom ℂ) * Q.map (Int.castRingHom ℂ) := by
    rw [Multiset.map_add, Multiset.prod_add, hPprod, hQprod]
  have hA := prod_norm_derivative_le (R + R.map (· ^ p)) hZnodup
  rw [hF, hZcard] at hA
  have hQroot : ∀ x ∈ R, (Q.map (Int.castRingHom ℂ)).eval (x ^ p) = 0 := by
    intro x hx
    have hmem : x ^ p ∈ (Q.map (Int.castRingHom ℂ)).roots := by
      rw [hQroots]
      exact Multiset.mem_map_of_mem _ hx
    exact (mem_roots (hQ.map _).ne_zero).mp hmem
  -- split the left-hand side
  have hL1 : (R.map fun z =>
      ‖(P.map (Int.castRingHom ℂ) * Q.map (Int.castRingHom ℂ)).derivative.eval z‖).prod =
      (R.map fun x => ‖(P.map (Int.castRingHom ℂ)).derivative.eval x‖).prod *
        (R.map fun x => ‖(Q.map (Int.castRingHom ℂ)).eval x‖).prod := by
    rw [← Multiset.prod_map_mul]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun x hx => ?_)
    have hx' : (P.map (Int.castRingHom ℂ)).eval x = 0 := by
      rw [hPeval]
      exact (hRmem x).mp hx
    simp [derivative_mul, hx']
  have hL2 : ((R.map (· ^ p)).map fun z =>
      ‖(P.map (Int.castRingHom ℂ) * Q.map (Int.castRingHom ℂ)).derivative.eval z‖).prod =
      (R.map fun x => ‖(P.map (Int.castRingHom ℂ)).eval (x ^ p)‖).prod *
        (R.map fun x => ‖(Q.map (Int.castRingHom ℂ)).derivative.eval (x ^ p)‖).prod := by
    rw [Multiset.map_map, ← Multiset.prod_map_mul]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun x hx => ?_)
    simp [derivative_mul, hQroot x hx]
  rw [Multiset.map_add, Multiset.prod_add, hL1, hL2] at hA
  -- lower bounds for the factors
  have hA1 : 1 ≤ (R.map fun x => ‖(P.map (Int.castRingHom ℂ)).derivative.eval x‖).prod := by
    have h := one_le_prod_norm_roots_eval P (derivative P) hP (fun x hx => by
      rw [← derivative_map, hPeval']
      exact hsepf.aeval_derivative_ne_zero ((hRmem x).mp (hRdef ▸ hx)))
    rw [hRdef] at h
    simpa only [derivative_map] using h
  obtain ⟨g, hg⟩ := exists_expand_eq_pow_add P hp
  have hPxp_eval : ∀ x ∈ R, (P.map (Int.castRingHom ℂ)).eval (x ^ p) =
      (p : ℂ) * (g.map (Int.castRingHom ℂ)).eval x := by
    intro x hx
    have h1 : (P.map (Int.castRingHom ℂ)).eval (x ^ p) =
        ((expand ℤ p P).map (Int.castRingHom ℂ)).eval x := by
      rw [map_expand, expand_eval]
    have hx' : (P.map (Int.castRingHom ℂ)).eval x = 0 := by
      rw [hPeval]
      exact (hRmem x).mp hx
    rw [h1, hg, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_C,
      eval_add, eval_pow, eval_mul, eval_C, hx', zero_pow hp.ne_zero, zero_add]
    simp
  have hg1 : 1 ≤ (R.map fun x => ‖(g.map (Int.castRingHom ℂ)).eval x‖).prod := by
    have h := one_le_prod_norm_roots_eval P g hP (fun x hx => by
      have hx' : x ∈ R := hRdef ▸ hx
      intro h0
      apply hPxp x hx'
      rw [← hPeval, hPxp_eval x hx', h0, mul_zero])
    rwa [hRdef] at h
  have hA3eq : (R.map fun x => ‖(P.map (Int.castRingHom ℂ)).eval (x ^ p)‖).prod =
      (p : ℝ) ^ P.natDegree * (R.map fun x => ‖(g.map (Int.castRingHom ℂ)).eval x‖).prod := by
    have hmap : (R.map fun x => ‖(P.map (Int.castRingHom ℂ)).eval (x ^ p)‖) =
        R.map fun x => (p : ℝ) * ‖(g.map (Int.castRingHom ℂ)).eval x‖ :=
      Multiset.map_congr rfl fun x hx => by
        rw [hPxp_eval x hx, norm_mul, Complex.norm_natCast]
    rw [hmap, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hRcard]
  have hA3 : (p : ℝ) ^ P.natDegree ≤
      (R.map fun x => ‖(P.map (Int.castRingHom ℂ)).eval (x ^ p)‖).prod := by
    rw [hA3eq]
    exact le_mul_of_one_le_right (by positivity) hg1
  have hA4 : 1 ≤ (R.map fun x => ‖(Q.map (Int.castRingHom ℂ)).derivative.eval (x ^ p)‖).prod := by
    have hQsep : (Q.map (Int.castRingHom ℂ)).Separable := by
      rw [← nodup_roots_iff_of_splits (hQ.map _).ne_zero (IsAlgClosed.splits _), hQroots]
      exact hRp
    have h := one_le_prod_norm_roots_eval P (expand ℤ p (derivative Q)) hP (fun x hx => by
      have hx' : x ∈ R := hRdef ▸ hx
      rw [map_expand, expand_eval, ← derivative_map]
      have hroot : aeval (x ^ p) (Q.map (Int.castRingHom ℂ)) = 0 := by
        rw [coe_aeval_eq_eval]
        exact hQroot x hx'
      have := hQsep.aeval_derivative_ne_zero hroot
      rwa [coe_aeval_eq_eval] at this)
    rw [hRdef] at h
    simpa only [map_expand, expand_eval, derivative_map] using h
  have hA23 : (R.map fun x => ‖(Q.map (Int.castRingHom ℂ)).eval x‖).prod =
      (R.map fun x => ‖(P.map (Int.castRingHom ℂ)).eval (x ^ p)‖).prod := by
    have hQe : ∀ x, (Q.map (Int.castRingHom ℂ)).eval x =
        ((R.map (· ^ p)).map fun w => x - w).prod := by
      intro x
      rw [(IsAlgClosed.splits _).eval_eq_prod_roots_of_monic (hQ.map _), hQroots]
    have hPe : ∀ z, (P.map (Int.castRingHom ℂ)).eval z = (R.map fun y => z - y).prod := by
      intro z
      rw [(IsAlgClosed.splits _).eval_eq_prod_roots_of_monic (hP.map _), hRdef]
    simp only [hQe, hPe, Multiset.norm_prod, Multiset.map_map, Function.comp_def]
    rw [Multiset.prod_map_prod_map]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun x _ =>
      congrArg Multiset.prod (Multiset.map_congr rfl fun y _ => norm_sub_rev _ _))
  have hup : ((R + R.map (· ^ p)).map fun z => max 1 ‖z‖).prod =
      (R.map fun x => max 1 ‖x‖).prod ^ (p + 1) := by
    rw [Multiset.map_add, Multiset.prod_add, Multiset.map_map]
    have hmap : (R.map ((fun z => max 1 ‖z‖) ∘ fun x => x ^ p)) =
        R.map fun x => (max 1 ‖x‖) ^ p :=
      Multiset.map_congr rfl fun x _ => by
        simp only [Function.comp_apply, norm_pow]
        exact max_one_pow_eq _ (norm_nonneg _) p
    rw [hmap, Multiset.prod_map_pow, pow_succ']
  rw [hup, ← pow_mul] at hA
  refine le_trans ?_ hA
  rw [hA23]
  have hA3nn : 0 ≤ (R.map fun x => ‖(P.map (Int.castRingHom ℂ)).eval (x ^ p)‖).prod :=
    Multiset.prod_nonneg fun a ha => by
      obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp ha
      exact norm_nonneg _
  calc (p : ℝ) ^ P.natDegree * (p : ℝ) ^ P.natDegree
      ≤ (R.map fun x => ‖(P.map (Int.castRingHom ℂ)).eval (x ^ p)‖).prod *
          (R.map fun x => ‖(P.map (Int.castRingHom ℂ)).eval (x ^ p)‖).prod :=
        mul_le_mul hA3 hA3 (by positivity) hA3nn
    _ ≤ _ := mul_le_mul (le_mul_of_one_le_left hA3nn hA1) (le_mul_of_one_le_right hA3nn hA4)
        hA3nn (mul_nonneg (zero_le_one.trans hA1) hA3nn)

end Auxiliary

open NumberField

/-- **Stewart's lower bound for the Mahler measure.** Let $\alpha$ be a nonzero complex number
that is algebraic over $\mathbb{Q}$ and is not a root of unity, and let $d$ be the degree of its
minimal polynomial over $\mathbb{Q}$. If $d \ge 2$, then the algebraic Mahler measure $M(\alpha)$
satisfies $M(\alpha) > 1 + \frac{1}{10000\, d \log d}$, with $\log$ the natural logarithm.

Source: Stewart (1978), the strict degree-dependent bound quoted by Voutier. -/
theorem stewart_degreeBound (α : ℂ)
    (hα : IsAlgebraic ℚ α) (hα0 : α ≠ 0) (hroot : ¬IsOfFinOrder α)
    (hd : 2 ≤ (minpoly ℚ α).natDegree) :
    1 + 1 / (10000 * (minpoly ℚ α).natDegree * Real.log (minpoly ℚ α).natDegree) <
      algebraicMahlerMeasure α := by
  open Polynomial in
  set d := (minpoly ℚ α).natDegree with hd_def
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog2 := Real.log_two_gt_d9
  have hlogd : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) hdR
  have hden_pos : 0 < 10000 * (d : ℝ) * Real.log d := by
    have : 0 < Real.log d := by linarith
    positivity
  have hPdeg : (positivePrimitiveIntMinpoly α).natDegree = d :=
    positivePrimitiveIntMinpoly_natDegree_eq α
  have hlc := positivePrimitiveIntMinpoly_leadingCoeff_pos α
  have hM1 := one_le_algebraicMahlerMeasure α
  by_cases hlc1 : (positivePrimitiveIntMinpoly α).leadingCoeff = 1
  · have hPm : (positivePrimitiveIntMinpoly α).Monic := hlc1
    have hint : IsIntegral ℚ α := hα.isIntegral
    have hPf : (positivePrimitiveIntMinpoly α).map (Int.castRingHom ℚ) = minpoly ℚ α := by
      have hroot0 : aeval α ((positivePrimitiveIntMinpoly α).map (Int.castRingHom ℚ)) = 0 := by
        have h := positivePrimitiveIntMinpoly_eval₂_at α hα
        rw [aeval_def, eval₂_map]
        convert h using 2
        exact RingHom.ext_int _ _
      have hdvd := minpoly.dvd ℚ α hroot0
      exact eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (hPm.map _) hdvd
        (by rw [hPm.natDegree_map, hPdeg])
    have hMeq : algebraicMahlerMeasure α =
        (((positivePrimitiveIntMinpoly α).map (Int.castRingHom ℂ)).roots.map
          fun x => max 1 ‖x‖).prod := by
      have hdef : algebraicMahlerMeasure α =
          ((positivePrimitiveIntMinpoly α).map (Int.castRingHom ℂ)).mahlerMeasure := rfl
      rw [hdef, mahlerMeasure_eq_leadingCoeff_mul_prod_roots, (hPm.map _).leadingCoeff, norm_one,
        one_mul]
    obtain ⟨p, hp, hp6, hp12⟩ := Nat.exists_prime_lt_and_le_two_mul (6 * d) (by omega)
    have hdp : (positivePrimitiveIntMinpoly α).natDegree + 2 ≤ p := by
      rw [hPdeg]
      omega
    have hmain := main_ineq α _ hPm hPf hα0 hroot hp hdp
    rw [← hMeq, hPdeg] at hmain
    by_contra hcon
    push Not at hcon
    set M := algebraicMahlerMeasure α with hM
    set K := (p + 1) * (2 * (2 * d - 1)) with hK
    have hKn : K ≤ 52 * d * d := by
      have h1 : p + 1 ≤ 12 * d + 1 := by omega
      have h2 : 2 * (2 * d - 1) ≤ 4 * d := by omega
      calc K ≤ (12 * d + 1) * (4 * d) := Nat.mul_le_mul h1 h2
        _ ≤ 52 * d * d := by nlinarith
    have hKR : (K : ℝ) ≤ 52 * d * d := by exact_mod_cast hKn
    have hcK : (K : ℝ) * (1 / (10000 * (d : ℝ) * Real.log d)) ≤ d := by
      rw [mul_one_div, div_le_iff₀ hden_pos]
      have hd0 : (0 : ℝ) ≤ d := by linarith
      nlinarith [mul_nonneg hd0 hd0]
    have hMK : M ^ K ≤ Real.exp d := by
      calc M ^ K ≤ (1 + 1 / (10000 * (d : ℝ) * Real.log d)) ^ K :=
            pow_le_pow_left₀ (by linarith) hcon K
        _ ≤ Real.exp (1 / (10000 * (d : ℝ) * Real.log d)) ^ K := by
            gcongr
            linarith [Real.add_one_le_exp (1 / (10000 * (d : ℝ) * Real.log d))]
        _ = Real.exp ((K : ℝ) * (1 / (10000 * (d : ℝ) * Real.log d))) :=
            (Real.exp_nat_mul _ K).symm
        _ ≤ Real.exp d := Real.exp_le_exp.mpr hcK
    have hexp : Real.exp d < 3 ^ d := by
      have h := Real.exp_nat_mul 1 d
      rw [mul_one] at h
      rw [h]
      exact pow_lt_pow_left₀ (Real.exp_one_lt_d9.trans (by norm_num)) (Real.exp_pos 1).le
        (by omega)
    have h6 : ((6 * d : ℕ) : ℝ) ^ (2 * d) < (p : ℝ) ^ (2 * d) :=
      pow_lt_pow_left₀ (by exact_mod_cast hp6) (by positivity) (by omega)
    have h9 : ((6 * d : ℕ) : ℝ) ^ (2 * d) = 9 ^ d * ((2 * d : ℕ) : ℝ) ^ (2 * d) := by
      push_cast
      rw [show (6 : ℝ) * d = 3 * (2 * d) by ring, mul_pow, pow_mul]
      norm_num
    have hpos : 0 < ((2 * d : ℕ) : ℝ) ^ (2 * d) := by positivity
    have h93 : (3 : ℝ) ^ d ≤ 9 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
    have hlt : (9 : ℝ) ^ d * ((2 * d : ℕ) : ℝ) ^ (2 * d) < ((2 * d : ℕ) : ℝ) ^ (2 * d) * 9 ^ d := by
      calc (9 : ℝ) ^ d * ((2 * d : ℕ) : ℝ) ^ (2 * d) < (p : ℝ) ^ (2 * d) := h9 ▸ h6
        _ ≤ ((2 * d : ℕ) : ℝ) ^ (2 * d) * M ^ K := hmain
        _ < ((2 * d : ℕ) : ℝ) ^ (2 * d) * 9 ^ d := by
            gcongr
            exact (hMK.trans_lt hexp).trans_le h93
    linarith
  · have h2 : (2 : ℤ) ≤ (positivePrimitiveIntMinpoly α).leadingCoeff := by omega
    have hM2 : (2 : ℝ) ≤ algebraicMahlerMeasure α := by
      calc (2 : ℝ) ≤ ((positivePrimitiveIntMinpoly α).leadingCoeff : ℝ) := by exact_mod_cast h2
        _ = ‖(positivePrimitiveIntMinpoly α).leadingCoeff‖ := by
            rw [Int.norm_eq_abs, abs_of_pos (by exact_mod_cast hlc)]
        _ ≤ algebraicMahlerMeasure α :=
            Polynomial.leadingCoeff_le_mapMahlerMeasure _ _ Complex.isometry_intCast
    have hc : 1 / (10000 * (d : ℝ) * Real.log d) < 1 := by
      rw [div_lt_one hden_pos]
      nlinarith
    linarith

end MathlibExt.NumberTheory.AsymptoticDobrowolski
