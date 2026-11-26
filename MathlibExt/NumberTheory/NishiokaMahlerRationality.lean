/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.KMahlerFunction
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.Polynomial.IntegralNormalization
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Nishioka's theorem

Nishioka's rationality-transcendence dichotomy for Mahler functions.

The functional equation puts rotations by roots of unity of $k$-power order in a single finite
extension of $\mathbb{C}(z)$. After multiplying by a polynomial to obtain an integral series,
trace coordinates and the valuation at infinity put its rotations in a finite-dimensional
$\mathbb{C}$-vector space. Polynomial interpolation then forces the integral series to have finite
support.
-/

open scoped LaurentSeries Polynomial PowerSeries RatFunc
open Polynomial

namespace MetaMathlibExt
namespace NishiokaMahlerRationality

private theorem mahlerSubst_eq_expand (F : ℂ⟦X⟧) {k : ℕ} (hk : k ≠ 0) (i : ℕ) :
    mahlerSubst F k i = PowerSeries.expand (k ^ i) (pow_ne_zero i hk) F := by
  ext n
  simp [mahlerSubst, PowerSeries.coeff_expand]

private theorem expand_polynomial {m : ℕ} (hm : m ≠ 0) (p : ℂ[X]) :
    PowerSeries.expand m hm (p : ℂ⟦X⟧) = (Polynomial.expand ℂ m p : ℂ[X]) := by
  ext n
  simp only [PowerSeries.coeff_expand, Polynomial.coeff_coe,
    Polynomial.coeff_expand (Nat.pos_of_ne_zero hm)]

private theorem rescale_polynomial (t : ℂ) (p : ℂ[X]) :
    PowerSeries.rescale t (p : ℂ⟦X⟧) = (p.comp (C t * X) : ℂ[X]) := by
  ext n
  rw [PowerSeries.coeff_rescale, Polynomial.coeff_coe, Polynomial.coeff_coe,
    comp_C_mul_X_coeff, mul_comm]

private noncomputable def rescalePolynomial (t : ℂ) : ℂ[X] →+* ℂ[X] :=
  (Polynomial.eval₂RingHom C (C t * X))

private theorem map_rescalePolynomial (t : ℂ) (p : ℂ[X]) :
    rescalePolynomial t p = p.comp (C t * X) := rfl

private theorem powerSeries_algebraMap (p : ℂ[X]) :
    algebraMap ℂ[X] ℂ⟦X⟧ p = (p : ℂ⟦X⟧) := by
  rw [PowerSeries.algebraMap_apply']
  change PowerSeries.map (RingHom.id ℂ) (p : ℂ⟦X⟧) = _
  rw [PowerSeries.map_id, id_eq]

private theorem polynomial_laurentSeries (p : ℂ[X]) :
    ((p : ℂ⟦X⟧) : ℂ⸨X⸩) = algebraMap ℂ[X] ℂ⸨X⸩ p := by
  rw [RatFunc.coe_coe]
  exact (IsScalarTower.algebraMap_apply ℂ[X] ℂ⟮X⟯ ℂ⸨X⸩ p).symm

private theorem expand_isIntegral_ratFunc {F : ℂ⟦X⟧} {P : ℂ[X][X]} (hP : P ≠ 0)
    (hF : P.eval₂ (algebraMap ℂ[X] ℂ⟦X⟧) F = 0)
    {m : ℕ} (hm : m ≠ 0) :
    IsIntegral ℂ⟮X⟯ (PowerSeries.expand m hm F : ℂ⸨X⸩) := by
  let e := (Polynomial.expand ℂ m).toRingHom
  let j : ℂ⟦X⟧ →+* ℂ⸨X⸩ := HahnSeries.ofPowerSeries ℤ ℂ
  apply (isAlgebraic_iff_isIntegral).mp
  refine ⟨(P.map e).map (algebraMap ℂ[X] ℂ⟮X⟯), ?_, ?_⟩
  · exact (Polynomial.map_ne_zero_iff (IsFractionRing.injective _ _)).mpr
      ((Polynomial.map_ne_zero_iff (Polynomial.expand_injective (Nat.pos_of_ne_zero hm))).mpr hP)
  have heval := congrArg ((j.comp (PowerSeries.expand m hm).toRingHom) : ℂ⟦X⟧ →+* ℂ⸨X⸩) hF
  rw [Polynomial.hom_eval₂, map_zero] at heval
  change Polynomial.eval₂ (algebraMap ℂ⟮X⟯ ℂ⸨X⸩) (j (PowerSeries.expand m hm F)) _ = 0
  rw [Polynomial.eval₂_map, Polynomial.eval₂_map]
  have hcomp :
      ((algebraMap ℂ⟮X⟯ ℂ⸨X⸩).comp (algebraMap ℂ[X] ℂ⟮X⟯)).comp e =
      (j.comp (PowerSeries.expand m hm).toRingHom).comp (algebraMap ℂ[X] ℂ⟦X⟧) := by
    apply RingHom.ext
    intro p
    change algebraMap ℂ⟮X⟯ ℂ⸨X⸩ (algebraMap ℂ[X] ℂ⟮X⟯ (e p)) =
      j (PowerSeries.expand m hm (algebraMap ℂ[X] ℂ⟦X⟧ p))
    rw [← IsScalarTower.algebraMap_apply, powerSeries_algebraMap, expand_polynomial hm,
      ← polynomial_laurentSeries]
    rfl
  rwa [hcomp]

private theorem rescale_expand {t : ℂ} {m : ℕ} (hm : m ≠ 0) (ht : t ^ m = 1)
    (F : ℂ⟦X⟧) :
    PowerSeries.rescale t (PowerSeries.expand m hm F) = PowerSeries.expand m hm F := by
  ext n
  by_cases h : m ∣ n
  · obtain ⟨j, rfl⟩ := h
    simp [pow_mul, ht]
  · simp [PowerSeries.coeff_expand_of_not_dvd m hm F h]

private theorem mem_of_mul_add_eq_zero (E : IntermediateField ℂ⟮X⟯ ℂ⸨X⸩)
    {a x y : ℂ⸨X⸩} (ha : a ∈ E) (ha0 : a ≠ 0) (hy : y ∈ E) (h : a * x + y = 0) :
    x ∈ E := by
  have hx : x = -y / a := (eq_div_iff ha0).mpr <| by
    rw [mul_comm, ← add_eq_zero_iff_eq_neg]
    exact h
  rw [hx]
  exact E.div_mem (E.neg_mem hy) ha

private theorem rotations_mem_finite_extension (k : ℕ) (F : ℂ⟦X⟧)
    (hMahler : IsKMahlerFunction k F) {P : ℂ[X][X]} (hP : P ≠ 0)
    (hF : P.eval₂ (algebraMap ℂ[X] ℂ⟦X⟧) F = 0) :
    ∃ E : IntermediateField ℂ⟮X⟯ ℂ⸨X⸩, FiniteDimensional ℂ⟮X⟯ E ∧
      ∀ t : ℂ, (∃ L : ℕ, t ^ (k ^ L) = 1) → ((PowerSeries.rescale t F : ℂ⟦X⟧) : ℂ⸨X⸩) ∈ E := by
  obtain ⟨hk, d, a, ha₀, had, h⟩ := hMahler
  change a (0 : Fin (d + 1)) ≠ 0 at ha₀
  change a (Fin.last d) ≠ 0 at had
  have hk0 : k ≠ 0 := by omega
  let j : ℂ⟦X⟧ →+* ℂ⸨X⸩ := HahnSeries.ofPowerSeries ℤ ℂ
  let f (n : ℕ) : ℂ⟦X⟧ := PowerSeries.expand (k ^ n) (pow_ne_zero n hk0) F
  have hf₀ : f 0 = F := by simp [f]
  let E : IntermediateField ℂ⟮X⟯ ℂ⸨X⸩ :=
    IntermediateField.adjoin _ (Set.range fun i : Fin d => j (f i))
  have hEfin : FiniteDimensional ℂ⟮X⟯ E := by
    apply IntermediateField.finiteDimensional_adjoin
    rintro _ ⟨i, rfl⟩
    exact expand_isIntegral_ratFunc hP hF _
  have hshift (n : ℕ) (t : ℂ) :
      ∑ i : Fin (d + 1), j (↑((Polynomial.expand ℂ (k ^ n) (a i)).comp (C t * X))) *
        j (PowerSeries.rescale t (f (n + i))) = 0 := by
    let e := PowerSeries.expand (k ^ n) (pow_ne_zero n hk0) (R := ℂ)
    have h' := congrArg (j.comp ((PowerSeries.rescale t).comp e.toRingHom)) h
    change j (PowerSeries.rescale t (e (∑ i : Fin (d + 1), ↑(a i) *
      mahlerSubst F k i.val))) = j (PowerSeries.rescale t (e 0)) at h'
    simp only [map_sum, map_mul, map_zero, e, expand_polynomial, rescale_polynomial,
      mahlerSubst_eq_expand F hk0] at h'
    have hcompose (i : ℕ) :
        PowerSeries.expand (k ^ n) (pow_ne_zero n hk0)
          (PowerSeries.expand (k ^ i) (pow_ne_zero i hk0) F) = f (n + i) := by
      symm
      unfold f
      simp only [pow_add]
      exact PowerSeries.expand_mul _ _ _ _ _
    simpa only [hcompose] using h'
  have hpoly (p : ℂ[X]) : j (p : ℂ⟦X⟧) ∈ E :=
    (polynomial_laurentSeries p).symm ▸
      (IsScalarTower.algebraMap_apply ℂ[X] ℂ⟮X⟯ ℂ⸨X⸩ p) ▸ E.algebraMap_mem _
  have hpoly_ne {p : ℂ[X]} (hp : p ≠ 0) : j (p : ℂ⟦X⟧) ≠ 0 := by
    change ((p : ℂ⟦X⟧) : ℂ⸨X⸩) ≠ 0
    rw [polynomial_laurentSeries]
    simpa only [map_zero] using (FaithfulSMul.algebraMap_injective ℂ[X] ℂ⸨X⸩).ne hp
  -- Solve for the last term to put every forward substitution in the same field.
  have hforward (n : ℕ) : j (f n) ∈ E := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      by_cases hn : n < d
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨n, hn⟩, rfl⟩
      let m := n - d
      have hmd : m + d = n := by omega
      have heq := hshift m 1
      rw [Fin.sum_univ_castSucc] at heq
      simp only [Fin.val_castSucc, Fin.val_last, hmd, map_one, one_mul, comp_X,
        PowerSeries.rescale_one, RingHom.id_apply] at heq
      rw [add_comm] at heq
      refine mem_of_mul_add_eq_zero E (hpoly _) (hpoly_ne ?_) (E.sum_mem ?_) heq
      · simpa only [map_zero] using
          (Polynomial.expand_injective (pow_pos (Nat.pos_of_ne_zero hk0) m)).ne had
      · intro i _
        exact E.mul_mem (hpoly _) (ih _ (by have := i.isLt; omega))
  refine ⟨E, hEfin, ?_⟩
  rintro t ⟨L, ht⟩
  have ht0 : t ≠ 0 := by
    intro ht0
    rw [ht0, zero_pow (pow_ne_zero L hk0)] at ht
    exact zero_ne_one ht
  -- Beyond L the rotation fixes the substituted series. Solve for the first term to descend.
  have hback (r n : ℕ) (hn : L ≤ n + r) : j (PowerSeries.rescale t (f n)) ∈ E := by
    induction r generalizing n with
    | zero =>
      rw [Nat.add_zero] at hn
      rw [show PowerSeries.rescale t (f n) = f n from
        rescale_expand _ (orderOf_dvd_iff_pow_eq_one.mp
          ((orderOf_dvd_of_pow_eq_one ht).trans (pow_dvd_pow k hn))) F]
      exact hforward n
    | succ r ih =>
      have heq := hshift n t
      rw [Fin.sum_univ_succ] at heq
      simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ] at heq
      refine mem_of_mul_add_eq_zero E (hpoly _) (hpoly_ne ?_) (E.sum_mem ?_) heq
      · have ht' := mem_nonZeroDivisors_iff_ne_zero.mpr ht0
        apply (Polynomial.comp_C_mul_X_eq_zero_iff ht').not.mpr
        simpa only [map_zero] using
          (Polynomial.expand_injective (pow_pos (Nat.pos_of_ne_zero hk0) n)).ne ha₀
      · intro i _
        exact E.mul_mem (hpoly _) (ih _ (by omega))
  simpa only [hf₀] using hback L 0 (by simp)

private noncomputable def infinityRing : ValuationSubring ℂ⟮X⟯ := by
  classical
  exact (RatFunc.inftyValuation ℂ).valuationSubring

private theorem mem_infinityRing_iff {r : ℂ⟮X⟯} :
    r ∈ infinityRing ↔ r = 0 ∨ r.intDegree ≤ 0 := by
  classical
  rw [infinityRing, Valuation.mem_valuationSubring_iff, RatFunc.inftyValuation_apply]
  by_cases hr : r = 0
  · simp [hr, RatFunc.inftyValuationDef]
  · rw [RatFunc.inftyValuation_of_ne_zero _ hr, or_iff_right hr]
    change WithZero.exp r.intDegree ≤ WithZero.exp (0 : ℤ) ↔ r.intDegree ≤ 0
    exact WithZero.exp_le_exp

private theorem intDegree_X_pow (N : ℕ) :
    (RatFunc.X ^ N : ℂ⟮X⟯).intDegree = N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero _ RatFunc.X_ne_zero) RatFunc.X_ne_zero,
      ih, RatFunc.intDegree_X, Nat.cast_succ]

private theorem polynomial_mul_inv_pow_mem_infinityRing {p : ℂ[X]} {N : ℕ}
    (hp : p.natDegree ≤ N) :
    algebraMap ℂ[X] ℂ⟮X⟯ p * (RatFunc.X ^ N)⁻¹ ∈ infinityRing := by
  rw [mem_infinityRing_iff]
  by_cases hp0 : p = 0
  · simp [hp0]
  right
  have hp' : algebraMap ℂ[X] ℂ⟮X⟯ p ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective ℂ[X] ℂ⟮X⟯).ne hp0
  rw [RatFunc.intDegree_mul hp' (inv_ne_zero (pow_ne_zero _ RatFunc.X_ne_zero)),
    RatFunc.intDegree_inv, intDegree_X_pow, RatFunc.intDegree_polynomial]
  omega

private theorem natDegree_le_of_mem_infinityRing {p : ℂ[X]} {N : ℕ}
    (hp : algebraMap ℂ[X] ℂ⟮X⟯ p * (RatFunc.X ^ N)⁻¹ ∈ infinityRing) :
    p.natDegree ≤ N := by
  by_cases hp0 : p = 0
  · simp [hp0]
  have hp' : algebraMap ℂ[X] ℂ⟮X⟯ p ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective ℂ[X] ℂ⟮X⟯).ne hp0
  have hX : (RatFunc.X ^ N : ℂ⟮X⟯)⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ RatFunc.X_ne_zero)
  have h := (mem_infinityRing_iff.mp hp).resolve_left (mul_ne_zero hp' hX)
  rw [RatFunc.intDegree_mul hp' hX, RatFunc.intDegree_inv, intDegree_X_pow,
    RatFunc.intDegree_polynomial] at h
  omega

private theorem integral_at_infinity (E : IntermediateField ℂ⟮X⟯ ℂ⸨X⸩)
    {Q : ℂ[X][X]} (hQ : Q.Monic) {x : E} (hx : aeval x Q = 0)
    {N : ℕ} (hN : ∀ i, (Q.coeff i).natDegree ≤ N) :
    IsIntegral infinityRing ((RatFunc.X ^ N : ℂ⟮X⟯)⁻¹ • x) := by
  classical
  let Q' := Q.map (algebraMap ℂ[X] ℂ⟮X⟯)
  have hQ' : Q'.Monic := hQ.map _
  let u : ℂ⟮X⟯ := (RatFunc.X ^ N)⁻¹
  let S := Q'.scaleRoots u
  have hSm : S.Monic := (monic_scaleRoots_iff u).mpr hQ'
  have hdeg : S.natDegree = Q'.natDegree := natDegree_scaleRoots _ _
  have hSe : aeval (u • x) S = 0 := by
    apply scaleRoots_aeval_eq_zero
    rw [aeval_map_algebraMap, hx]
  have hcoeff (i : ℕ) : S.coeff i ∈ infinityRing := by
    rcases lt_trichotomy i Q'.natDegree with hi | hi | hi
    · have he : N ≤ N * (Q'.natDegree - i) := by
        simpa only [mul_one] using Nat.mul_le_mul_left N (show 1 ≤ Q'.natDegree - i by omega)
      rw [show S.coeff i = algebraMap ℂ[X] ℂ⟮X⟯ (Q.coeff i) *
          (RatFunc.X ^ (N * (Q'.natDegree - i)))⁻¹ by
        simp only [S, Q', u, coeff_scaleRoots, coeff_map, inv_pow, pow_mul]]
      exact polynomial_mul_inv_pow_mem_infinityRing ((hN i).trans he)
    · rw [hi, show S.coeff Q'.natDegree = 1 by
        rw [← hdeg, ← leadingCoeff]
        exact hSm]
      exact one_mem _
    · rw [coeff_eq_zero_of_natDegree_lt (hdeg.symm ▸ hi)]
      exact zero_mem _
  have hlift : S ∈ lifts (algebraMap infinityRing ℂ⟮X⟯) :=
    (lifts_iff_coeff_lifts S).mpr fun i => ⟨⟨S.coeff i, hcoeff i⟩, rfl⟩
  obtain ⟨T, hT, -, hTm⟩ := lifts_and_natDegree_eq_and_monic hlift hSm
  refine ⟨T, hTm, ?_⟩
  change eval₂ (algebraMap infinityRing E) (u • x) T = 0
  rw [IsScalarTower.algebraMap_eq infinityRing ℂ⟮X⟯ E, ← eval₂_map, hT]
  exact hSe

private theorem exists_coeff_degree_bound (Q : ℂ[X][X]) :
    ∃ N : ℕ, ∀ i, (Q.coeff i).natDegree ≤ N := by
  classical
  refine ⟨Q.support.sup fun i => (Q.coeff i).natDegree, fun i => ?_⟩
  by_cases hi : i ∈ Q.support
  · exact Finset.le_sup (f := fun i => (Q.coeff i).natDegree) hi
  · simp [notMem_support_iff.mp hi]

private theorem rescalePolynomial_degree_le (t : ℂ) (p : ℂ[X]) :
    (rescalePolynomial t p).natDegree ≤ p.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [map_rescalePolynomial, comp_C_mul_X_coeff, coeff_eq_zero_of_natDegree_lt hn, zero_mul]

private theorem rescale_eval₂ {G : ℂ⟦X⟧} {Q : ℂ[X][X]}
    (h : eval₂ (algebraMap ℂ[X] ℂ⟦X⟧) G Q = 0) (t : ℂ) :
    eval₂ (algebraMap ℂ[X] ℂ⟦X⟧) (PowerSeries.rescale t G)
      (Q.map (rescalePolynomial t)) = 0 := by
  rw [eval₂_map]
  have h' := congrArg (PowerSeries.rescale t) h
  rw [hom_eval₂, map_zero] at h'
  convert h' using 1
  congr 1
  apply RingHom.ext
  intro p
  simp only [RingHom.comp_apply, powerSeries_algebraMap, map_rescalePolynomial, rescale_polynomial]

private theorem integral_trace_degree_bound (E : IntermediateField ℂ⟮X⟯ ℂ⸨X⸩)
    [FiniteDimensional ℂ⟮X⟯ E] {x y : E} (hx : IsIntegral ℂ[X] x) (hy : IsIntegral ℂ[X] y)
    {N M : ℕ} (hx' : IsIntegral infinityRing ((RatFunc.X ^ N : ℂ⟮X⟯)⁻¹ • x))
    (hy' : IsIntegral infinityRing ((RatFunc.X ^ M : ℂ⟮X⟯)⁻¹ • y)) :
    ∃ p : ℂ[X], p.natDegree ≤ N + M ∧
      algebraMap ℂ[X] ℂ⟮X⟯ p = Algebra.trace ℂ⟮X⟯ E (x * y) := by
  obtain ⟨p, hp⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (Algebra.isIntegral_trace (L := ℂ⟮X⟯) (hx.mul hy))
  refine ⟨p, ?_, hp⟩
  have hmul :
      ((RatFunc.X ^ N : ℂ⟮X⟯)⁻¹ • x) * ((RatFunc.X ^ M : ℂ⟮X⟯)⁻¹ • y) =
        ((RatFunc.X ^ (N + M) : ℂ⟮X⟯)⁻¹) • (x * y) := by
    simp only [Algebra.smul_def, pow_add, mul_inv_rev, map_mul]
    ring
  have h := Algebra.isIntegral_trace (L := ℂ⟮X⟯) (hx'.mul hy')
  rw [hmul, map_smul, smul_eq_mul, ← hp, mul_comm] at h
  obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact natDegree_le_of_mem_infinityRing (hv ▸ v.property)

private theorem exists_integral_basis (E : IntermediateField ℂ⟮X⟯ ℂ⸨X⸩)
    [FiniteDimensional ℂ⟮X⟯ E] :
    ∃ b : Module.Basis (Fin (Module.finrank ℂ⟮X⟯ E)) ℂ⟮X⟯ E,
      ∀ i, IsIntegral ℂ[X] (b i) := by
  let b := Module.finBasis ℂ⟮X⟯ E
  have h (i : Fin (Module.finrank ℂ⟮X⟯ E)) :
      ∃ a : nonZeroDivisors ℂ[X], IsIntegral ℂ[X] (a • b i) :=
    IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℂ[X]) _ <|
      Algebra.IsIntegral.isIntegral (R := ℂ⟮X⟯) (b i)
  choose a ha using h
  have hunit (i : Fin (Module.finrank ℂ⟮X⟯ E)) :
      IsUnit (algebraMap ℂ[X] ℂ⟮X⟯ (a i : ℂ[X])) :=
    IsLocalization.map_units ℂ⟮X⟯ (a i)
  refine ⟨b.isUnitSMul hunit, fun i => ?_⟩
  rw [Module.Basis.isUnitSMul_apply, algebraMap_smul]
  exact ha i

private theorem lift_eval₂_to_intermediateField (E : IntermediateField ℂ⟮X⟯ ℂ⸨X⸩)
    {G : ℂ⟦X⟧} {Q : ℂ[X][X]} (hQ : eval₂ (algebraMap ℂ[X] ℂ⟦X⟧) G Q = 0)
    (hG : (G : ℂ⸨X⸩) ∈ E) :
    aeval (⟨(G : ℂ⸨X⸩), hG⟩ : E) Q = 0 := by
  let j : ℂ⟦X⟧ →+* ℂ⸨X⸩ := HahnSeries.ofPowerSeries ℤ ℂ
  let e := E.val.toRingHom
  apply e.injective
  rw [map_zero]
  change e (eval₂ (algebraMap ℂ[X] E) _ Q) = 0
  rw [hom_eval₂]
  have hcomp : e.comp (algebraMap ℂ[X] E) = j.comp (algebraMap ℂ[X] ℂ⟦X⟧) := by
    apply RingHom.ext
    intro p
    change algebraMap E ℂ⸨X⸩ (algebraMap ℂ[X] E p) = j (algebraMap ℂ[X] ℂ⟦X⟧ p)
    rw [IsScalarTower.algebraMap_apply ℂ[X] ℂ⟮X⟯ E,
      ← IsScalarTower.algebraMap_apply ℂ⟮X⟯ E ℂ⸨X⸩,
      ← IsScalarTower.algebraMap_apply ℂ[X] ℂ⟮X⟯ ℂ⸨X⸩, powerSeries_algebraMap]
    exact (polynomial_laurentSeries p).symm
  rw [hcomp]
  change eval₂ (j.comp (algebraMap ℂ[X] ℂ⟦X⟧)) (j G) Q = 0
  rw [← hom_eval₂, hQ, map_zero]

set_option maxHeartbeats 600000 in
-- Elaborating the trace coordinates resolves several scalar towers into Laurent series.
private theorem rotations_mem_finite_submodule (E : IntermediateField ℂ⟮X⟯ ℂ⸨X⸩)
    [FiniteDimensional ℂ⟮X⟯ E] (G : ℂ⟦X⟧) (S : Set ℂ)
    (hE : ∀ t ∈ S, ((PowerSeries.rescale t G : ℂ⟦X⟧) : ℂ⸨X⸩) ∈ E)
    {Q : ℂ[X][X]} (hQ : Q.Monic) (hG : eval₂ (algebraMap ℂ[X] ℂ⟦X⟧) G Q = 0) :
    ∃ W : Submodule ℂ ℂ⸨X⸩, Module.Finite ℂ W ∧
      ∀ t ∈ S, ((PowerSeries.rescale t G : ℂ⟦X⟧) : ℂ⸨X⸩) ∈ W := by
  classical
  let ι := Fin (Module.finrank ℂ⟮X⟯ E)
  obtain ⟨b, hb⟩ := exists_integral_basis E
  choose B hBm hBe using hb
  have hB (i : ι) := exists_coeff_degree_bound (B i)
  choose M hM using hB
  obtain ⟨N, hN⟩ := exists_coeff_degree_bound Q
  let D := N + (Finset.univ : Finset ι).sup M
  let bDual : Module.Basis ι ℂ⟮X⟯ E := by
    exact Module.Basis.traceDual (K := ℂ⟮X⟯) (L := ↥E) b
  let v (i : ι × Fin (D + 1)) : ℂ⸨X⸩ :=
    ((RatFunc.X ^ (i.2 : ℕ) : ℂ⟮X⟯) • ((bDual i.1) : E) : E)
  let W := Submodule.span ℂ (Set.range v)
  refine ⟨W, Module.Finite.span_of_finite _ (Set.finite_range v), ?_⟩
  intro t ht
  let x : E := ⟨(PowerSeries.rescale t G : ℂ⟦X⟧), hE t ht⟩
  let Q' := Q.map (rescalePolynomial t)
  have hQ' : Q'.Monic := hQ.map _
  have hxQ : aeval x Q' = 0 := lift_eval₂_to_intermediateField E (rescale_eval₂ hG t) (hE t ht)
  have hx : IsIntegral ℂ[X] x := ⟨Q', hQ', hxQ⟩
  have hx' := integral_at_infinity E hQ' hxQ (N := N) fun i => by
    rw [show Q'.coeff i = rescalePolynomial t (Q.coeff i) by simp [Q']]
    exact (rescalePolynomial_degree_le t _).trans (hN i)
  have hRepr (i : ι) :
      ∃ p : ℂ[X], p.natDegree ≤ D ∧
        algebraMap ℂ[X] ℂ⟮X⟯ p = bDual.repr x i := by
    obtain ⟨p, hp, he⟩ := integral_trace_degree_bound E hx ⟨B i, hBm i, hBe i⟩ hx'
      (integral_at_infinity E (hBm i) (hBe i) (hM i))
    have hMi : M i ≤ (Finset.univ : Finset ι).sup M := Finset.le_sup (Finset.mem_univ i)
    refine ⟨p, hp.trans (Nat.add_le_add_left hMi N), ?_⟩
    rw [he]
    have hcoord := Module.Basis.traceDual_repr_apply (K := ℂ⟮X⟯) (L := ↥E) b x i
    rw [Algebra.traceForm_apply] at hcoord
    exact hcoord.symm
  choose p hp hpr using hRepr
  have hs (i : ι) :
      ((((algebraMap ℂ[X] ℂ⟮X⟯ (p i)) • bDual i) : E) : ℂ⸨X⸩) ∈ W := by
    let l : ℂ[X] →ₗ[ℂ] ℂ⸨X⸩ :=
      { toFun := fun q => ((q : ℂ⟦X⟧) : ℂ⸨X⸩) * (bDual i : ℂ⸨X⸩)
        map_add' := fun q r => by
          simp only [Polynomial.coe_add, PowerSeries.coe_add, add_mul]
        map_smul' := fun c q => by
          simp only [RingHom.id_apply, Polynomial.coe_smul, PowerSeries.coe_smul]
          simp only [← HahnSeries.C_mul_eq_smul, mul_assoc] }
    have hl (q : ℂ[X]) : l q = algebraMap ℂ[X] ℂ⟮X⟯ q • (bDual i : ℂ⸨X⸩) := by
      change ((q : ℂ⟦X⟧) : ℂ⸨X⸩) * (bDual i : ℂ⸨X⸩) = _
      rw [polynomial_laurentSeries, IsScalarTower.algebraMap_apply ℂ[X] ℂ⟮X⟯ ℂ⸨X⸩,
        Algebra.smul_def]
    change algebraMap ℂ[X] ℂ⟮X⟯ (p i) • (bDual i : ℂ⸨X⸩) ∈ W
    rw [← hl]
    have hpd : p i ∈ degreeLE ℂ (D : WithBot ℕ) :=
      mem_degreeLE.mpr (degree_le_natDegree.trans (by exact_mod_cast hp i))
    rw [degreeLE_eq_span_X_pow] at hpd
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hpd
    · intro q hq
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hq
      have hn' := Finset.mem_range.mp hn
      exact Submodule.subset_span ⟨(i, ⟨n, hn'⟩), by
        rw [hl, map_pow, RatFunc.algebraMap_X]
        rfl⟩
    · simpa only [map_zero] using W.zero_mem
    · intro q r _ _ hq hr
      rw [map_add]
      exact W.add_mem hq hr
    · intro c q _ hq
      rw [map_smul]
      exact W.smul_mem c hq
  have hsum := congrArg E.val (bDual.sum_repr x)
  simp only [map_sum, AlgHom.map_smul_of_tower] at hsum
  change E.val x ∈ W
  rw [← hsum]
  exact W.sum_mem fun i _ => by
    rw [← hpr i]
    exact hs i

private theorem finite_support_of_rotations (k : ℕ) (hk : 2 ≤ k) (G : ℂ⟦X⟧)
    (W : Submodule ℂ ℂ⸨X⸩) [Module.Finite ℂ W]
    (hW : ∀ t : ℂ, (∃ L : ℕ, t ^ (k ^ L) = 1) →
      ((PowerSeries.rescale t G : ℂ⟦X⟧) : ℂ⸨X⸩) ∈ W) :
    {n : ℕ | PowerSeries.coeff n G ≠ 0}.Finite := by
  classical
  by_contra h
  let m := Module.finrank ℂ W + 1
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq h m
  let L := s.sup id
  have hkL : k ^ L ≠ 0 := pow_ne_zero _ (by omega)
  let t := Complex.exp (2 * Real.pi * Complex.I / (k ^ L : ℕ))
  have ht : IsPrimitiveRoot t (k ^ L) := Complex.isPrimitiveRoot_exp _ hkL
  let v (j : Fin m) : W :=
    ⟨(PowerSeries.rescale (t ^ (j : ℕ)) G : ℂ⟦X⟧),
      hW _ ⟨L, by rw [pow_right_comm, ht.pow_eq_one, one_pow]⟩⟩
  -- A dependence would give a polynomial of degree less than m with m distinct roots.
  have hli : LinearIndependent ℂ v := by
    apply (Fintype.linearIndependent_iff (R := ℂ) (v := v)).mpr
    intro c hc j
    let P : ℂ[X] := ∑ i : Fin m, monomial (i : ℕ) (c i)
    have hPdeg : P.natDegree ≤ m - 1 := by
      apply natDegree_sum_le_of_forall_le
      intro i _
      exact (natDegree_monomial_le _).trans (by have := i.isLt; omega)
    have hP : P = 0 := by
      apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero P (f := fun n : s => t ^ (n : ℕ))
      · intro a b hab
        have hlt (n : s) : (n : ℕ) < k ^ L :=
          (Finset.le_sup (f := id) n.property).trans_lt (Nat.lt_pow_self (by omega))
        exact Subtype.ext (ht.pow_inj (hlt a) (hlt b) hab)
      · intro n
        have hcn := congrArg (fun x : W => (x : ℂ⸨X⸩).coeff (n : ℕ)) hc
        simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero, HahnSeries.coeff_sum,
          HahnSeries.coeff_smul, HahnSeries.coeff_zero] at hcn
        have hcn' : ∑ i : Fin m, c i * ((t ^ (i : ℕ)) ^ (n : ℕ) *
            PowerSeries.coeff (n : ℕ) G) = 0 := by
          simpa only [v, LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_rescale,
            smul_eq_mul] using hcn
        have hn : PowerSeries.coeff (n : ℕ) G ≠ 0 := hs n.property
        have heval : P.eval (t ^ (n : ℕ)) = ∑ i : Fin m, c i * (t ^ (n : ℕ)) ^ (i : ℕ) := by
          simp only [P, eval_finsetSum, eval_monomial]
        have hprod : P.eval (t ^ (n : ℕ)) * PowerSeries.coeff (n : ℕ) G = 0 := by
          rw [heval, Finset.sum_mul]
          simpa only [mul_assoc, pow_right_comm t (n : ℕ)] using hcn'
        exact (mul_eq_zero.mp hprod).resolve_right hn
      · simpa only [Fintype.card_coe, hcard] using
          (lt_of_le_of_lt hPdeg (show m - 1 < m by dsimp [m]; omega))
    have hcoeff := congrArg (fun p : ℂ[X] => p.coeff (j : ℕ)) hP
    rw [coeff_zero] at hcoeff
    simpa only [P, finsetSum_coeff, coeff_monomial, Finsupp.single_apply, Fin.val_inj,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hcoeff
  have hdim := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at hdim
  omega

end NishiokaMahlerRationality

open NishiokaMahlerRationality in
/-- **Nishioka's theorem: algebraic Mahler functions are rational.** Let $k$ be a natural number
and let $F \in \mathbb{C}[[z]]$ be a $k$-Mahler function. If $F$ is algebraic over
$\mathbb{C}[z]$, that is, $P(F) = 0$ for some nonzero polynomial $P$ with coefficients in
$\mathbb{C}[z]$, then $F$ is rational: there are polynomials $p, q \in \mathbb{C}[z]$ with $q \ne 0$
and $qF = p$ in $\mathbb{C}[[z]]$.

Source: Jason P. Bell, Michael Coons, and Eric Rowland, "The
Rational-Transcendental Dichotomy of Mahler Functions", Journal of Integer
Sequences 16 (2013), Article 13.2.10, Nishioka corollary lines 238–241,
<https://cs.uwaterloo.ca/journals/JIS/VOL16/Bell/bell2.tex>.
The corollary is attributed to Ku. Nishioka, "Mahler Functions and
Transcendence", Lecture Notes in Mathematics 1294, Theorem 5.1.7. -/
public theorem nishioka_algebraic_kMahler_is_rational
    (k : ℕ) (F : PowerSeries ℂ)
    (hMahler : IsKMahlerFunction k F)
    (hAlgebraic : ∃ P : Polynomial (Polynomial ℂ), P ≠ 0 ∧
      Polynomial.eval₂ (algebraMap (Polynomial ℂ) (PowerSeries ℂ)) F P = 0) :
    ∃ p q : Polynomial ℂ, q ≠ 0 ∧
      Polynomial.toPowerSeries q * F = Polynomial.toPowerSeries p := by
  obtain ⟨P, hP, hF⟩ := hAlgebraic
  obtain ⟨E, hEfin, hE⟩ := rotations_mem_finite_extension k F hMahler hP hF
  let q := P.leadingCoeff
  have hq : q ≠ 0 := leadingCoeff_ne_zero.mpr hP
  let G := Polynomial.toPowerSeries q * F
  have hGp : eval₂ (algebraMap ℂ[X] ℂ⟦X⟧) G P.integralNormalization = 0 := by
    rw [show G = algebraMap ℂ[X] ℂ⟦X⟧ P.leadingCoeff * F by rw [powerSeries_algebraMap]]
    exact integralNormalization_eval₂_eq_zero _ hF (by
      intro p hp
      rw [powerSeries_algebraMap] at hp
      exact (Polynomial.coe_injective ℂ) (hp.trans (Polynomial.coe_zero (R := ℂ)).symm))
  let S : Set ℂ := {t | ∃ L : ℕ, t ^ (k ^ L) = 1}
  have hGE (t : ℂ) (ht : t ∈ S) : ((PowerSeries.rescale t G : ℂ⟦X⟧) : ℂ⸨X⸩) ∈ E := by
    change ((PowerSeries.rescale t ((q : ℂ⟦X⟧) * F) : ℂ⟦X⟧) : ℂ⸨X⸩) ∈ E
    rw [map_mul, PowerSeries.coe_mul, rescale_polynomial, polynomial_laurentSeries,
      IsScalarTower.algebraMap_apply ℂ[X] ℂ⟮X⟯ ℂ⸨X⸩]
    exact E.mul_mem (E.algebraMap_mem _) (hE t ht)
  obtain ⟨W, hWfin, hW⟩ :=
    rotations_mem_finite_submodule E G S hGE (monic_integralNormalization hP) hGp
  have hs := finite_support_of_rotations k hMahler.1 G W hW
  obtain ⟨n, hn⟩ := hs.bddAbove
  refine ⟨PowerSeries.trunc (n + 1) G, q, hq, ?_⟩
  change G = (PowerSeries.trunc (n + 1) G : ℂ⟦X⟧)
  ext i
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hi
  · rfl
  · by_contra hne
    exact hi (by have := hn (show i ∈ {j : ℕ | PowerSeries.coeff j G ≠ 0} from hne); omega)

end MetaMathlibExt
