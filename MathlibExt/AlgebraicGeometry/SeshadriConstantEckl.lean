/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.SeshadriConstant
import MathlibExt.AlgebraicGeometry.PointMultiplicity
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-!
# Eckl's lower bound for the ten-point Seshadri constant

This module proves Eckl's lower bound $4/13$ for the affine-chart Seshadri constant.
The proof first bounds a weighted sum of multiplicities using eight lines through
a rational configuration. Matrices of Taylor coefficients transfer the bound to
algebraically independent coordinates, where cyclic relabelings give the unweighted bound.
-/

namespace MathlibExt.AlgebraicGeometry.SeshadriConstantWanted

namespace Eckl2008

open MathlibExt.AlgebraicGeometry.SeshadriConstant
open MvPolynomial Finset
open scoped Polynomial Matrix

private theorem monomialDegree_eq (d : Fin 2 →₀ ℕ) : monomialDegree d = d.degree := by
  rw [Finsupp.degree_eq_sum]
  rfl

private theorem orderAt_eq {f : PlanePolynomial} (hf : f ≠ 0) (x : AffinePoint) :
    f.orderAt x = (multiplicity f x : ℕ∞) := by
  classical
  have hne : (shifted f x).support.Nonempty :=
    MvPolynomial.support_nonempty.mpr (shifted_eq_zero_iff.not.mpr hf)
  rw [SeshadriConstant.multiplicity, dite_eq_left hne]
  let s := (shifted f x).support.image monomialDegree
  change ((shifted f x : PlanePolynomial) : MvPowerSeries (Fin 2) ℂ).order =
    (s.min' (Finset.image_nonempty.mpr hne) : ℕ∞)
  rw [MvPowerSeries.order_eq_nat]
  constructor
  · obtain ⟨d, hd, he⟩ := Finset.mem_image.mp
      (s.min'_mem (Finset.image_nonempty.mpr hne))
    exact ⟨d, by simpa only [coeff_coe] using mem_support_iff.mp hd,
      by simpa only [monomialDegree_eq] using he⟩
  · intro d hd
    rw [coeff_coe]
    by_contra hn
    have hle : s.min' (Finset.image_nonempty.mpr hne) ≤ monomialDegree d :=
      s.min'_le _ (Finset.mem_image.mpr ⟨d, mem_support_iff.mpr hn, rfl⟩)
    exact (not_lt_of_ge ((monomialDegree_eq d) ▸ hle)) hd

private theorem multiplicity_mul {f g : PlanePolynomial} (hf : f ≠ 0) (hg : g ≠ 0)
    (x : AffinePoint) :
    multiplicity (f * g) x = multiplicity f x + multiplicity g x := by
  have h : (f * g).orderAt x = f.orderAt x + g.orderAt x := by
    simp only [orderAt, map_mul, MvPolynomial.coe_mul, MvPowerSeries.order_mul]
  rw [orderAt_eq (mul_ne_zero hf hg), orderAt_eq hf, orderAt_eq hg, ← Nat.cast_add] at h
  exact Nat.cast_injective h

private theorem coeff_shifted_eq_zero_of_lt {f : PlanePolynomial} {x : AffinePoint}
    {d : Fin 2 →₀ ℕ} (h : d.degree < multiplicity f x) :
    (shifted f x).coeff d = 0 := by
  by_contra hc
  exact (not_lt_of_ge (monomialDegree_eq d ▸
    multiplicity_le_of_mem_support (mem_support_iff.mpr hc))) h

private theorem multiplicity_ge_of_coeff_shifted_eq_zero {f : PlanePolynomial}
    (hf : f ≠ 0) {x : AffinePoint} {m : ℕ}
    (h : ∀ d : Fin 2 →₀ ℕ, d.degree < m → (shifted f x).coeff d = 0) :
    m ≤ multiplicity f x := by
  have h' : (m : ℕ∞) ≤ f.orderAt x :=
    MvPowerSeries.nat_le_order (fun d hd => by rw [coeff_coe]; exact h d hd)
  simpa only [orderAt_eq hf, Nat.cast_le] using h'

private theorem restriction_degree (f : PlanePolynomial) (u : Fin 2 → ℂ[X])
    (hu : ∀ i, (u i).natDegree ≤ 1) :
    (MvPolynomial.aeval u f).natDegree ≤ f.totalDegree := by
  conv_lhs => rw [f.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  rw [aeval_monomial, Polynomial.algebraMap_eq]
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  calc
    (d.prod fun i n => u i ^ n).natDegree ≤
        ∑ i ∈ d.support, (u i ^ d i).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      gcongr with i _
      exact (Polynomial.natDegree_pow_le).trans (by simpa using Nat.mul_le_mul_left (d i) (hu i))
    _ = d.degree := by rw [Finsupp.degree_apply]
    _ ≤ f.totalDegree := le_totalDegree hd

private theorem restriction_rootMultiplicity {f : PlanePolynomial} (u : Fin 2 → ℂ[X])
    (t : ℂ) (hf : MvPolynomial.aeval u f ≠ 0) :
    multiplicity f (fun i => (u i).eval t) ≤
      (MvPolynomial.aeval u f).rootMultiplicity t := by
  let x : AffinePoint := fun i => (u i).eval t
  let v : Fin 2 → ℂ[X] := fun i => u i - Polynomial.C (x i)
  have hcomp : (aeval v).comp (aeval (fun i => X i + C (x i))) = aeval u := by
    apply algHom_ext
    intro i
    simp [v]
  rw [Polynomial.le_rootMultiplicity_iff hf]
  change (Polynomial.X - Polynomial.C t) ^ multiplicity f x ∣ aeval u f
  rw [← hcomp, AlgHom.comp_apply]
  change _ ∣ aeval v (shifted f x)
  rw [(shifted f x).as_sum, map_sum]
  apply Finset.dvd_sum
  intro d hd
  rw [aeval_monomial]
  apply dvd_mul_of_dvd_right
  have hterm (i : Fin 2) : Polynomial.X - Polynomial.C t ∣ v i := by
    rw [Polynomial.dvd_iff_isRoot]
    simp [Polynomial.IsRoot, v, x]
  have hle : multiplicity f x ≤ ∑ i ∈ d.support, d i := by
    simpa only [monomialDegree_eq, Finsupp.degree_apply] using
      multiplicity_le_of_mem_support hd
  refine (pow_dvd_pow _ hle).trans ?_
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => pow_dvd_pow_of_dvd (hterm i) _)

/-- A line written as one coordinate equal to an affine function of the other. -/
private structure Line where
  coord : Fin 2
  slope : ℚ
  intercept : ℚ

private theorem other_ne (i : Fin 2) : 1 - i ≠ i := by
  fin_cases i <;> decide

private theorem eq_other {i j : Fin 2} (h : j ≠ i) : j = 1 - i := by
  fin_cases i <;> fin_cases j <;> simp_all

private noncomputable def Line.equation (l : Line) : PlanePolynomial :=
  X l.coord - (C (l.slope : ℂ) * X (1 - l.coord) + C (l.intercept : ℂ))

private noncomputable def Line.param (l : Line) (i : Fin 2) : ℂ[X] :=
  if i = l.coord then Polynomial.C (l.slope : ℂ) * Polynomial.X +
    Polynomial.C (l.intercept : ℂ) else Polynomial.X

private def Line.Contains (l : Line) (x : Fin 2 → ℚ) : Prop :=
  x l.coord = l.slope * x (1 - l.coord) + l.intercept

private instance instDecidableContains (l : Line) (x : Fin 2 → ℚ) : Decidable (l.Contains x) := by
  unfold Line.Contains
  infer_instance

private theorem Line.contains_iff (l : Line) (x : Fin 2 → ℚ) :
    l.Contains x ↔ eval (fun i => (x i : ℂ)) l.equation = 0 := by
  simp only [Line.Contains, Line.equation, map_sub, map_add, map_mul, eval_X, eval_C, sub_eq_zero]
  norm_cast

private theorem Line.param_eval (l : Line) (x : Fin 2 → ℚ) (hx : l.Contains x) (i : Fin 2) :
    (l.param i).eval (x (1 - l.coord) : ℂ) = (x i : ℂ) := by
  by_cases hi : i = l.coord
  · subst i
    simp only [Line.param, ite_eq_left, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    exact_mod_cast hx.symm
  · simp [Line.param, eq_other hi, other_ne]

private theorem Line.coeff_shifted (l : Line) (x : AffinePoint) :
    (shifted l.equation x).coeff (Finsupp.single l.coord 1) = 1 := by
  have hne : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single l.coord 1 :=
    (Finsupp.single_ne_zero.mpr one_ne_zero).symm
  simp [shifted, Line.equation, mul_add, coeff_C_mul, coeff_single_X, coeff_C, hne, other_ne]

private theorem Line.ne_zero (l : Line) : l.equation ≠ 0 := by
  intro h
  have hc := l.coeff_shifted 0
  simp [h, shifted] at hc

private theorem Line.degree (l : Line) : l.equation.totalDegree = 1 := by
  have hle : l.equation.totalDegree ≤ 1 := by
    unfold Line.equation
    apply (totalDegree_sub _ _).trans
    apply max_le (totalDegree_X l.coord).le
    apply (totalDegree_add _ _).trans
    apply max_le _ (by simp)
    exact (totalDegree_mul _ _).trans (by simp)
  have hc := l.coeff_shifted 0
  simp only [shifted, Pi.zero_apply, map_zero, add_zero, aeval_X_left_apply] at hc
  have hl := le_totalDegree (mem_support_iff.mpr (hc.trans_ne one_ne_zero))
  simpa using le_antisymm hle (by simpa using hl)

private theorem Line.multiplicity_eq (l : Line) (x : Fin 2 → ℚ) :
    multiplicity l.equation (fun i => (x i : ℂ)) = if l.Contains x then 1 else 0 := by
  split_ifs with hx
  · apply le_antisymm
    · have h := multiplicity_le_of_mem_support
        (mem_support_iff.mpr ((l.coeff_shifted (fun i => (x i : ℂ))).trans_ne one_ne_zero))
      simpa [monomialDegree_eq] using h
    · exact multiplicity_pos_of_eval_eq_zero l.ne_zero ((l.contains_iff x).mp hx)
  · exact multiplicity_eq_zero_of_eval_ne_zero (fun h => hx ((l.contains_iff x).mpr h))

private theorem Line.dvd_of_restriction_eq_zero (l : Line) (f : PlanePolynomial)
    (hf : aeval l.param f = 0) : l.equation ∣ f := by
  let I : Ideal PlanePolynomial := Ideal.span {l.equation}
  let q := Ideal.Quotient.mkₐ ℂ I
  let lift : ℂ[X] →ₐ[ℂ] PlanePolynomial := Polynomial.aeval (X (1 - l.coord))
  have hq : q l.equation = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton_self _)
  have h : (q.comp lift).comp (aeval l.param) = q := by
    apply algHom_ext
    intro i
    by_cases hi : i = l.coord
    · subst i
      have hq' : q (X l.coord) =
          q (C (l.slope : ℂ) * X (1 - l.coord) + C (l.intercept : ℂ)) := by
        simpa only [Line.equation, map_sub, sub_eq_zero] using hq
      simpa [Line.param, lift, Polynomial.aeval_C, algebraMap_eq] using hq'.symm
    · simp [Line.param, lift, eq_other hi, other_ne]
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q f = 0
  rw [← h, AlgHom.comp_apply, hf, map_zero]

private theorem Line.sum_multiplicity_le (l : Line) (f : PlanePolynomial)
    (hf : ¬ l.equation ∣ f) (p : Fin 10 → Fin 2 → ℚ) (s : Finset (Fin 10))
    (hp : ∀ i ∈ s, l.Contains (p i))
    (hinj : Function.Injective fun i : s => p i) :
    ∑ i ∈ s, multiplicity f (fun j => (p i j : ℂ)) ≤ f.totalDegree := by
  classical
  let P := aeval l.param f
  have hP : P ≠ 0 := fun h => hf (l.dvd_of_restriction_eq_zero f h)
  let t (i : Fin 10) : ℂ := (p i (1 - l.coord) : ℂ)
  have ht : Set.InjOn t ↑s := by
    intro i hi k hk hik
    refine congrArg (fun a : s => a.val) (hinj (a₁ := ⟨i, hi⟩) (a₂ := ⟨k, hk⟩) ?_)
    funext j
    apply Rat.cast_injective (α := ℂ)
    have hpi := l.param_eval (p i) (hp i hi) j
    have hpk := l.param_eval (p k) (hp k hk) j
    change (l.param j).eval (t i) = _ at hpi
    change (l.param j).eval (t k) = _ at hpk
    exact hpi.symm.trans ((congrArg (fun a => (l.param j).eval a) hik).trans hpk)
  have hsum : ∑ i ∈ s, multiplicity f (fun j => (p i j : ℂ)) ≤
      ∑ i ∈ s, P.roots.count (t i) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [Polynomial.count_roots]
    have hpoint : (fun j => (l.param j).eval (t i)) = fun j => (p i j : ℂ) :=
      funext (l.param_eval (p i) (hp i hi))
    simpa only [hpoint] using restriction_rootMultiplicity l.param (t i) hP
  apply hsum.trans
  rw [← Finset.sum_image (f := fun a => P.roots.count a) ht]
  calc
    ∑ a ∈ s.image t, P.roots.count a ≤
        ∑ a ∈ s.image t ∪ P.roots.toFinset, P.roots.count a :=
      Finset.sum_le_sum_of_subset Finset.subset_union_left
    _ = P.roots.card := Multiset.sum_count_eq_card (by
      intro a ha
      exact Finset.mem_union_right _ (Multiset.mem_toFinset.mpr ha))
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ ≤ f.totalDegree := by
      apply restriction_degree
      intro i
      unfold Line.param
      split_ifs
      · apply (Polynomial.natDegree_add_le _ _).trans
        exact max_le ((Polynomial.natDegree_C_mul_le _ _).trans (by simp)) (by simp)
      · simp

/-- The first six points lie on the sides of a triangle. The last four lie on
(x + 3y = 20), at its intersections with four secants of the first six points. -/
private def model : Fin 10 → Fin 2 → ℚ :=
  ![![0, 0], ![4, 0], ![0, 4], ![2, 0], ![0, 2], ![2, 2],
    ![-28, 16], ![2, 6], ![5, 5], ![-7, 9]]

private theorem model_injective : Function.Injective model := by decide

private def lines : Fin 8 → Line :=
  ![⟨1, 0, 0⟩, ⟨0, 0, 0⟩, ⟨1, -1, 4⟩, ⟨1, -1 / 2, 2⟩,
    ⟨0, 0, 2⟩, ⟨1, 1, 0⟩, ⟨1, -1, 2⟩, ⟨1, -1 / 3, 20 / 3⟩]

private def pointWeight : Fin 10 → ℕ :=
  ![80, 81, 63, 84, 102, 101, 62, 60, 64, 59]

private def lineWeight : Fin 8 → ℕ :=
  ![14, 30, 33, 34, 32, 36, 38, 28]

private def pointsOn (j : Fin 8) : Finset (Fin 10) :=
  univ.filter fun i => (lines j).Contains (model i)

private theorem sum_pointWeight : ∑ i, pointWeight i = 756 := by decide

private theorem sum_lineWeight : ∑ j, lineWeight j = 245 := by decide

private theorem pointWeight_le : ∀ i : Fin 10,
    pointWeight i ≤ ∑ j : Fin 8, if (lines j).Contains (model i) then lineWeight j else 0 := by
  decide +kernel

private theorem line_pointWeight : ∀ j : Fin 8, ∑ i ∈ pointsOn j, pointWeight i = 245 := by
  decide +kernel

/-- Each line factor contributes one degree and exactly 245 units of weighted
multiplicity. Once no selected line divides the polynomial, the weighted sum
of the restriction inequalities bounds its multiplicities. -/
private theorem model_weighted_bound (f : PlanePolynomial) (hf : f ≠ 0) :
    ∑ i, pointWeight i * multiplicity f (fun j => (model i j : ℂ)) ≤ 245 * f.totalDegree := by
  classical
  induction hd : f.totalDegree using Nat.strong_induction_on generalizing f with
  | ind d ih =>
    by_cases hdiv : ∃ j, (lines j).equation ∣ f
    · obtain ⟨j, g, rfl⟩ := hdiv
      have hg : g ≠ 0 := fun h => hf (by simp [h])
      have hdg : 1 + g.totalDegree = d := by
        rw [← hd, totalDegree_mul_of_isDomain (lines j).ne_zero hg, (lines j).degree]
      have hsmall := ih g.totalDegree (by omega) g hg rfl
      have hline : ∑ i, pointWeight i *
          multiplicity (lines j).equation (fun k => (model i k : ℂ)) = 245 := by
        simpa only [(lines j).multiplicity_eq, pointsOn, Finset.sum_filter, mul_ite, mul_one,
          mul_zero] using line_pointWeight j
      simp_rw [multiplicity_mul (lines j).ne_zero hg, Nat.mul_add, Finset.sum_add_distrib]
      omega
    · let m (i : Fin 10) := multiplicity f (fun k => (model i k : ℂ))
      have hintersect (j : Fin 8) : ∑ i ∈ pointsOn j, m i ≤ d :=
        hd ▸ (lines j).sum_multiplicity_le f (fun h => hdiv ⟨j, h⟩) model (pointsOn j)
          (fun _ hi => (Finset.mem_filter.mp hi).2) (model_injective.comp Subtype.val_injective)
      calc
        ∑ i, pointWeight i * m i ≤
            ∑ i : Fin 10, (∑ j : Fin 8, if (lines j).Contains (model i)
              then lineWeight j else 0) * m i :=
          Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_right _ (pointWeight_le i))
        _ = ∑ j, lineWeight j * ∑ i ∈ pointsOn j, m i := by
          simp_rw [Finset.sum_mul, pointsOn, Finset.sum_filter, Finset.mul_sum, mul_ite,
            ite_mul, mul_zero, zero_mul]
          exact Finset.sum_comm
        _ ≤ ∑ j, lineWeight j * d :=
          Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left _ (hintersect j))
        _ = 245 * d := by rw [← Finset.sum_mul, sum_lineWeight]

private abbrev Exponent := Fin 2 →₀ ℕ

private abbrev DegreeLE (d : ℕ) := {e : Exponent // e.degree ≤ d}
private abbrev Jets (m : Fin 10 → ℕ) := Σ i, {e : Exponent // e.degree < m i}

private theorem finite_bounded_exponents (P : Exponent → Prop) (d : ℕ)
    (h : ∀ e, P e → e.degree ≤ d) : Finite {e // P e} := by
  let toFin (e : {e // P e}) (j : Fin 2) : Fin (d + 1) :=
    ⟨e.val j, Nat.lt_succ_of_le ((Finsupp.le_degree j e.val).trans (h e.val e.property))⟩
  apply Finite.of_injective toFin
  intro e e' he
  apply Subtype.ext
  ext j
  exact congrArg Fin.val (congrFun he j)

private noncomputable instance instFintypeDegreeLE (d : ℕ) : Fintype (DegreeLE d) := by
  have := finite_bounded_exponents (fun e => e.degree ≤ d) d (fun _ h => h)
  exact Fintype.ofFinite _

private noncomputable instance instFintypeJets (m : Fin 10 → ℕ) : Fintype (Jets m) := by
  letI (i : Fin 10) : Fintype {e : Exponent // e.degree < m i} := by
    have := finite_bounded_exponents (fun e => e.degree < m i) (m i) (fun _ h => h.le)
    exact Fintype.ofFinite _
  infer_instance

private noncomputable def fromCoeffs {d : ℕ} (v : DegreeLE d → ℂ) : PlanePolynomial :=
  ∑ e, MvPolynomial.monomial e.val (v e)

private theorem fromCoeffs_totalDegree_le {d : ℕ} (v : DegreeLE d → ℂ) :
    (fromCoeffs v).totalDegree ≤ d := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e _
  apply (MvPolynomial.totalDegree_monomial_le _ _).trans
  simpa only [Finsupp.degree_apply, Finsupp.sum, id_eq] using e.property

private theorem coeff_fromCoeffs {d : ℕ} (v : DegreeLE d → ℂ) (e : Exponent) :
    (fromCoeffs v).coeff e = if h : e.degree ≤ d then v ⟨e, h⟩ else 0 := by
  classical
  rw [fromCoeffs, coeff_sum]
  simp_rw [coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨e, h⟩ : DegreeLE d)]
    · simp
    · intro k _ hk
      have hne : k.val ≠ e := fun he => hk (Subtype.ext he)
      simp [hne]
    · simp
  · apply Finset.sum_eq_zero
    intro k _
    have hne : k.val ≠ e := fun he => h (he ▸ k.property)
    simp [hne]

private theorem fromCoeffs_injective (d : ℕ) :
    Function.Injective (fromCoeffs (d := d)) := by
  intro v w h
  funext e
  simpa only [coeff_fromCoeffs, dite_eq_left e.property] using
    congrArg (fun f : PlanePolynomial => f.coeff e.val) h

private theorem fromCoeffs_coeff {f : PlanePolynomial} {d : ℕ} (hf : f.totalDegree ≤ d) :
    fromCoeffs (d := d) (fun e => f.coeff e.val) = f := by
  ext e
  rw [coeff_fromCoeffs]
  split_ifs with h
  · rfl
  · exact (coeff_eq_zero_of_totalDegree_lt (hf.trans_lt (Nat.lt_of_not_ge h))).symm

private abbrev Coordinate := Fin 10 × Fin 2
private abbrev CoordinateRing := MvPolynomial Coordinate ℚ

private noncomputable def jetMatrix (d : ℕ) (m : Fin 10 → ℕ) :
    Matrix (Jets m) (DegreeLE d) CoordinateRing :=
  fun e a =>
    ((aeval (fun j : Fin 2 => X j + C (X (e.1, j))))
      (monomial a.val (1 : CoordinateRing))).coeff e.2.val

private noncomputable def evaluatedJets (x : Fin 10 → AffinePoint) (d : ℕ) (m : Fin 10 → ℕ) :
    Matrix (Jets m) (DegreeLE d) ℂ :=
  (jetMatrix d m).map (aeval fun ij : Coordinate => x ij.1 ij.2)

private theorem evaluatedJets_apply (x : Fin 10 → AffinePoint) (d : ℕ) (m : Fin 10 → ℕ)
    (e : Jets m) (a : DegreeLE d) :
    evaluatedJets x d m e a =
      (shifted (monomial a.val (1 : ℂ)) (x e.1)).coeff e.2.val := by
  let ev : CoordinateRing →ₐ[ℚ] ℂ := aeval fun ij => x ij.1 ij.2
  let P : MvPolynomial (Fin 2) CoordinateRing :=
    aeval (fun j : Fin 2 => X j + C (X (e.1, j))) (monomial a.val (1 : CoordinateRing))
  have hev (j : Fin 2) : ev.toRingHom (X (e.1, j)) = x e.1 j := aeval_X _ _
  change ev (P.coeff e.2.val) = _
  calc
    _ = (MvPolynomial.map ev.toRingHom P).coeff e.2.val :=
      (MvPolynomial.coeff_map ev.toRingHom P e.2.val).symm
    _ = _ := by
      congr 1
      simp only [P, shifted, aeval_monomial, map_one, one_mul, Finsupp.prod,
        map_prod, map_pow, map_add, map_X, map_C, hev]

private theorem evaluatedJets_mulVec (x : Fin 10 → AffinePoint) (d : ℕ) (m : Fin 10 → ℕ)
    (v : DegreeLE d → ℂ) (e : Jets m) :
    (evaluatedJets x d m *ᵥ v) e = (shifted (fromCoeffs v) (x e.1)).coeff e.2.val := by
  classical
  simp only [Matrix.mulVec, dotProduct, evaluatedJets_apply, fromCoeffs, shifted, map_sum,
    coeff_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [show (monomial a.val (v a) : PlanePolynomial) =
      C (v a) * monomial a.val 1 by simp [C_mul_monomial]]
  rw [map_mul, aeval_C, algebraMap_eq, coeff_C_mul, mul_comm]

private theorem exists_generic_points : ∃ x : Fin 10 → AffinePoint,
    AlgebraicIndependent ℚ (fun ij : Coordinate => x ij.1 ij.2) := by
  obtain ⟨ι, z, hz⟩ := exists_isTranscendenceBasis' ℚ ℂ
  have hcard := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' z hz
    (Cardinal.mk_le_aleph0_iff.mpr inferInstance)
    (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)
  have hι : Infinite ι := Cardinal.infinite_iff.mpr
    (by rw [← hcard, Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum.le)
  let k : Coordinate ↪ ι :=
    ((Fintype.equivFin Coordinate).toEmbedding.trans Fin.valEmbedding).trans
      (Infinite.natEmbedding ι)
  exact ⟨fun i j => z (k (i, j)), hz.1.comp k k.injective⟩

open scoped ComplexOrder in
/-- A nonzero polynomial satisfying given multiplicities at algebraically independent
coordinates specializes to a nonzero polynomial of at most the same degree at rational points.
The kernel dimension can only increase under specialization. -/
private theorem specialize (x : Fin 10 → AffinePoint)
    (hx : AlgebraicIndependent ℚ (fun ij : Coordinate => x ij.1 ij.2))
    (y : Fin 10 → Fin 2 → ℚ) {f : PlanePolynomial} (hf : f ≠ 0) :
    ∃ g : PlanePolynomial, g ≠ 0 ∧ g.totalDegree ≤ f.totalDegree ∧
      ∀ i, multiplicity f (x i) ≤ multiplicity g (fun j => (y i j : ℂ)) := by
  classical
  let d := f.totalDegree
  let m i := multiplicity f (x i)
  let v (a : DegreeLE d) := f.coeff a.val
  let A := jetMatrix d m
  let B := evaluatedJets x d m
  let C' := evaluatedJets (fun i j => (y i j : ℂ)) d m
  have hv : v ≠ 0 := by
    intro h
    apply hf
    have heq : fromCoeffs v = f := fromCoeffs_coeff le_rfl
    rw [h] at heq
    simpa [fromCoeffs] using heq.symm
  have hBv : B *ᵥ v = 0 := by
    funext e
    rw [evaluatedJets_mulVec, fromCoeffs_coeff (f := f) le_rfl]
    exact coeff_shifted_eq_zero_of_lt e.2.property
  have hCstar : C'ᴴ = C'ᵀ := by
    let ev : CoordinateRing →+* ℚ := eval (fun ij => y ij.1 ij.2)
    have h : (aeval (R := ℚ) (fun ij : Coordinate => (y ij.1 ij.2 : ℂ))).toRingHom =
        (algebraMap ℚ ℂ).comp ev := by
      ext <;> simp [ev]
    ext e a
    change star ((aeval fun ij : Coordinate => (y ij.1 ij.2 : ℂ)).toRingHom (A a e)) =
      (aeval fun ij : Coordinate => (y ij.1 ij.2 : ℂ)).toRingHom (A a e)
    rw [h]
    exact star_ratCast _
  have hnot : ¬ Function.Injective C'.mulVec := by
    intro hinj
    have hgram : Function.Injective (C'ᵀ * C').mulVec := by
      rw [← hCstar]
      intro u w huw
      have hs : (C'ᴴ * C') *ᵥ (u - w) = 0 := by rw [Matrix.mulVec_sub, huw, sub_self]
      have he := (Matrix.conjTranspose_mul_self_mulVec_eq_zero C' (u - w)).mp hs
      exact sub_eq_zero.mp (hinj (he.trans (Matrix.mulVec_zero _).symm))
    have hCd : (C'ᵀ * C').det ≠ 0 :=
      isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
        (Matrix.mulVec_injective_iff_isUnit.mp hgram))
    have hdet (ev : CoordinateRing →ₐ[ℚ] ℂ) :
        ev (Aᵀ * A).det = ((A.map ev)ᵀ * A.map ev).det := by
      rw [ev.map_det]
      change ((Aᵀ * A).map ev).det = _
      rw [Matrix.map_mul]
      rfl
    have hAd : (Aᵀ * A).det ≠ 0 := by
      intro ha
      apply hCd
      calc
        _ = (aeval fun ij : Coordinate => (y ij.1 ij.2 : ℂ)) (Aᵀ * A).det :=
          (hdet _).symm
        _ = 0 := by rw [ha, map_zero]
    have hBd : (Bᵀ * B).det ≠ 0 := by
      intro h
      have hev : (aeval fun ij : Coordinate => x ij.1 ij.2) (Aᵀ * A).det = 0 :=
        (hdet _).trans h
      exact hAd (hx (hev.trans (map_zero _).symm))
    have hBinj := Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hBd))
    apply hv
    apply hBinj
    simp [← Matrix.mulVec_mulVec, hBv]
  obtain ⟨u, w, huw, hne⟩ := Function.not_injective_iff.mp hnot
  let z := u - w
  have hz : z ≠ 0 := sub_ne_zero.mpr hne
  have hCz : C' *ᵥ z = 0 := by rw [Matrix.mulVec_sub, huw, sub_self]
  have hzP : fromCoeffs z ≠ 0 := by
    intro h
    apply hz
    apply fromCoeffs_injective d
    simpa [fromCoeffs] using h
  refine ⟨fromCoeffs z, hzP, fromCoeffs_totalDegree_le z, fun i => ?_⟩
  apply multiplicity_ge_of_coeff_shifted_eq_zero hzP
  intro e he
  let row : Jets m := ⟨i, e, he⟩
  have hrow := congrFun hCz row
  change (evaluatedJets (fun i j => (y i j : ℂ)) d m *ᵥ z) row = 0 at hrow
  rw [evaluatedJets_mulVec] at hrow
  exact hrow

private theorem generic_degree_bound (x : Fin 10 → AffinePoint)
    (hx : AlgebraicIndependent ℚ (fun ij : Coordinate => x ij.1 ij.2))
    {f : PlanePolynomial} (hf : f ≠ 0) :
    4 * ∑ i, multiplicity f (x i) ≤ 13 * f.totalDegree := by
  classical
  let m (i : Fin 10) := multiplicity f (x i)
  have hweighted (j : Fin 10) :
      ∑ i, pointWeight i * m (i + j) ≤ 245 * f.totalDegree := by
    let perm := (Equiv.addRight j).prodCongr (Equiv.refl (Fin 2))
    obtain ⟨g, hg, hd, hm⟩ := specialize (fun i => x (i + j))
      (hx.comp perm perm.injective) model hf
    calc
      ∑ i, pointWeight i * m (i + j) ≤
          ∑ i, pointWeight i * multiplicity g (fun k => (model i k : ℂ)) :=
        Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (hm i))
      _ ≤ 245 * g.totalDegree := model_weighted_bound g hg
      _ ≤ 245 * f.totalDegree := Nat.mul_le_mul_left _ hd
  have hsum (i : Fin 10) : ∑ j, m (i + j) = ∑ j, m j :=
    Fintype.sum_equiv (Equiv.addLeft i) _ _ fun _ => rfl
  -- In the sum over rotations each multiplicity receives every point weight once.
  have htotal : 756 * ∑ i, m i ≤ 2450 * f.totalDegree := by
    calc
      756 * ∑ i, m i = ∑ i, pointWeight i * ∑ j, m (i + j) := by
        simp only [hsum, ← Finset.sum_mul, sum_pointWeight]
      _ = ∑ j, ∑ i, pointWeight i * m (i + j) := by
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
      _ ≤ ∑ _j : Fin 10, 245 * f.totalDegree :=
        Finset.sum_le_sum (fun j _ => hweighted j)
      _ = 2450 * f.totalDegree := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← mul_assoc]
        rfl
  change 4 * ∑ i, m i ≤ 13 * f.totalDegree
  omega

private theorem seshadriRatios_nonempty (x : Fin 10 → AffinePoint) :
    (seshadriRatios x).Nonempty := by
  let f : PlanePolynomial := X 0 - C (x 0 0)
  have hf : f ≠ 0 := by
    intro h
    have hs : shifted f (x 0) = X 0 := shifted_X_sub_C (x 0)
    simp only [h, shifted, map_zero] at hs
    exact X_ne_zero 0 hs.symm
  have hm : multiplicity f (x 0) = 1 := multiplicity_X_sub_C (x 0)
  have hsum : 0 < ∑ i, multiplicity f (x i) := by
    have h := Finset.single_le_sum (fun i _ => Nat.zero_le (multiplicity f (x i)))
      (Finset.mem_univ (0 : Fin 10))
    omega
  exact ⟨_, f, hf, hsum, rfl⟩

end Eckl2008

open MathlibExt.AlgebraicGeometry.SeshadriConstant Eckl2008

/-- **Eckl's 2008 lower bound for the ten-point Seshadri constant.**
The generic ten-point Seshadri constant of $\mathbb{P}^2$, in the affine-chart model, is at least
$4/13$.

Source: Eckl (2008), asymptotic Dumnicki method, catalogue lower bound `4/13`. -/
public theorem eckl2008LowerBound_wanted :
    (4 / 13 : ℝ) ≤ seshadriConstant10 := by
  obtain ⟨x, hx⟩ := exists_generic_points
  have hinj : Function.Injective x := by
    intro i j hij
    exact congrArg Prod.fst (hx.injective (a₁ := (i, 0)) (a₂ := (j, 0)) (congrFun hij 0))
  have hbound : (4 / 13 : ℝ) ≤ affineSeshadriConstant x := by
    apply le_csInf (seshadriRatios_nonempty x)
    rintro _ ⟨f, hf, hs, rfl⟩
    apply (le_div_iff₀ (by exact_mod_cast hs)).2
    have hreal : (4 : ℝ) * ((∑ i, multiplicity f (x i) : ℕ) : ℝ) ≤
        13 * (f.totalDegree : ℝ) := by
      exact_mod_cast generic_degree_bound x hx hf
    linarith
  exact hbound.trans (le_csSup bddAbove_genericSeshadriSet ⟨x, hinj, rfl⟩)

end MathlibExt.AlgebraicGeometry.SeshadriConstantWanted
