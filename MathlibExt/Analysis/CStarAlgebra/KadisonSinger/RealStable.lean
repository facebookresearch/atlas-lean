/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.CStarAlgebra.KadisonSinger.MixedCharPoly
public import MathlibExt.Algebra.MvPolynomial.Stable
public import Mathlib.Analysis.Matrix.Order

import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Data.List.OfFn
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Real stable multivariate polynomials

This file develops the real-stability facts used in the Marcus--Spielman--Srivastava proof.
-/

@[expose] public section

open scoped BigOperators ComplexOrder

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

open Filter MvPolynomial

private noncomputable def ksPolynomialIn {σ R : Type*} [CommRing R]
    (i : σ) [DecidableEq σ] (p : MvPolynomial σ R) :
    Polynomial (MvPolynomial {j : σ // j ≠ i} R) :=
  optionEquivLeft R {j : σ // j ≠ i} (rename (Equiv.optionSubtypeNe i).symm p)

private lemma ksUnivariateSpecialization_eq_map_polynomialIn
    {σ R : Type*} [CommRing R] (i : σ) [DecidableEq σ]
    (a : σ → R) (p : MvPolynomial σ R) :
    univariateSpecialization i a p =
      Polynomial.map (eval (fun j : {j : σ // j ≠ i} ↦ a j)) (ksPolynomialIn i p) := by
  unfold univariateSpecialization ksPolynomialIn
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
      simpa only [map_add, Polynomial.map_add] using congrArg₂ (fun x y ↦ x + y) hp hq
  | mul_X p j hp =>
      by_cases hji : j = i
      · subst j
        simp only [map_mul]
        rw [hp]
        simp
      · simp only [map_mul]
        rw [hp]
        simp [hji]

/-- **Stability of the determinant polynomial.** For every finite family $A_1, \dots, A_m$ of
positive semidefinite complex square matrices whose rows and columns are indexed by a finite set
$d$, the polynomial $\det\left(x I + \sum_{i=1}^m z_i A_i\right)$ in the variables
$x, z_1, \dots, z_m$, where $I$ is the identity matrix, is stable. -/
public theorem mixedDetPolynomial_isStable_of_posSemidef
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (A : Fin m → Matrix d d ℂ) (hA : ∀ i, (A i).PosSemidef) :
    (mixedDetPolynomial A).IsStable := by
  intro z hz hzero
  rw [eval_mixedDetPolynomial] at hzero
  let M : Matrix d d ℂ :=
    Matrix.scalar d (z (Sum.inl ())) + ∑ i, z (Sum.inr i) • A i
  obtain ⟨w, hwne, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hzero
  have hdot : dotProduct (star w) (Matrix.mulVec M w) = 0 := by
    rw [show Matrix.mulVec M w = 0 by exact hw, dotProduct_zero]
  have hMmul : Matrix.mulVec M w =
      z (Sum.inl ()) • w + ∑ i, z (Sum.inr i) • Matrix.mulVec (A i) w := by
    ext j
    simp [M, Matrix.add_mulVec, Matrix.sum_mulVec, Matrix.scalar,
      Matrix.smul_mulVec, Matrix.mulVec_diagonal]
  rw [hMmul, dotProduct_add, dotProduct_sum] at hdot
  simp only [dotProduct_smul] at hdot
  have hself : 0 < dotProduct (star w) w := Matrix.dotProduct_star_self_pos_iff.mpr hwne
  have hself_re : 0 < (dotProduct (star w) w).re := (RCLike.pos_iff.mp hself).1
  have hself_im : (dotProduct (star w) w).im = 0 := (RCLike.pos_iff.mp hself).2
  have hquad (i : Fin m) : 0 ≤ dotProduct (star w) (Matrix.mulVec (A i) w) :=
    (hA i).dotProduct_mulVec_nonneg w
  have hquad_re (i : Fin m) : 0 ≤ (dotProduct (star w) (Matrix.mulVec (A i) w)).re :=
    (RCLike.nonneg_iff.mp (hquad i)).1
  have hquad_im (i : Fin m) : (dotProduct (star w) (Matrix.mulVec (A i) w)).im = 0 :=
    (RCLike.nonneg_iff.mp (hquad i)).2
  have him := congrArg Complex.im hdot
  simp only [smul_eq_mul, Complex.add_im, Complex.im_sum, Complex.mul_im, hself_im,
    hquad_im, mul_zero, zero_add, Complex.zero_im] at him
  have hfirst : 0 < (z (Sum.inl ())).im * (dotProduct (star w) w).re :=
    mul_pos (hz (Sum.inl ())) hself_re
  have hsum : 0 ≤ ∑ i, (z (Sum.inr i)).im *
      (dotProduct (star w) (Matrix.mulVec (A i) w)).re := by
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (le_of_lt (hz (Sum.inr i))) (hquad_re i)
  nlinarith

private lemma ksMap_star_mixedDetPolynomial_of_isHermitian
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (A : Fin m → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) :
    MvPolynomial.map (starRingEnd ℂ) (mixedDetPolynomial A) = mixedDetPolynomial A := by
  let B : Matrix d d (MvPolynomial (Unit ⊕ Fin m) ℂ) :=
    Matrix.scalar d (X (Sum.inl ())) +
      ∑ i, (X (Sum.inr i) : MvPolynomial (Unit ⊕ Fin m) ℂ) •
        (A i).map (C : ℂ → MvPolynomial (Unit ⊕ Fin m) ℂ)
  change MvPolynomial.map (starRingEnd ℂ) (Matrix.det B) = Matrix.det B
  rw [RingHom.map_det]
  have hmatrix : (MvPolynomial.map (starRingEnd ℂ)).mapMatrix B = B.transpose := by
    apply Matrix.ext
    intro j k
    simp only [Matrix.add_apply, Matrix.map_apply, map_add, Matrix.sum_apply, map_sum,
      Matrix.smul_apply, Matrix.transpose_apply, B]
    congr 1
    · by_cases hjk : j = k
      · subst k
        simp [Matrix.scalar_apply]
      · simp [Matrix.scalar_apply, hjk, Ne.symm hjk]
    · apply Finset.sum_congr rfl
      intro i hi
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
        map_mul, MvPolynomial.map_X, MvPolynomial.map_C]
      congr 1
      apply congrArg C
      simpa [Matrix.conjTranspose_apply] using congrFun (congrFun (hA i).eq k) j
  rw [hmatrix, Matrix.det_transpose]

/-- **Real stability of the determinant polynomial.** For every finite family $A_1, \dots, A_m$ of
positive semidefinite complex square matrices whose rows and columns are indexed by a finite set
$d$, the polynomial $\det\left(x I + \sum_{i=1}^m z_i A_i\right)$ in the variables
$x, z_1, \dots, z_m$, where $I$ is the identity matrix, is real stable. -/
public theorem mixedDetPolynomial_isRealStable_of_posSemidef
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (A : Fin m → Matrix d d ℂ) (hA : ∀ i, (A i).PosSemidef) :
    (mixedDetPolynomial A).IsRealStable := by
  exact ⟨ksMap_star_mixedDetPolynomial_of_isHermitian A (fun i ↦ (hA i).1),
    mixedDetPolynomial_isStable_of_posSemidef A hA⟩

private lemma ksDegreeOf_pderiv_le_of_ne {σ R : Type*} [CommRing R]
    (p : MvPolynomial σ R) {i j : σ} (hij : i ≠ j) :
    (pderiv j p).degreeOf i ≤ p.degreeOf i := by
  rw [degreeOf_le_iff]
  intro s hs
  have hcoeff : p.coeff (s + Finsupp.single j 1) ≠ 0 := by
    rw [mem_support_iff, coeff_pderiv] at hs
    intro hp
    rw [hp, zero_mul] at hs
    exact hs rfl
  have hmem : s + Finsupp.single j 1 ∈ p.support := by
    rwa [mem_support_iff]
  have hle := monomial_le_degreeOf i hmem
  simpa [Finsupp.single_apply, hij] using hle

private lemma ksPolynomialIn_mixedDetPolynomial
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (A : Fin m → Matrix d d ℂ) :
    ksPolynomialIn (Sum.inl ()) (mixedDetPolynomial A) =
      Matrix.charpoly
        (-(∑ i, (X (⟨Sum.inr i, by simp⟩ : {j : Unit ⊕ Fin m // j ≠ Sum.inl ()}) :
            MvPolynomial {j : Unit ⊕ Fin m // j ≠ Sum.inl ()} ℂ) •
          (A i).map (C : ℂ →
            MvPolynomial {j : Unit ⊕ Fin m // j ≠ Sum.inl ()} ℂ))) := by
  let B : Matrix d d (MvPolynomial {j : Unit ⊕ Fin m // j ≠ Sum.inl ()} ℂ) :=
    ∑ i, (X (⟨Sum.inr i, by simp⟩ : {j : Unit ⊕ Fin m // j ≠ Sum.inl ()}) :
        MvPolynomial {j : Unit ⊕ Fin m // j ≠ Sum.inl ()} ℂ) •
      (A i).map (C : ℂ → MvPolynomial {j : Unit ⊕ Fin m // j ≠ Sum.inl ()} ℂ)
  change ksPolynomialIn (Sum.inl ())
      (Matrix.det (Matrix.scalar d (X (Sum.inl ())) +
        ∑ i, X (Sum.inr i) • (A i).map C)) = Matrix.charpoly (-B)
  rw [show ksPolynomialIn (Sum.inl ())
      (Matrix.det (Matrix.scalar d (X (Sum.inl ())) +
        ∑ i, X (Sum.inr i) • (A i).map C)) =
      Matrix.det ((Matrix.scalar d Polynomial.X + B.map Polynomial.C)) by
    unfold ksPolynomialIn
    let M : Matrix d d (MvPolynomial (Unit ⊕ Fin m) ℂ) :=
      Matrix.scalar d (X (Sum.inl ()) : MvPolynomial (Unit ⊕ Fin m) ℂ) +
        ∑ i, (X (Sum.inr i) : MvPolynomial (Unit ⊕ Fin m) ℂ) •
          (A i).map (C : ℂ → MvPolynomial (Unit ⊕ Fin m) ℂ)
    let ρ : MvPolynomial (Unit ⊕ Fin m) ℂ →+*
        MvPolynomial (Option {j : Unit ⊕ Fin m // j ≠ Sum.inl ()}) ℂ :=
      (rename (R := ℂ) (Equiv.optionSubtypeNe (Sum.inl () : Unit ⊕ Fin m)).symm).toRingHom
    let φ : MvPolynomial (Option {j : Unit ⊕ Fin m // j ≠ Sum.inl ()}) ℂ →+*
        Polynomial (MvPolynomial {j : Unit ⊕ Fin m // j ≠ Sum.inl ()} ℂ) :=
      (optionEquivLeft ℂ {j : Unit ⊕ Fin m // j ≠ Sum.inl ()}).toRingEquiv.toRingHom
    change φ (ρ (Matrix.det M)) = _
    rw [RingHom.map_det ρ M]
    rw [RingHom.map_det φ]
    have hparam (j k : d) :
        ksPolynomialIn (Sum.inl ())
            ((∑ i, (X (Sum.inr i) : MvPolynomial (Unit ⊕ Fin m) ℂ) •
              (A i).map (C : ℂ → MvPolynomial (Unit ⊕ Fin m) ℂ)) j k) =
          Polynomial.C (B j k) := by
      simp [ksPolynomialIn, B, Matrix.sum_apply, Matrix.smul_apply]
    apply congrArg Matrix.det
    apply Matrix.ext
    intro j k
    change ksPolynomialIn (Sum.inl ()) (M j k) =
      Matrix.diagonal (fun _ ↦ Polynomial.X) j k + Polynomial.C (B j k)
    rw [show M j k =
        Matrix.scalar d (X (Sum.inl ()) : MvPolynomial (Unit ⊕ Fin m) ℂ) j k +
          (∑ i, (X (Sum.inr i) : MvPolynomial (Unit ⊕ Fin m) ℂ) •
            (A i).map (C : ℂ → MvPolynomial (Unit ⊕ Fin m) ℂ)) j k by rfl]
    rw [show ksPolynomialIn (Sum.inl ())
        (Matrix.scalar d (X (Sum.inl ()) : MvPolynomial (Unit ⊕ Fin m) ℂ) j k +
          (∑ i, (X (Sum.inr i) : MvPolynomial (Unit ⊕ Fin m) ℂ) •
            (A i).map (C : ℂ → MvPolynomial (Unit ⊕ Fin m) ℂ)) j k) =
        ksPolynomialIn (Sum.inl ())
            (Matrix.scalar d (X (Sum.inl ()) : MvPolynomial (Unit ⊕ Fin m) ℂ) j k) +
          ksPolynomialIn (Sum.inl ())
            ((∑ i, (X (Sum.inr i) : MvPolynomial (Unit ⊕ Fin m) ℂ) •
              (A i).map (C : ℂ → MvPolynomial (Unit ⊕ Fin m) ℂ)) j k) by
      simp [ksPolynomialIn], hparam]
    by_cases hjk : j = k
    · subst k
      simp [Matrix.scalar_apply, ksPolynomialIn]
    · simp [Matrix.scalar_apply, ksPolynomialIn, hjk]]
  have hneg : -(-B).map Polynomial.C = B.map Polynomial.C := by
    ext j k
    simp
  simp [Matrix.charpoly, Matrix.charmatrix, sub_eq_add_neg, hneg]

private def ksMonicIn {σ R : Type*} [CommRing R]
    (i : σ) (d : ℕ) (p : MvPolynomial σ R) : Prop :=
  ∃ q, p = X i ^ d + q ∧ q.degreeOf i < d

private lemma ksMonicIn_of_polynomialIn {σ R : Type*} [CommRing R]
    (i : σ) [DecidableEq σ] (d : ℕ) (hd : d ≠ 0) (p : MvPolynomial σ R)
    (hp : Polynomial.IsMonicOfDegree (ksPolynomialIn i p) d) : ksMonicIn i d p := by
  refine ⟨p - X i ^ d, by ring, ?_⟩
  rw [degreeOf_eq_natDegree i (p - X i ^ d)]
  change (ksPolynomialIn i (p - X i ^ d)).natDegree < d
  have hsplit : ksPolynomialIn i (p - X i ^ d) =
      ksPolynomialIn i p - Polynomial.X ^ d := by
    simp [ksPolynomialIn]
  rw [hsplit]
  exact hp.natDegree_sub_X_pow hd

private lemma ksMonicIn_sub_pderiv {σ R : Type*} [CommRing R]
    {i j : σ} {d : ℕ} {p : MvPolynomial σ R}
    (hp : ksMonicIn i d p) (hij : i ≠ j) : ksMonicIn i d (p - pderiv j p) := by
  obtain ⟨q, hpq, hq⟩ := hp
  refine ⟨q - pderiv j q, ?_, ?_⟩
  · rw [hpq, map_add]
    have hderiv : pderiv j (X i ^ d : MvPolynomial σ R) = 0 := by
      rw [pderiv_pow]
      simp [pderiv_X_of_ne hij]
    rw [hderiv, zero_add]
    ring
  · refine (degreeOf_sub_le i q (pderiv j q)).trans_lt ?_
    exact max_lt hq ((ksDegreeOf_pderiv_le_of_ne q hij).trans_lt hq)

private lemma ksMonicIn_mixedDifferential {σ R : Type*} [CommRing R]
    {i : σ} {d : ℕ} {p : MvPolynomial σ R}
    (hp : ksMonicIn i d p) (indices : List σ) (hindices : ∀ j ∈ indices, i ≠ j) :
    ksMonicIn i d (mixedDifferential indices p) := by
  induction indices generalizing p with
  | nil => simpa [mixedDifferential]
  | cons j js ih =>
      rw [mixedDifferential_cons]
      apply ih (ksMonicIn_sub_pderiv hp (hindices j (by simp)))
      intro k hk
      exact hindices k (by simp [hk])

private lemma ksMonicIn_specialization {σ R : Type*} [CommRing R] [Nontrivial R]
    {i : σ} [DecidableEq σ] {d : ℕ} {p : MvPolynomial σ R}
    (hp : ksMonicIn i d p) (a : σ → R) :
    Polynomial.IsMonicOfDegree (univariateSpecialization i a p) d := by
  obtain ⟨q, hpq, hq⟩ := hp
  rw [hpq]
  have hqspec : (univariateSpecialization i a q).natDegree < d :=
    (show (univariateSpecialization i a q).natDegree ≤ q.degreeOf i from by
      rw [ksUnivariateSpecialization_eq_map_polynomialIn]
      exact Polynomial.natDegree_map_le.trans_eq (degreeOf_eq_natDegree i q).symm).trans_lt hq
  simpa [univariateSpecialization] using
    (Polynomial.isMonicOfDegree_X_pow R d).add_right hqspec

private lemma ksMixedCharacteristicPolynomial_eq_one_of_card_eq_zero
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (A : Fin m → Matrix d d ℂ) (hd : Fintype.card d = 0) :
    mixedCharacteristicPolynomial A = 1 := by
  have hdet : mixedDetPolynomial A = 1 := by
    unfold mixedDetPolynomial
    rw [Matrix.det_eq_one_of_card_eq_zero hd]
  have hmixed (is : List (Unit ⊕ Fin m)) :
      mixedDifferential is (1 : MvPolynomial _ ℂ) = 1 := by
    induction is with
    | nil => rfl
    | cons i is ih =>
        rw [mixedDifferential_cons]
        simp [ih]
  unfold mixedCharacteristicPolynomial
  rw [hdet, hmixed]
  simp

private lemma ksMixedDifferential_monicIn
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (A : Fin m → Matrix d d ℂ) (hd : Fintype.card d ≠ 0) :
    ksMonicIn (Sum.inl ()) (Fintype.card d)
      (mixedDifferential ((List.finRange m).map Sum.inr) (mixedDetPolynomial A)) := by
  have hraw : Polynomial.IsMonicOfDegree
      (ksPolynomialIn (Sum.inl ()) (mixedDetPolynomial A)) (Fintype.card d) := by
    rw [ksPolynomialIn_mixedDetPolynomial]
    exact ⟨Matrix.charpoly_natDegree_eq_dim _, Matrix.charpoly_monic _⟩
  apply ksMonicIn_mixedDifferential
    (ksMonicIn_of_polynomialIn (Sum.inl ()) (Fintype.card d) hd
      (mixedDetPolynomial A) hraw)
  intro j hj
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
  exact Sum.inl_ne_inr

private lemma ksMixedCharacteristicPolynomial_eq_specialization
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (A : Fin m → Matrix d d ℂ) :
    mixedCharacteristicPolynomial A =
      univariateSpecialization (Sum.inl ()) (fun _ ↦ 0)
        (mixedDifferential ((List.finRange m).map Sum.inr) (mixedDetPolynomial A)) := by
  unfold mixedCharacteristicPolynomial univariateSpecialization
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro j
    rcases j with u | i
    · cases u
      simp
    · simp

private theorem ksMixedCharacteristicPolynomial_isMonicOfDegree
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (A : Fin m → Matrix d d ℂ) :
    Polynomial.IsMonicOfDegree (mixedCharacteristicPolynomial A) (Fintype.card d) := by
  by_cases hd : Fintype.card d = 0
  · rw [ksMixedCharacteristicPolynomial_eq_one_of_card_eq_zero A hd, hd]
    simp
  · rw [ksMixedCharacteristicPolynomial_eq_specialization]
    exact ksMonicIn_specialization (ksMixedDifferential_monicIn A hd) (fun _ ↦ 0)

/-- **Mixed characteristic polynomials are monic.** For every finite family $A_1, \dots, A_m$ of
complex square matrices of a common size, the mixed characteristic polynomial of
$A_1, \dots, A_m$ is monic. -/
public theorem mixedCharacteristicPolynomial_monic
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (A : Fin m → Matrix d d ℂ) : (mixedCharacteristicPolynomial A).Monic :=
  (ksMixedCharacteristicPolynomial_isMonicOfDegree A).monic

/-- **Degree of a mixed characteristic polynomial.** For every finite family $A_1, \dots, A_m$ of
complex square matrices whose rows and columns are indexed by a finite set $d$, the mixed
characteristic polynomial of $A_1, \dots, A_m$ has degree $|d|$, the number of elements of $d$. -/
public theorem mixedCharacteristicPolynomial_natDegree
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (A : Fin m → Matrix d d ℂ) :
    (mixedCharacteristicPolynomial A).natDegree = Fintype.card d :=
  (ksMixedCharacteristicPolynomial_isMonicOfDegree A).natDegree_eq

/-- **Mixed characteristic polynomials of positive semidefinite matrices are real-rooted.** For
every finite family $A_1, \dots, A_m$ of positive semidefinite complex square matrices of a common
size, the mixed characteristic polynomial of $A_1, \dots, A_m$ is real-rooted. -/
public theorem mixedCharacteristicPolynomial_isRealRooted_of_posSemidef
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (A : Fin m → Matrix d d ℂ) (hA : ∀ i, (A i).PosSemidef) :
    (mixedCharacteristicPolynomial A).IsRealRooted := by
  by_cases hd : Fintype.card d = 0
  · rw [ksMixedCharacteristicPolynomial_eq_one_of_card_eq_zero A hd]
    intro z hz
    simp at hz
  · let q := mixedDifferential ((List.finRange m).map Sum.inr) (mixedDetPolynomial A)
    have hmono := ksMixedDifferential_monicIn A hd
    have hstable : q.IsRealStable :=
      MvPolynomial.IsRealStable.mixedDifferential
        (mixedDetPolynomial_isRealStable_of_posSemidef A hA) _
    have hrooted : (univariateSpecialization (Sum.inl ()) (fun _ ↦ 0) q).IsRealRooted :=
      MvPolynomial.isRealRooted_univariateSpecialization_of_isRealStable
        (Sum.inl ()) q hstable
        (Fintype.card d) (fun a ↦ (ksMonicIn_specialization hmono a).monic)
        (fun a ↦ (ksMonicIn_specialization hmono a).natDegree_eq) (fun _ ↦ 0) (by simp)
    rw [ksMixedCharacteristicPolynomial_eq_specialization]
    exact hrooted

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger
