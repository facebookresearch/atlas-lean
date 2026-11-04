/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# Sylvester's law of inertia

This file proves that congruent real symmetric matrices have the same numbers of positive,
negative, and zero eigenvalues.
-/

@[expose] public section

namespace MetaMathlibExt

private theorem sylvesterInertia_toQuadraticForm'_congr
    {n : Type*} [Fintype n] [DecidableEq n] (A P : Matrix n n ℝ) (x : n → ℝ) :
    (P.transpose * A * P).toQuadraticForm' x =
      A.toQuadraticForm' (P.mulVec x) := by
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply']
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

private theorem sylvesterInertia_congr_equivalent
    {n : Type*} [Fintype n] [DecidableEq n] (A P : Matrix n n ℝ)
    (hP : IsUnit P.det) :
    QuadraticMap.Equivalent (P.transpose * A * P).toQuadraticForm'
      A.toQuadraticForm' := by
  refine ⟨QuadraticMap.IsometryEquiv.mk
    (Matrix.toLinearEquiv (Pi.basisFun ℝ n) P hP) ?_⟩
  intro x
  simpa [Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin',
    Matrix.toLin'_apply] using
    (sylvesterInertia_toQuadraticForm'_congr A P x).symm

private theorem sylvesterInertia_spectral_comp
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) :
    A.toQuadraticForm'.comp (Matrix.UnitaryGroup.toLin' hA.eigenvectorUnitary) =
      QuadraticMap.weightedSumSquares ℝ hA.eigenvalues := by
  ext y
  simp only [QuadraticMap.comp_apply, Matrix.UnitaryGroup.toLin',
    Matrix.toLin'_apply, Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply',
    QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
  let U : Matrix n n ℝ := hA.eigenvectorUnitary
  let d : n → ℝ := hA.eigenvalues
  change U.mulVec y ⬝ᵥ A.mulVec (U.mulVec y) =
    ∑ i, d i * (y i * y i)
  have hspec : A = U * Matrix.diagonal d * U.transpose := by
    simpa [U, d, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Function.comp_def] using hA.spectral_theorem
  have hU : U.transpose * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] using
      Matrix.UnitaryGroup.star_mul_self hA.eigenvectorUnitary
  rw [hspec,
    ← Matrix.mulVec_mulVec (U.mulVec y) (U * Matrix.diagonal d) U.transpose,
    Matrix.mulVec_mulVec y U.transpose U, hU, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec y U (Matrix.diagonal d),
    Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec U U y, hU, Matrix.vecMul_one]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem sylvesterInertia_spectral_equivalent
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) :
    QuadraticMap.Equivalent A.toQuadraticForm'
      (QuadraticMap.weightedSumSquares ℝ hA.eigenvalues) := by
  rw [← sylvesterInertia_spectral_comp hA]
  exact ⟨QuadraticMap.isometryEquivOfCompLinearEquiv A.toQuadraticForm'
    (Matrix.UnitaryGroup.toLinearEquiv hA.eigenvectorUnitary)⟩

private theorem sylvesterInertia_ncard_setOf
    {n : Type*} [Fintype n] (p : n → Prop) [DecidablePred p] :
    {i | p i}.ncard = (Finset.univ.filter p).card := by
  simpa using (Set.ncard_coe_finset (Finset.univ.filter p))

private theorem sylvesterInertia_card_signs
    {n : Type*} [Fintype n] (w : n → ℝ) :
    (Finset.univ.filter (fun i => 0 < w i)).card +
        (Finset.univ.filter (fun i => w i < 0)).card +
        (Finset.univ.filter (fun i => w i = 0)).card =
      Fintype.card n := by
  classical
  have hp := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun i => 0 < w i)
  have hn := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun i => ¬ 0 < w i)) (fun i => w i < 0)
  simp only [Finset.filter_filter, not_lt] at hp hn
  have hneg :
      Finset.univ.filter (fun i => w i ≤ 0 ∧ w i < 0) =
        Finset.univ.filter (fun i => w i < 0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact And.right
    · intro hi
      exact ⟨hi.le, hi⟩
  have hzero :
      Finset.univ.filter (fun i => w i ≤ 0 ∧ 0 ≤ w i) =
        Finset.univ.filter (fun i => w i = 0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hi, hi'⟩
      exact le_antisymm hi hi'
    · intro hi
      rw [hi]
      exact ⟨le_rfl, le_rfl⟩
  rw [hneg, hzero] at hn
  simp only [Finset.card_univ] at hp
  omega

/-- **Sylvester's law of inertia.** Let $A$ and $B$ be real symmetric square matrices with rows
and columns indexed by a finite set $n$, and suppose $B = P^{\mathsf T} A P$ for some invertible
real matrix $P$ indexed by $n$. Then $A$ and $B$ have the same number of positive eigenvalues, the
same number of negative eigenvalues and the same number of zero eigenvalues, each counted with
multiplicity.

Proof: By the spectral theorem, the quadratic form of each matrix is a weighted sum of squares
whose weights are its eigenvalues. Congruence gives an equivalence of quadratic forms, and
invariance of the signature fixes the positive and negative counts; the zero count follows by
trichotomy.

Proves `Wanted` entry `sylvester_law_of_inertia`.

Source: J. J. Sylvester, *A demonstration of the theorem that every homogeneous quadratic
polynomial is reducible by real orthogonal substitutions to the form of a sum of positive and
negative squares*, Philosophical Magazine Ser. 4, 4(23) (1852), 138-142; statement
`sylvester-inertia-s1`.
-/
theorem sylvester_law_of_inertia {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (P : Matrix n n ℝ) (hP : IsUnit P.det)
    (hcong : B = P.transpose * A * P) :
    (Finset.univ.filter (fun i => 0 < hA.eigenvalues i)).card =
      (Finset.univ.filter (fun i => 0 < hB.eigenvalues i)).card ∧
    (Finset.univ.filter (fun i => hA.eigenvalues i < 0)).card =
      (Finset.univ.filter (fun i => hB.eigenvalues i < 0)).card ∧
    (Finset.univ.filter (fun i => hA.eigenvalues i = 0)).card =
      (Finset.univ.filter (fun i => hB.eigenvalues i = 0)).card := by
  have hBA : QuadraticMap.Equivalent B.toQuadraticForm' A.toQuadraticForm' := by
    rw [hcong]
    exact sylvesterInertia_congr_equivalent A P hP
  have hPosA := QuadraticForm.sigPos_of_equiv_weightedSumSquares
    (sylvesterInertia_spectral_equivalent hA)
  have hPosB := QuadraticForm.sigPos_of_equiv_weightedSumSquares
    (sylvesterInertia_spectral_equivalent hB)
  have hNegA := QuadraticForm.sigNeg_of_equiv_weightedSumSquares
    (sylvesterInertia_spectral_equivalent hA)
  have hNegB := QuadraticForm.sigNeg_of_equiv_weightedSumSquares
    (sylvesterInertia_spectral_equivalent hB)
  have hPosSet :
      {i | 0 < hA.eigenvalues i}.ncard =
        {i | 0 < hB.eigenvalues i}.ncard := by
    calc
      _ = sigPos A.toQuadraticForm' := hPosA.symm
      _ = sigPos B.toQuadraticForm' := hBA.sigPos_eq.symm
      _ = _ := hPosB
  have hNegSet :
      {i | hA.eigenvalues i < 0}.ncard =
        {i | hB.eigenvalues i < 0}.ncard := by
    calc
      _ = sigNeg A.toQuadraticForm' := hNegA.symm
      _ = sigNeg B.toQuadraticForm' := hBA.sigNeg_eq.symm
      _ = _ := hNegB
  have hPos :
      (Finset.univ.filter (fun i => 0 < hA.eigenvalues i)).card =
        (Finset.univ.filter (fun i => 0 < hB.eigenvalues i)).card := by
    rw [← sylvesterInertia_ncard_setOf, ← sylvesterInertia_ncard_setOf]
    exact hPosSet
  have hNeg :
      (Finset.univ.filter (fun i => hA.eigenvalues i < 0)).card =
        (Finset.univ.filter (fun i => hB.eigenvalues i < 0)).card := by
    rw [← sylvesterInertia_ncard_setOf, ← sylvesterInertia_ncard_setOf]
    exact hNegSet
  refine ⟨hPos, hNeg, ?_⟩
  have hTotalA := sylvesterInertia_card_signs hA.eigenvalues
  have hTotalB := sylvesterInertia_card_signs hB.eigenvalues
  omega

end MetaMathlibExt
