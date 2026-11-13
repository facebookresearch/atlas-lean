/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.KWRectangleCritical










namespace StatMech.Onsager

open Matrix BigOperators
open scoped Matrix.Norms.L2Operator




noncomputable def ons_rectKWmatDartWeighted (M N : Nat)
    (weight : ons_RectDart M N -> Complex) :
    Matrix (ons_RectDart M N) (ons_RectDart M N) Complex :=
  (ons_rectDartMask M N * ons_arrivalTurnMatrixOf (ons_RectVertex M N) *
      (ons_rectTailDartEquiv M N).permMatrix Complex * ons_rectDartMask M N) *
    Matrix.diagonal weight


theorem ons_rectKWmatDartWeighted_const (M N : Nat) (x : Complex) :
    ons_rectKWmatDartWeighted M N (fun _ => x) = ons_rectKWmat M N x := by
  unfold ons_rectKWmatDartWeighted ons_rectKWmat
  ext d2 d1
  rw [Matrix.mul_diagonal]
  simp
  ring



theorem norm_diagonal_rectDartWeight_le (M N : Nat)
    (weight : ons_RectDart M N -> Complex) (q : Real)
    (hq : 0 <= q) (hweight : forall d, ‖weight d‖ <= q) :
    letI : NormedRing
        (Matrix (ons_RectDart M N) (ons_RectDart M N) Complex) :=
      Matrix.instL2OpNormedRing
    ‖Matrix.diagonal weight‖ <= q := by
  letI : NormedRing
      (Matrix (ons_RectDart M N) (ons_RectDart M N) Complex) :=
    Matrix.instL2OpNormedRing
  rw [Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg hq]
  exact hweight



theorem norm_ons_rectKWmatDartWeighted_sharp (M N : Nat)
    (weight : ons_RectDart M N -> Complex) (q : Real)
    (hq : 0 <= q) (hweight : forall d, ‖weight d‖ <= q) :
    letI : NormedRing
        (Matrix (ons_RectDart M N) (ons_RectDart M N) Complex) :=
      Matrix.instL2OpNormedRing
    ‖ons_rectKWmatDartWeighted M N weight‖ <=
      (Real.sqrt 2 + 1) * q := by
  letI : NormedRing
      (Matrix (ons_RectDart M N) (ons_RectDart M N) Complex) :=
    Matrix.instL2OpNormedRing
  let base :=
    ons_rectDartMask M N * ons_arrivalTurnMatrixOf (ons_RectVertex M N) *
      (ons_rectTailDartEquiv M N).permMatrix Complex * ons_rectDartMask M N
  have hbase : ‖base‖ <= Real.sqrt 2 + 1 := by
    simpa [base, ons_rectKWmat] using
      (norm_ons_rectKWmat_sharp M N (1 : Complex))
  rw [ons_rectKWmatDartWeighted]
  calc
    ‖base * Matrix.diagonal weight‖ <=
        ‖base‖ * ‖Matrix.diagonal weight‖ := Matrix.l2_opNorm_mul _ _
    _ <= (Real.sqrt 2 + 1) * q := by
      gcongr
      exact norm_diagonal_rectDartWeight_le M N weight q hq hweight


theorem norm_root_ons_rectKWmatDartWeighted_le (M N : Nat)
    (weight : ons_RectDart M N -> Complex) (q : Real)
    (hq : 0 <= q) (hweight : forall d, ‖weight d‖ <= q)
    (alpha : Complex)
    (halpha : alpha ∈ (ons_rectKWmatDartWeighted M N weight).charpoly.roots) :
    ‖alpha‖ <= (Real.sqrt 2 + 1) * q := by
  letI : NormedRing
      (Matrix (ons_RectDart M N) (ons_RectDart M N) Complex) :=
    Matrix.instL2OpNormedRing
  let A := ons_rectKWmatDartWeighted M N weight
  have hroot : A.charpoly.IsRoot alpha :=
    (Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero).mp halpha
  have heig : Module.End.HasEigenvalue (Matrix.toLin' A) alpha :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly (Matrix.toLin' A) alpha).2 <| by
      rw [Matrix.charpoly_toLin']
      exact hroot
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  let vE : EuclideanSpace Complex (ons_RectDart M N) :=
    (EuclideanSpace.equiv (ons_RectDart M N) Complex).symm v
  have hvE : vE ≠ 0 := by
    intro hzero
    apply hv.2
    apply (EuclideanSpace.equiv (ons_RectDart M N) Complex).symm.injective
    simpa [vE] using hzero
  have heigen :
      (EuclideanSpace.equiv (ons_RectDart M N) Complex).symm (A *ᵥ vE) =
        alpha • vE := by
    apply (EuclideanSpace.equiv (ons_RectDart M N) Complex).injective
    simpa [vE, Matrix.toLin'_apply] using hv.apply_eq_smul
  have hmul : ‖alpha‖ * ‖vE‖ <= ‖A‖ * ‖vE‖ := by
    rw [← norm_smul, ← heigen]
    exact Matrix.l2_opNorm_mulVec A vE
  have halpha_le : ‖alpha‖ <= ‖A‖ :=
    le_of_mul_le_mul_right hmul (norm_pos_iff.mpr hvE)
  exact halpha_le.trans
    (norm_ons_rectKWmatDartWeighted_sharp M N weight q hq hweight)



theorem ons_rectKWmatDartWeighted_spectral
    (M N : Nat) (weight : ons_RectDart M N -> Complex) (q : Real)
    (hq0 : 0 <= q) (hq : q < ons_signedLoopCriticalWeight)
    (hweight : forall d, ‖weight d‖ <= q) :
    ∀ alpha ∈ (ons_rectKWmatDartWeighted M N weight).charpoly.roots,
      ‖alpha‖ < 1 := by
  intro alpha halpha
  refine (norm_root_ons_rectKWmatDartWeighted_le
    M N weight q hq0 hweight alpha halpha).trans_lt ?_
  have hconstant : 0 < Real.sqrt 2 + 1 := by positivity
  have hmul := mul_lt_mul_of_pos_left hq hconstant
  simpa [sqrt_two_add_one_mul_signedLoopCriticalWeight] using hmul



theorem ons_rectKWmatDartWeighted_det_eq_walk_exp
    (M N : Nat) (weight : ons_RectDart M N -> Complex) (q : Real)
    (hq0 : 0 <= q) (hq : q < ons_signedLoopCriticalWeight)
    (hweight : forall d, ‖weight d‖ <= q) :
    (1 - ons_rectKWmatDartWeighted M N weight).det =
      Complex.exp (- ∑' n : Nat,
        (∑ v : Fin (n + 1) -> ons_RectDart M N,
          ∏ k : Fin (n + 1),
            ons_rectKWmatDartWeighted M N weight
              (v k) (v (k + 1))) / (n + 1)) := by
  exact ons_det_eq_walk_exp _
    (ons_rectKWmatDartWeighted_spectral M N weight q hq0 hq hweight)


noncomputable def ons_rectWeightedWalkExponent (M N : Nat)
    (weight : ons_RectDart M N -> Complex) : Complex :=
  ∑' n : Nat,
    (∑ v : Fin (n + 1) -> ons_RectDart M N,
      ∏ k : Fin (n + 1),
        ons_rectKWmatDartWeighted M N weight (v k) (v (k + 1))) /
      (n + 1)




noncomputable def ons_rectDartSignDefect (M N : Nat)
    (defect : ons_RectDart M N -> Prop) [DecidablePred defect]
    (q : Real) (d : ons_RectDart M N) : Complex :=
  if defect d then -(q : Complex) else (q : Complex)

theorem norm_ons_rectDartSignDefect
    (M N : Nat) (defect : ons_RectDart M N -> Prop)
    [DecidablePred defect] {q : Real} (hq : 0 <= q) (d : ons_RectDart M N) :
    ‖ons_rectDartSignDefect M N defect q d‖ = q := by
  unfold ons_rectDartSignDefect
  split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg hq]




theorem ons_rectSignDefect_det_ratio_eq_walk_exp
    (M N : Nat) (defect : ons_RectDart M N -> Prop)
    [DecidablePred defect] (q : Real)
    (hq0 : 0 <= q) (hq : q < ons_signedLoopCriticalWeight) :
    (1 - ons_rectKWmatDartWeighted M N
          (ons_rectDartSignDefect M N defect q)).det /
        (1 - ons_rectKWmat M N (q : Complex)).det =
      Complex.exp
        (-(ons_rectWeightedWalkExponent M N
              (ons_rectDartSignDefect M N defect q) -
            ons_rectWeightedWalkExponent M N (fun _ => (q : Complex)))) := by
  have hdef := ons_rectKWmatDartWeighted_det_eq_walk_exp
    M N (ons_rectDartSignDefect M N defect q) q hq0 hq
    (fun d => (norm_ons_rectDartSignDefect M N defect hq0 d).le)
  have hplain := ons_rectKWmatDartWeighted_det_eq_walk_exp
    M N (fun _ => (q : Complex)) q hq0 hq (fun d => by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0])
  rw [ons_rectKWmatDartWeighted_const] at hplain
  rw [hdef, hplain, ← Complex.exp_sub]
  congr 1
  unfold ons_rectWeightedWalkExponent
  simp_rw [ons_rectKWmatDartWeighted_const]
  ring

end StatMech.Onsager
