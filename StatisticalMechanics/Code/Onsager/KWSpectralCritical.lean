/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.KWSpectralSharp
import Code.Onsager.SignedLoopCriticalWeight
import Code.Onsager.KWWeighted









namespace StatMech.Onsager

open Matrix BigOperators
open scoped Matrix.Norms.L2Operator



noncomputable def ons_KWcolumnMultiplier (L : Nat)
    (weight : Sym2 (ZMod L × ZMod L) -> Complex) (a b : Fin 2)
    (dart : ons_Dart L) : Complex :=
  ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b) dart.2 *
    weight (ons_portEdge L dart)



theorem ons_KWmatWeightedPhase_eq_unit_mul_diagonal
    (L : Nat) [NeZero L]
    (weight : Sym2 (ZMod L × ZMod L) -> Complex) (a b : Fin 2) :
    ons_KWmatWeightedPhase L weight ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) =
      ons_KWmat L 1 ons_turnRoot *
        Matrix.diagonal (ons_KWcolumnMultiplier L weight a b) := by
  ext d2 d1
  rw [Matrix.mul_diagonal]
  unfold ons_KWcolumnMultiplier ons_KWmatWeightedPhase ons_KWmatWeighted
  by_cases hstep : d2.1 = ons_dirStep L d1.2 d1.1
  · rw [if_pos hstep]
    simp [ons_KWmat, hstep]
    ring
  · rw [if_neg hstep]
    simp [ons_KWmat, hstep]



theorem norm_ons_KWcolumnMultiplier_le
    (L : Nat) (weight : Sym2 (ZMod L × ZMod L) -> Complex)
    (a b : Fin 2) (dart : ons_Dart L) :
    ‖ons_KWcolumnMultiplier L weight a b dart‖ <=
      ‖weight (ons_portEdge L dart)‖ := by
  unfold ons_KWcolumnMultiplier
  rw [norm_mul]
  have hphase :
      ‖ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b) dart.2‖ = 1 := by
    generalize hdir : dart.2 = direction
    fin_cases direction <;> simp [ons_dirPhase, norm_ons_spinPhase]
  rw [hphase, one_mul]



theorem norm_diagonal_ons_KWcolumnMultiplier_le
    (L : Nat) [NeZero L]
    (weight : Sym2 (ZMod L × ZMod L) -> Complex) (a b : Fin 2)
    (q : Real) (hweight : forall edge, ‖weight edge‖ <= q) :
    letI : NormedRing (Matrix (ons_Dart L) (ons_Dart L) Complex) :=
      Matrix.instL2OpNormedRing
    ‖Matrix.diagonal (ons_KWcolumnMultiplier L weight a b)‖ <= q := by
  letI : NormedRing (Matrix (ons_Dart L) (ons_Dart L) Complex) :=
    Matrix.instL2OpNormedRing
  rw [Matrix.l2_opNorm_diagonal]
  have hq0 : 0 <= q :=
    (norm_nonneg (weight (ons_portEdge L (((0, 0), 0) : ons_Dart L)))).trans
      (hweight _)
  rw [pi_norm_le_iff_of_nonneg hq0]
  intro dart
  exact (norm_ons_KWcolumnMultiplier_le L weight a b dart).trans
    (hweight (ons_portEdge L dart))



theorem norm_ons_KWmatWeightedPhase_sharp
    (L : Nat) [NeZero L]
    (weight : Sym2 (ZMod L × ZMod L) -> Complex) (a b : Fin 2)
    (q : Real) (hweight : forall edge, ‖weight edge‖ <= q) :
    letI : NormedRing (Matrix (ons_Dart L) (ons_Dart L) Complex) :=
      Matrix.instL2OpNormedRing
    ‖ons_KWmatWeightedPhase L weight ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)‖ <=
      (Real.sqrt 2 + 1) * q := by
  letI : NormedRing (Matrix (ons_Dart L) (ons_Dart L) Complex) :=
    Matrix.instL2OpNormedRing
  rw [ons_KWmatWeightedPhase_eq_unit_mul_diagonal]
  calc
    ‖ons_KWmat L 1 ons_turnRoot *
        Matrix.diagonal (ons_KWcolumnMultiplier L weight a b)‖ <=
      ‖ons_KWmat L 1 ons_turnRoot‖ *
        ‖Matrix.diagonal (ons_KWcolumnMultiplier L weight a b)‖ :=
          Matrix.l2_opNorm_mul _ _
    _ <= (Real.sqrt 2 + 1) * q := by
      gcongr
      · simpa using norm_ons_KWmat_turnRoot_sharp L (1 : Complex)
      · exact norm_diagonal_ons_KWcolumnMultiplier_le
          L weight a b q hweight


theorem norm_root_ons_KWmatWeightedPhase_le
    (L : Nat) [NeZero L]
    (weight : Sym2 (ZMod L × ZMod L) -> Complex) (a b : Fin 2)
    (q : Real) (hweight : forall edge, ‖weight edge‖ <= q)
    (alpha : Complex)
    (halpha : alpha ∈
      (ons_KWmatWeightedPhase L weight ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)).charpoly.roots) :
    ‖alpha‖ <= (Real.sqrt 2 + 1) * q := by
  letI : NormedRing (Matrix (ons_Dart L) (ons_Dart L) Complex) :=
    Matrix.instL2OpNormedRing
  let A := ons_KWmatWeightedPhase L weight ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b)
  have hroot : A.charpoly.IsRoot alpha :=
    (Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero).mp halpha
  have heig : Module.End.HasEigenvalue (Matrix.toLin' A) alpha :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly (Matrix.toLin' A) alpha).2 <| by
      rw [Matrix.charpoly_toLin']
      exact hroot
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  let vE : EuclideanSpace Complex (ons_Dart L) :=
    (EuclideanSpace.equiv (ons_Dart L) Complex).symm v
  have hvE : vE ≠ 0 := by
    intro hzero
    apply hv.2
    apply (EuclideanSpace.equiv (ons_Dart L) Complex).symm.injective
    simpa [vE] using hzero
  have heigen :
      (EuclideanSpace.equiv (ons_Dart L) Complex).symm (A *ᵥ vE) =
        alpha • vE := by
    apply (EuclideanSpace.equiv (ons_Dart L) Complex).injective
    simpa [vE, Matrix.toLin'_apply] using hv.apply_eq_smul
  have hmul : ‖alpha‖ * ‖vE‖ <= ‖A‖ * ‖vE‖ := by
    rw [← norm_smul, ← heigen]
    exact Matrix.l2_opNorm_mulVec A vE
  have halpha_le : ‖alpha‖ <= ‖A‖ :=
    le_of_mul_le_mul_right hmul (norm_pos_iff.mpr hvE)
  exact halpha_le.trans
    (norm_ons_KWmatWeightedPhase_sharp L weight a b q hweight)



theorem ons_KWmatWeightedPhase_spectral_critical
    (L : Nat) [NeZero L]
    (weight : Sym2 (ZMod L × ZMod L) -> Complex) (a b : Fin 2)
    (q : Real) (hq : q < ons_signedLoopCriticalWeight)
    (hweight : forall edge, ‖weight edge‖ <= q) :
    ∀ alpha ∈
      (ons_KWmatWeightedPhase L weight ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)).charpoly.roots,
      ‖alpha‖ < 1 := by
  intro alpha halpha
  refine (norm_root_ons_KWmatWeightedPhase_le
    L weight a b q hweight alpha halpha).trans_lt ?_
  have hconstant : 0 < Real.sqrt 2 + 1 := by positivity
  have hmul := mul_lt_mul_of_pos_left hq hconstant
  simpa [sqrt_two_add_one_mul_signedLoopCriticalWeight] using hmul



theorem ons_KWmatWeightedPhase_det_eq_walk_exp_critical
    (L : Nat) [NeZero L]
    (weight : Sym2 (ZMod L × ZMod L) -> Complex) (a b : Fin 2)
    (q : Real) (hq : q < ons_signedLoopCriticalWeight)
    (hweight : forall edge, ‖weight edge‖ <= q) :
    (1 - ons_KWmatWeightedPhase L weight ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)).det =
      Complex.exp (- ∑' n : Nat,
        (∑ v : Fin (n + 1) -> ons_Dart L,
          ∏ k : Fin (n + 1),
            ons_KWmatWeightedPhase L weight ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b)
              (v k) (v (k + 1))) / (n + 1)) := by
  exact ons_det_eq_walk_exp _
    (ons_KWmatWeightedPhase_spectral_critical
      L weight a b q hq hweight)


theorem ons_KWmatPhase_det_eq_walk_exp_critical
    (L : Nat) [NeZero L] (q : Real)
    (hq0 : 0 <= q) (hq : q < ons_signedLoopCriticalWeight)
    (a b : Fin 2) :
    (1 - ons_KWmatPhase L (q : Complex) ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)).det =
      Complex.exp (- ∑' n : Nat,
        (∑ v : Fin (n + 1) -> ons_Dart L,
          ∏ k : Fin (n + 1),
            ons_KWmatPhase L (q : Complex) ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b)
              (v k) (v (k + 1))) / (n + 1)) := by
  rw [← ons_KWmatWeightedPhase_const]
  apply ons_KWmatWeightedPhase_det_eq_walk_exp_critical
    L (fun _ => (q : Complex)) a b q hq
  intro edge
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]



theorem ons_KWmatPhase_tanh_det_eq_walk_exp_before_betaC
    (L : Nat) [NeZero L] (beta : Real)
    (hbeta0 : 0 <= beta) (hbetaC : beta < ons_betaC)
    (a b : Fin 2) :
    (1 - ons_KWmatPhase L (Real.tanh beta : Complex) ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)).det =
      Complex.exp (- ∑' n : Nat,
        (∑ v : Fin (n + 1) -> ons_Dart L,
          ∏ k : Fin (n + 1),
            ons_KWmatPhase L (Real.tanh beta : Complex) ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b)
              (v k) (v (k + 1))) / (n + 1)) := by
  apply ons_KWmatPhase_det_eq_walk_exp_critical L (Real.tanh beta)
  · rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hbeta0)
      (Real.cosh_pos beta).le
  · exact tanh_lt_signedLoopCriticalWeight hbetaC

end StatMech.Onsager
