/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheFiniteRoots
import Code.FrontierD.SixVertexBethePhysicalExpansion










open Finset Matrix

namespace StatMech.FrontierD

noncomputable section


theorem SixVertexSatisfiesMultiplicativeBetheEquations.physicalCoordinateBetheEigenrelation_of_pos
    {c : Real} (hc : 2 < c) {N n : Nat} (hn : 0 < n)
    (p : Fin n → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N n p)
    (hphase : ∀ j, sixVertexBethePhase (p j) ≠ 1) :
    SixVertexCoordinateBetheEigenrelation (N := N) c p := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact hp.physicalCoordinateBetheEigenrelation hc p hphase



theorem sixVertexHalfFilledBetheRoots_physicalEigenrelation
    {c : Real} (hc : 2 < c) (k : Nat) :
    SixVertexCoordinateBetheEigenrelation
      (N := sixVertexFourWidth 0 k) c
      (sixVertexHalfFilledBetheRoots hc k) := by
  exact SixVertexSatisfiesMultiplicativeBetheEquations.physicalCoordinateBetheEigenrelation_of_pos
    hc (by omega) (sixVertexHalfFilledBetheRoots hc k)
    (sixVertexHalfFilledBetheRoots_is_multiplicativeSolution hc k)
    (sixVertexHalfFilledBetheRoots_phase_ne_one hc k)


def sixVertexHalfFilledBetheRealWave
    {c : Real} (hc : 2 < c) (k : Nat) :
    SixVertexSector (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) → Real :=
  fun x => (sixVertexCoordinateBetheWave c
    (sixVertexHalfFilledBetheRoots hc k) x).re



theorem sixVertexHalfFilledBetheRealWave_eigenrelation
    {c : Real} (hc : 2 < c) (k : Nat) :
    sixVertexSectorTransfer (sixVertexFourWidth 0 k)
        ((k + 1) + (k + 1)) c *ᵥ
      sixVertexHalfFilledBetheRealWave hc k =
        sixVertexSymmetricBetheEigenvalueValue c
          (sixVertexPositiveHalfBetheRoots hc k) •
            sixVertexHalfFilledBetheRealWave hc k := by
  funext x
  have hx := congrFun
    (sixVertexHalfFilledBetheRoots_physicalEigenrelation hc k) x
  have hre := congrArg Complex.re hx
  simp only [sixVertexSectorTransferComplex_mulVec_apply,
    sixVertexHalfFilledBetheEigenvalueCandidate_eq_value hc k,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Pi.smul_apply, smul_eq_mul] at hre
  simpa [sixVertexHalfFilledBetheRealWave, Matrix.mulVec, dotProduct,
    smul_eq_mul] using hre


def SixVertexSelectedHalfFilledWavePositive (c : Real) : Prop :=
  ∀ (hc : 2 < c) (k : Nat) (x : SixVertexSector
      (sixVertexFourWidth 0 k) ((k + 1) + (k + 1))),
    0 < sixVertexHalfFilledBetheRealWave hc k x



theorem sixVertexHasSymmetricBetheIdentification_of_selectedWavePositive
    {c : Real} (hc : 2 < c)
    (hpos : SixVertexSelectedHalfFilledWavePositive c) :
    SixVertexHasSymmetricBetheIdentification c
      (sixVertexPositiveHalfBetheRootFamily hc) := by
  intro k
  have hn : (k + 1) + (k + 1) ≤ sixVertexFourWidth 0 k := by
    unfold sixVertexFourWidth
    omega
  have heq := sixVertexSector_eigenvalue_eq_top_of_positive_eigenvector
    hn (show 0 < c by linarith)
    (sixVertexHalfFilledBetheRealWave hc k) (hpos hc k)
    (sixVertexHalfFilledBetheRealWave_eigenrelation hc k)
  have hhalf : sixVertexFourWidth 0 k / 2 = (k + 1) + (k + 1) := by
    unfold sixVertexFourWidth
    omega
  have heq' : sixVertexSymmetricBetheEigenvalueValue c
        (sixVertexPositiveHalfBetheRoots hc k) =
      sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
        (sixVertexFourWidth 0 k / 2) (Nat.div_le_self _ _) c := by
    simpa only [hhalf] using heq
  unfold sixVertexLambdaAlongFour sixVertexLambda
  simpa only [Nat.sub_zero] using heq'.symm

end

end StatMech.FrontierD
