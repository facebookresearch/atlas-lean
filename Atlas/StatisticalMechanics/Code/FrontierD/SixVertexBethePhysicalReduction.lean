/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheWordAlgebra











open Finset Matrix

namespace StatMech.FrontierD

noncomputable section



def sixVertexSectorIntCoordinates {N n : Nat} (x : SixVertexSector N n) :
    Fin n -> Int :=
  fun i => (sixVertexSectorPosition x i).val



theorem sixVertexBetheMonomial_eq_intMonomial {N n : Nat}
    (p : Fin n -> Real) (sigma : Equiv.Perm (Fin n))
    (x : SixVertexSector N n) :
    sixVertexBetheMonomial p sigma x =
      sixVertexBetheIntMonomial p sigma
        (sixVertexSectorIntCoordinates x) := by
  unfold sixVertexBetheMonomial sixVertexBetheIntMonomial
    sixVertexSectorIntCoordinates
  apply Finset.prod_congr rfl
  intro i _
  rw [zpow_natCast]



theorem sixVertexCoordinateBetheWave_eq_intWave {N n : Nat}
    (c : Real) (p : Fin n -> Real) (x : SixVertexSector N n) :
    sixVertexCoordinateBetheWave c p x =
      sixVertexCoordinateBetheIntWave c p
        (sixVertexSectorIntCoordinates x) := by
  unfold sixVertexCoordinateBetheWave sixVertexCoordinateBetheIntWave
  apply Finset.sum_congr rfl
  intro sigma _
  rw [sixVertexBetheMonomial_eq_intMonomial]



theorem SixVertexSatisfiesMultiplicativeBetheEquations.cyclicWordEigenvalue_sector
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) -> Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (x : SixVertexSector N (n + 1))
    (hphase : forall j, sixVertexBethePhase (p j) ≠ 1) :
    (∑ w : Finset (Fin (n + 1)),
      ∑ sigma, sixVertexBetheAmplitude c p sigma *
        sixVertexBetheWordCoefficient c
          (fun j => sixVertexBethePhase (p j)) sigma w *
        sixVertexBetheWordMonomial N
          (fun j => sixVertexBethePhase (p j)) sigma
          (sixVertexSectorIntCoordinates x) w) =
      sixVertexBetheEigenvalueCandidate c p *
        sixVertexCoordinateBetheWave c p x := by
  rw [sixVertexCoordinateBetheWave_eq_intWave]
  exact hp.cyclicWordEigenvalue hc p
    (sixVertexSectorIntCoordinates x) hphase




def SixVertexPhysicalWordExpansion {N n : Nat} (c : Real)
    (p : Fin (n + 1) -> Real) : Prop :=
  forall x : SixVertexSector N (n + 1),
    (sixVertexSectorTransferComplex N (n + 1) c).mulVec
        (sixVertexCoordinateBetheWave c p) x =
      ∑ w : Finset (Fin (n + 1)),
        ∑ sigma, sixVertexBetheAmplitude c p sigma *
          sixVertexBetheWordCoefficient c
            (fun j => sixVertexBethePhase (p j)) sigma w *
          sixVertexBetheWordMonomial N
            (fun j => sixVertexBethePhase (p j)) sigma
            (sixVertexSectorIntCoordinates x) w




theorem sixVertexCoordinateBetheEigenrelation_of_physicalWordExpansion
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) -> Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (hphase : forall j, sixVertexBethePhase (p j) ≠ 1)
    (hexpand : SixVertexPhysicalWordExpansion (N := N) c p) :
    SixVertexCoordinateBetheEigenrelation (N := N) c p := by
  unfold SixVertexCoordinateBetheEigenrelation
  funext x
  rw [hexpand x, hp.cyclicWordEigenvalue_sector hc p x hphase]
  rfl

end

end StatMech.FrontierD
