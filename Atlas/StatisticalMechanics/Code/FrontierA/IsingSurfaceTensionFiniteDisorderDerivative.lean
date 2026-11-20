/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.IsingSurfaceTensionRectangularModel

open scoped BigOperators
open Finset

namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


def multibondBondSpin (ends : P -> V × V) (s : V -> Bool) (p : P) : Real :=
  if s (ends p).1 = s (ends p).2 then 1 else -1


def multibondTotalBondSpin (ends : P -> V × V) (s : V -> Bool) : Real :=
  ∑ p : P, multibondBondSpin ends s p



def multibondTwistedBondSpin
    (ends : P -> V × V) (D : Finset P) (s : V -> Bool) : Real :=
  ∑ p : P, (if p ∈ D then (-1 : Real) else 1) * multibondBondSpin ends s p


def multibondMeanTotalBondSpin (ends : P -> V × V) (J : Real) : Real :=
  (∑ s : V -> Bool,
      multibondIsingWeight ends (fun _ => J) s * multibondTotalBondSpin ends s) /
    multibondIsingPartition ends (fun _ => J)


def multibondMeanTwistedBondSpin
    (ends : P -> V × V) (D : Finset P) (J : Real) : Real :=
  (∑ s : V -> Bool,
      multibondIsingWeight ends (multibondTwistCoupling (fun _ => J) D) s *
        multibondTwistedBondSpin ends D s) /
    multibondIsingPartition ends (multibondTwistCoupling (fun _ => J) D)

theorem hasDerivAt_multibondIsingWeight_homogeneous
    (ends : P -> V × V) (s : V -> Bool) (J : Real) :
    HasDerivAt (fun K => multibondIsingWeight ends (fun _ => K) s)
      (multibondIsingWeight ends (fun _ => J) s *
        multibondTotalBondSpin ends s) J := by
  have hinner : HasDerivAt
      (fun K : Real => ∑ p : P, K * multibondBondSpin ends s p)
      (multibondTotalBondSpin ends s) J := by
    simpa [multibondTotalBondSpin] using
      (HasDerivAt.fun_sum (u := (Finset.univ : Finset P))
        (fun p _ => (hasDerivAt_id J).mul_const (multibondBondSpin ends s p)))
  simpa [multibondIsingWeight, multibondBondSpin] using
    (Real.hasDerivAt_exp
      (∑ p : P, J * multibondBondSpin ends s p)).comp J hinner

theorem hasDerivAt_multibondIsingPartition_homogeneous
    (ends : P -> V × V) (J : Real) :
    HasDerivAt (fun K => multibondIsingPartition ends (fun _ => K))
      (∑ s : V -> Bool,
        multibondIsingWeight ends (fun _ => J) s *
          multibondTotalBondSpin ends s) J := by
  unfold multibondIsingPartition
  simpa using
    (HasDerivAt.fun_sum (u := (Finset.univ : Finset (V -> Bool)))
      (fun s _ => hasDerivAt_multibondIsingWeight_homogeneous ends s J))

theorem hasDerivAt_log_multibondIsingPartition_homogeneous
    (ends : P -> V × V) (J : Real) :
    HasDerivAt
      (fun K => Real.log (multibondIsingPartition ends (fun _ => K)))
      (multibondMeanTotalBondSpin ends J) J := by
  exact (hasDerivAt_multibondIsingPartition_homogeneous ends J).log
    (multibondIsingPartition_pos ends (fun _ => J)).ne'

theorem hasDerivAt_multibondIsingWeight_twisted
    (ends : P -> V × V) (D : Finset P) (s : V -> Bool) (J : Real) :
    HasDerivAt
      (fun K => multibondIsingWeight ends
        (multibondTwistCoupling (fun _ => K) D) s)
      (multibondIsingWeight ends (multibondTwistCoupling (fun _ => J) D) s *
        multibondTwistedBondSpin ends D s) J := by
  have hinner : HasDerivAt
      (fun K : Real => ∑ p : P,
        K * ((if p ∈ D then (-1 : Real) else 1) * multibondBondSpin ends s p))
      (multibondTwistedBondSpin ends D s) J := by
    simpa [multibondTwistedBondSpin] using
      (HasDerivAt.fun_sum (u := (Finset.univ : Finset P))
        (fun p _ => (hasDerivAt_id J).mul_const
          ((if p ∈ D then (-1 : Real) else 1) * multibondBondSpin ends s p)))
  convert (Real.hasDerivAt_exp
    (∑ p : P, J * ((if p ∈ D then (-1 : Real) else 1) *
      multibondBondSpin ends s p))).comp J hinner using 1 <;>
    simp [Function.comp_def, multibondIsingWeight, multibondTwistCoupling,
      multibondBondSpin]

theorem hasDerivAt_multibondIsingPartition_twisted
    (ends : P -> V × V) (D : Finset P) (J : Real) :
    HasDerivAt
      (fun K => multibondIsingPartition ends
        (multibondTwistCoupling (fun _ => K) D))
      (∑ s : V -> Bool,
        multibondIsingWeight ends (multibondTwistCoupling (fun _ => J) D) s *
          multibondTwistedBondSpin ends D s) J := by
  unfold multibondIsingPartition
  simpa using
    (HasDerivAt.fun_sum (u := (Finset.univ : Finset (V -> Bool)))
      (fun s _ => hasDerivAt_multibondIsingWeight_twisted ends D s J))

theorem hasDerivAt_log_multibondIsingPartition_twisted
    (ends : P -> V × V) (D : Finset P) (J : Real) :
    HasDerivAt
      (fun K => Real.log (multibondIsingPartition ends
        (multibondTwistCoupling (fun _ => K) D)))
      (multibondMeanTwistedBondSpin ends D J) J := by
  exact (hasDerivAt_multibondIsingPartition_twisted ends D J).log
    (multibondIsingPartition_pos ends
      (multibondTwistCoupling (fun _ => J) D)).ne'



theorem hasDerivAt_multibondDisorderFreeEnergy_homogeneous
    (ends : P -> V × V) (D : Finset P) (J : Real) :
    HasDerivAt (fun K => multibondDisorderFreeEnergy ends (fun _ => K) D)
      (multibondMeanTotalBondSpin ends J -
        multibondMeanTwistedBondSpin ends D J) J := by
  unfold multibondDisorderFreeEnergy
  exact (hasDerivAt_log_multibondIsingPartition_homogeneous ends J).sub
    (hasDerivAt_log_multibondIsingPartition_twisted ends D J)



theorem hasDerivAt_finiteRectangularIsingDisorderFreeEnergy
    (m n : Nat) (J : Real) :
    HasDerivAt (fun K => finiteRectangularIsingDisorderFreeEnergy K m n)
      (multibondMeanTotalBondSpin
          (cubicalDualEnds (a := m) (b := n) (c := max m n)) J -
        multibondMeanTwistedBondSpin
          (cubicalDualEnds (a := m) (b := n) (c := max m n))
          (cubicalXYSheet (a := m) (b := n) (c := max m n)
            (0 : Fin (max m n + 1))) J) J := by
  exact hasDerivAt_multibondDisorderFreeEnergy_homogeneous
    (cubicalDualEnds (a := m) (b := n) (c := max m n))
    (cubicalXYSheet (a := m) (b := n) (c := max m n)
      (0 : Fin (max m n + 1))) J

end

end StatMech.FrontierA
