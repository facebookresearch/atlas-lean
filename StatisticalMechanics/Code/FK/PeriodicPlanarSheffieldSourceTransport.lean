/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldAdjacentHeight











open Filter MeasureTheory Set Topology

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}






theorem PeriodicPlaneEmbedding.adjacentHeightVerticalCrossing_transport_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (a b c d : Nat -> Real) (step : Nat -> Int)
    (hstep : forall n, 0 <= step n)
    (L R : Nat -> Finset V) (z : Nat -> Site 2)
    (radius : Nat -> Nat) (epsilon : Nat -> Real)
    (hbottom : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((L n).image (P.shift (z n)) : Set V)
        (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1))
    (hhit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (R n : Set V))) atTop (nhds 1))
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hopposite : forall n,
      mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((R n).image (P.shift (z n)) : Set V)
        (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n))) <=
      mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((R n).image (P.shift (z n)) : Set V)
        (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n))) + epsilon n)
    (hmergeCurrent : Tendsto (fun n => mu.real
      (P.pairMergeErrorUnion (L n) (R n) (radius n))) atTop (nhds 0))
    (hmergeSuccessor : Tendsto (fun n => mu.real
      (P.pairMergeErrorUnion (L n)
        ((R n).image (P.shift (verticalShift (step n)))) (radius n)))
      atTop (nhds 0))
    (hconnector : forall n,
      (P.shift (z n) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
      E.rectVertices (a n) (b n) (c n) (d n)) :
    Tendsto (fun n => mu.real
      (E.verticalCrossingEvent
        (a n) (b n) (c n) (d n + step n))) atTop (nhds 1) := by
  let Lz : Nat -> Finset V := fun n => (L n).image (P.shift (z n))
  let Rz : Nat -> Finset V := fun n => (R n).image (P.shift (z n))
  let Rstep : Nat -> Finset V := fun n =>
    (R n).image (P.shift (verticalShift (step n)))
  let U : Nat -> Finset V := fun n =>
    (Rz n).image (P.shift (verticalShift (step n)))
  have hconnectorSuccessor (n : Nat) :
      (P.shift (z n) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
      E.rectVertices (a n) (b n) (c n) (d n + step n) := by
    have hstepReal : (0 : Real) <= step n := by exact_mod_cast hstep n
    exact (hconnector n).trans
      (E.rectVertices_mono le_rfl le_rfl le_rfl (by linarith))
  have hcurrent : Tendsto (fun n => mu.real
      (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
        (Lz n) (Rz n))) atTop (nhds 0) := by
    apply squeeze_zero (fun _ => measureReal_nonneg) _ hmergeCurrent
    intro n
    simpa only [Lz, Rz] using
      E.translated_rectanglePairMergeErrorUnion_measureReal_le
        mu hTI (z n) (a n) (b n) (c n) (d n)
          (L n) (R n) (radius n) (hconnector n)
  have hsuccessorEq (n : Nat) :
      U n = (Rstep n).image (P.shift (z n)) := by
    simp only [U, Rz, Rstep, Finset.image_image]
    apply Finset.image_congr
    intro u hu
    change P.shift (verticalShift (step n)) (P.shift (z n) u) =
      P.shift (z n) (P.shift (verticalShift (step n)) u)
    rw [<- P.shift_add, <- P.shift_add]
    congr 2
    abel
  have hsuccessorBase : Tendsto (fun n => mu.real
      (E.rectanglePairMergeErrorUnion
        (a n) (b n) (c n) (d n + step n)
        ((L n).image (P.shift (z n)))
        ((Rstep n).image (P.shift (z n))))) atTop (nhds 0) := by
    apply squeeze_zero (fun _ => measureReal_nonneg) _ hmergeSuccessor
    intro n
    simpa only [Rstep] using
      E.translated_rectanglePairMergeErrorUnion_measureReal_le
        mu hTI (z n) (a n) (b n) (c n) (d n + step n)
          (L n) (Rstep n) (radius n) (hconnectorSuccessor n)
  have hsuccessor : Tendsto (fun n => mu.real
      (E.rectanglePairMergeErrorUnion
        (a n) (b n) (c n) (d n + step n) (Lz n) (U n)))
      atTop (nhds 0) := by
    apply hsuccessorBase.congr'
    filter_upwards [] with n
    rw [hsuccessorEq n]
  let A : Nat -> Real := fun n => mu.real
    (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      (Lz n : Set V)
      (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))
  let H : Nat -> Real := fun n => mu.real
    (P.setHitsInfinite (Rz n : Set V))
  let M0 : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion
      (a n) (b n) (c n) (d n) (Lz n) (Rz n))
  let M1 : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion
      (a n) (b n) (c n) (d n + step n) (Lz n) (U n))
  have hA : Tendsto A atTop (nhds 1) := by
    simpa only [A, Lz] using hbottom
  have hH : Tendsto H atTop (nhds 1) := by
    apply hhit.congr'
    filter_upwards [] with n
    have hset : ((Rz n : Finset V) : Set V) =
        P.shift (z n) '' (R n : Set V) := by
      ext v
      simp [Rz]
    dsimp only [H]
    rw [hset, P.setHitsInfinite_translate_measureReal_eq mu hTI]
  have hM0 : Tendsto M0 atTop (nhds 0) := by
    simpa only [M0] using hcurrent
  have hM1 : Tendsto M1 atTop (nhds 0) := by
    simpa only [M1] using hsuccessor
  let lower : Nat -> Real := fun n =>
    A n * (H n * A n - M0 n - epsilon n) - M1 n
  have hlower : Tendsto lower atTop (nhds 1) := by
    have hHA : Tendsto (fun n => H n * A n) atTop (nhds 1) := by
      simpa using hH.mul hA
    have hinner : Tendsto (fun n => H n * A n - M0 n - epsilon n)
        atTop (nhds 1) := by
      simpa using (hHA.sub hM0).sub hepsilon
    have hfinal := (hA.mul hinner).sub hM1
    norm_num at hfinal
    simpa only [lower] using hfinal
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlower tendsto_const_nhds
  · intro n
    have htransport :=
      E.adjacentHeightVerticalCrossing_ge_approxPreferredSide_transfer
        mu hFKG hTI (a n) (b n) (c n) (d n) (step n) (hstep n)
          (Lz n) (Rz n) (epsilon n) (by simpa only [Rz] using hopposite n)
    simpa only [lower, A, H, M0, M1, U] using htransport
  · intro n
    exact measureReal_le_one

end StatMech.FK.PeriodicPlanar
