/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Ring.Comparison.QuillenIndependentPlusHomotopyGroups

/-!
# Original-point and representative contracts for the homotopy-group comparison

These clients retain all K0 components, the actual constant loop, the
literal projected forward and zero-section inverse maps, and the original
based cube representatives. Concrete profiles keep ring, module, object,
Hom, native carrier and compact-probe roles independently sized.
-/

noncomputable section

open AlgebraicKTheory.QuillenPlus
open AlgebraicKTheory.QuillenPlus.UniverseAssembly
open scoped ContinuousMap Topology Topology.Homotopy

universe uR uM uObj uHom uNative uProbe

/-- Every actual source loop retains its independent Q/S K0 class in degree zero. -/
example (R : Type uR) [Ring R]
    (p : sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) :
    quillenIndependentPlusPiZeroEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R
      ((HomotopyGroup.pi0EquivZerothHomotopy
        (X := sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
        (x := sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)).symm
          (ZerothHomotopy.mk p)) =
      AlgebraicKTheory.OriginalQK0UniverseLiftCompatibility.nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R p :=
  quillenIndependentPlusPiZeroEquiv_loop.{uR, uM, uObj, uHom, uNative, uProbe} R p

/-- The degree-zero class of the original constant loop has the original zero label. -/
example (R : Type uR) [Ring R] :
    quillenIndependentPlusPiZeroEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R
      ((HomotopyGroup.pi0EquivZerothHomotopy
        (X := sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
        (x := sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)).symm
          (ZerothHomotopy.mk
            (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R))) = 0 :=
  (quillenIndependentPlusPiZeroEquiv_loop.{uR, uM, uObj, uHom, uNative, uProbe} R _).trans
    ((quillenIndependentPlusComponentsEquiv_mk.{uR, uM, uObj, uHom, uNative, uProbe} R _).symm.trans
      (quillenIndependentPlusComponentsEquiv_constant.{uR, uM, uObj, uHom, uNative, uProbe} R))

/-- Every fixed K0 class occurs in both the original evaluator and the actual global F. -/
example (R : Type uR) [Ring R] (k : AlgebraicKTheory.RingK0 R) :
    ∃ p : sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R,
      AlgebraicKTheory.OriginalQK0UniverseLiftCompatibility.nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R p = k ∧
      (transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R p).1 = k := by
  obtain ⟨c, hc⟩ :=
    (quillenIndependentPlusComponentsEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R).surjective k
  obtain ⟨p, rfl⟩ := ZerothHomotopy.mk_surjective c
  exact ⟨p,
    (quillenIndependentPlusComponentsEquiv_mk.{uR, uM, uObj, uHom, uNative, uProbe} R p).symm.trans hc,
    (quillenIndependentPlusComponentsEquiv_forward.{uR, uM, uObj, uHom, uNative, uProbe} R p).symm.trans hc⟩

/-- The representative maps compute the literal F/G compositions and retain both original points. -/
example (R : Type uR) [Ring R]
    (p : sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
    (b : plusSpace.{uR, uM, uObj, uHom, uNative} R) :
    quillenIndependentPlusForwardProjection.{uR, uM, uObj, uHom, uNative, uProbe} R p =
      (transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R p).2 ∧
    quillenIndependentPlusInverseSection.{uR, uM, uObj, uHom, uNative, uProbe} R b =
      transportedInverse.{uR, uM, uObj, uHom, uNative, uProbe} R ((0 : AlgebraicKTheory.RingK0 R), b) ∧
    quillenIndependentPlusForwardProjection.{uR, uM, uObj, uHom, uNative, uProbe} R
      (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) =
        plusPoint.{uR, uM, uObj, uHom, uNative} R ∧
    quillenIndependentPlusInverseSection.{uR, uM, uObj, uHom, uNative, uProbe} R
      (plusPoint.{uR, uM, uObj, uHom, uNative} R) =
        sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R :=
  ⟨quillenIndependentPlusForwardProjection_apply.{uR, uM, uObj, uHom, uNative, uProbe} R p,
    quillenIndependentPlusInverseSection_apply.{uR, uM, uObj, uHom, uNative, uProbe} R b,
    quillenIndependentPlusForwardProjection_point.{uR, uM, uObj, uHom, uNative, uProbe} R,
    quillenIndependentPlusInverseSection_point.{uR, uM, uObj, uHom, uNative, uProbe} R⟩

/-- In every positive degree both maps are the actual induced maps and both roundtrips hold. -/
example (R : Type uR) [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1)
      (sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
      (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R))
    (b : HomotopyGroup.Pi (n + 1)
      (plusSpace.{uR, uM, uObj, uHom, uNative} R)
      (plusPoint.{uR, uM, uObj, uHom, uNative} R)) :
    quillenIndependentPlusPositiveHomotopyEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R n a =
      HomotopyGroup.mapHomOfEq
        (quillenIndependentPlusForwardProjection.{uR, uM, uObj, uHom, uNative, uProbe} R)
        (quillenIndependentPlusForwardProjection_point.{uR, uM, uObj, uHom, uNative, uProbe} R) n a ∧
    (quillenIndependentPlusPositiveHomotopyEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R n).symm b =
      HomotopyGroup.mapHomOfEq
        (quillenIndependentPlusInverseSection.{uR, uM, uObj, uHom, uNative, uProbe} R)
        (quillenIndependentPlusInverseSection_point.{uR, uM, uObj, uHom, uNative, uProbe} R) n b ∧
    (quillenIndependentPlusPositiveHomotopyEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R n).symm
      (quillenIndependentPlusPositiveHomotopyEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R n a) = a ∧
    quillenIndependentPlusPositiveHomotopyEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R n
      ((quillenIndependentPlusPositiveHomotopyEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R n).symm b) = b :=
  ⟨quillenIndependentPlusPositiveHomotopyEquiv_apply.{uR, uM, uObj, uHom, uNative, uProbe} R n a,
    quillenIndependentPlusPositiveHomotopyEquiv_symm_apply.{uR, uM, uObj, uHom, uNative, uProbe} R n b,
    (quillenIndependentPlusPositiveHomotopyEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R n).symm_apply_apply a,
    (quillenIndependentPlusPositiveHomotopyEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R n).apply_symm_apply b⟩

/-- A based cube is postcomposed by the literal projected F, with its full boundary retained. -/
example (R : Type uR) [Ring R] (n : ℕ)
    (p : GenLoop (Fin (n + 1))
      (sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
      (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)) :
    quillenIndependentPlusPositiveHomotopyEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R n
      (HomotopyGroup.mk p) =
    HomotopyGroup.mk
      (⟨(quillenIndependentPlusForwardProjection.{uR, uM, uObj, uHom, uNative, uProbe} R).comp p.1,
        fun t ht =>
          (congrArg (quillenIndependentPlusForwardProjection.{uR, uM, uObj, uHom, uNative, uProbe} R)
            (GenLoop.boundary p t ht)).trans
            (quillenIndependentPlusForwardProjection_point.{uR, uM, uObj, uHom, uNative, uProbe} R)⟩ :
        GenLoop (Fin (n + 1))
          (plusSpace.{uR, uM, uObj, uHom, uNative} R)
          (plusPoint.{uR, uM, uObj, uHom, uNative} R)) :=
  (quillenIndependentPlusPositiveHomotopyEquiv_apply.{uR, uM, uObj, uHom, uNative, uProbe} R n
    (HomotopyGroup.mk p)).trans
      (HomotopyGroup.mapHomOfEq_mk n
        (quillenIndependentPlusForwardProjection.{uR, uM, uObj, uHom, uNative, uProbe} R)
        (quillenIndependentPlusForwardProjection_point.{uR, uM, uObj, uHom, uNative, uProbe} R) p)

/-- Degree one keeps the distinct 0/1/3/5/7 roles and the genuine compact probe two. -/
example (R : Type) [Ring R]
    (a : HomotopyGroup.Pi 1 (sourceSpaceWithProbe.{0, 1, 3, 5, 7, 2} R)
      (sourcePointWithProbe.{0, 1, 3, 5, 7, 2} R))
    (b : HomotopyGroup.Pi 1 (plusSpace.{0, 1, 3, 5, 7} R)
      (plusPoint.{0, 1, 3, 5, 7} R)) :
    quillenIndependentPlusPositiveHomotopyEquiv.{0, 1, 3, 5, 7, 2} R 0 a =
      HomotopyGroup.mapHomOfEq
        (quillenIndependentPlusForwardProjection.{0, 1, 3, 5, 7, 2} R)
        (quillenIndependentPlusForwardProjection_point.{0, 1, 3, 5, 7, 2} R) 0 a ∧
    (quillenIndependentPlusPositiveHomotopyEquiv.{0, 1, 3, 5, 7, 2} R 0).symm b =
      HomotopyGroup.mapHomOfEq
        (quillenIndependentPlusInverseSection.{0, 1, 3, 5, 7, 2} R)
        (quillenIndependentPlusInverseSection_point.{0, 1, 3, 5, 7, 2} R) 0 b :=
  ⟨quillenIndependentPlusPositiveHomotopyEquiv_apply.{0, 1, 3, 5, 7, 2} R 0 a,
    quillenIndependentPlusPositiveHomotopyEquiv_symm_apply.{0, 1, 3, 5, 7, 2} R 0 b⟩

/-- Degree three uses compact probe nine with the same fixed native carrier seven. -/
example (R : Type) [Ring R]
    (a : HomotopyGroup.Pi 3 (sourceSpaceWithProbe.{0, 1, 3, 5, 7, 9} R)
      (sourcePointWithProbe.{0, 1, 3, 5, 7, 9} R))
    (b : HomotopyGroup.Pi 3 (plusSpace.{0, 1, 3, 5, 7} R)
      (plusPoint.{0, 1, 3, 5, 7} R)) :
    quillenIndependentPlusPositiveHomotopyEquiv.{0, 1, 3, 5, 7, 9} R 2 a =
      HomotopyGroup.mapHomOfEq
        (quillenIndependentPlusForwardProjection.{0, 1, 3, 5, 7, 9} R)
        (quillenIndependentPlusForwardProjection_point.{0, 1, 3, 5, 7, 9} R) 2 a ∧
    (quillenIndependentPlusPositiveHomotopyEquiv.{0, 1, 3, 5, 7, 9} R 2).symm b =
      HomotopyGroup.mapHomOfEq
        (quillenIndependentPlusInverseSection.{0, 1, 3, 5, 7, 9} R)
        (quillenIndependentPlusInverseSection_point.{0, 1, 3, 5, 7, 9} R) 2 b :=
  ⟨quillenIndependentPlusPositiveHomotopyEquiv_apply.{0, 1, 3, 5, 7, 9} R 2 a,
    quillenIndependentPlusPositiveHomotopyEquiv_symm_apply.{0, 1, 3, 5, 7, 9} R 2 b⟩

#check @quillenIndependentPlusComponentsEquiv
#print axioms quillenIndependentPlusComponentsEquiv
#check @quillenIndependentPlusPiZeroEquiv
#print axioms quillenIndependentPlusPiZeroEquiv
#check @quillenIndependentPlusForwardProjection
#print axioms quillenIndependentPlusForwardProjection
#check @quillenIndependentPlusInverseSection
#print axioms quillenIndependentPlusInverseSection
#check @quillenIndependentPlusPositiveHomotopyEquiv
#print axioms quillenIndependentPlusPositiveHomotopyEquiv
#check @quillenIndependentPlusPositiveHomotopyEquiv_apply
#print axioms quillenIndependentPlusPositiveHomotopyEquiv_apply
#check @quillenIndependentPlusPositiveHomotopyEquiv_symm_apply
#print axioms quillenIndependentPlusPositiveHomotopyEquiv_symm_apply
#check @quillenIndependentPlusPiOneAddEquiv
#print axioms quillenIndependentPlusPiOneAddEquiv

end
