/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.SphereHom
import MathlibExt.AlgebraicTopology.Spectra.Sequential.OrderedLoop.GroupEvaluation

/-!
# Positive homotopy groups of iterated native loops

For a pointed compactly generated weak Hausdorff space `X` and natural numbers `n` and `k`,
the native iterated loop functor gives a multiplicative equivalence between
`piN (k + 1) ((loopPower n).obj X)` and `piN (k + n + 1) X`. The forward group comparison
agrees with the all-degree homotopy-group shift after identifying the degree expressions,
and the inverse preserves multiplication.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.SphereHom

open PointedCGWH.SequentialSpectrum.OrderedLoop.HomotopyEvaluationGeometry

/-- Reuse the genuine group shift along the same full ordered native loop functor. -/
abbrev loopPowerGroupShift (n k : ℕ) :=
  PointedCGWH.SequentialSpectrum.OrderedLoop.HomotopyEvaluationGeometry.loopPowerGroupShiftNatIso
    n k

/-- The original all-degree shift with its positive output degree kept canonical. -/
def positiveLoopPowerPiShift (n k : ℕ) (X : PointedCGWH.{u, v}) :
    PointedCGWH.piN (k + 1) ((loopPower n).obj X) ≃ PointedCGWH.piN (k + n + 1) X :=
  ((loopPowerPiShift n (k + 1)).app X).toEquiv.trans
    (Equiv.cast (congrArg (fun q => PointedCGWH.piN q X)
      (show k + 1 + n = k + n + 1 by omega)))

/-- The actual group comparison uses the same canonical positive degree. -/
def positiveLoopPowerGroupIso (n k : ℕ) (X : PointedCGWH.{u, v}) :
    (PointedCGWH.piNPositiveFunctor k).obj ((loopPower n).obj X) ≅
      (PointedCGWH.piNPositiveFunctor (k + n)).obj X :=
  (loopPowerGroupShift n k).app X

/-- The group isomorphism itself supplies the exact positive underlying correspondence. -/
def positiveLoopPowerMulEquiv (n k : ℕ) (X : PointedCGWH.{u, v}) :
    PointedCGWH.piN (k + 1) ((loopPower n).obj X) ≃*
      PointedCGWH.piN (k + n + 1) X :=
  (positiveLoopPowerGroupIso n k X).groupIsoToMulEquiv

/-- The full positive inverse preserves the original multiplication. -/
theorem positiveLoopPowerMulEquiv_inverse_mul (n k : ℕ) (X : PointedCGWH.{u, v})
    (x y : PointedCGWH.piN (k + n + 1) X) :
    (positiveLoopPowerMulEquiv n k X).symm (x * y) =
      (positiveLoopPowerMulEquiv n k X).symm x *
        (positiveLoopPowerMulEquiv n k X).symm y :=
  (positiveLoopPowerMulEquiv n k X).symm.map_mul x y

theorem positiveLoopGroup_hom_eq_allDegree (n k : ℕ) (X : PointedCGWH.{u, v})
    (x : PointedCGWH.piN (k + 1)
      ((PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower n).obj X)) :
    ((loopPowerGroupShiftNatIso n k).hom.app X).hom x =
      Equiv.cast (congrArg (fun d => PointedCGWH.piN d X)
        (show k + 1 + n = k + n + 1 by omega))
        ((loopPowerPiShift n (k + 1)).hom.app X x) := by
  induction n generalizing k X with
  | zero =>
    simp only [loopPowerGroupShiftNatIso, loopPowerPiShift]
    rfl
  | succ n ih =>
    let x' : PointedCGWH.piN (k + 1)
        (PointedCGWH.loop.obj ((PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower n).obj X)) := x
    have hShift := PointedCGWH.NativeLoopShiftGeometry.nativeLoopGroupShiftNatIso_hom_eq_allDegree
      k ((PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower n).obj X) x'
    let y : PointedCGWH.piN (k + 2)
        ((PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower n).obj X) :=
      (PointedCGWH.NativeLoopShiftGeometry.nativeLoopPiShiftNatIso (k + 1)).hom.app
        ((PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower n).obj X) x'
    have hi := ih (k + 1) X y
    change
      (((eqToIso (congrArg PointedCGWH.piNPositiveFunctor
        (show k + 1 + n = k + (n + 1) by omega))).hom.app X).hom)
        (((loopPowerGroupShiftNatIso n (k + 1)).hom.app X).hom
          (((PointedCGWH.NativeLoopShiftGeometry.nativeLoopGroupShiftNatIso k).hom.app
            ((PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower n).obj X)).hom x)) = _
    have h := congrArg (fun a =>
      (((eqToIso (congrArg PointedCGWH.piNPositiveFunctor
        (show k + 1 + n = k + (n + 1) by omega))).hom.app X).hom)
        (((loopPowerGroupShiftNatIso n (k + 1)).hom.app X).hom a)) hShift
    apply h.trans
    calc
      _ = _ := congrArg
        (((eqToIso (congrArg PointedCGWH.piNPositiveFunctor
          (show k + 1 + n = k + (n + 1) by omega))).hom.app X).hom) hi
      _ = _ := by
        let z := (loopPowerPiShift n (k + 2)).hom.app X y
        change
          (((eqToIso (congrArg PointedCGWH.piNPositiveFunctor
            (show k + 1 + n = k + (n + 1) by omega))).hom.app X).hom)
            (Equiv.cast (congrArg (fun d => PointedCGWH.piN d X)
              (show k + 1 + 1 + n = k + 1 + n + 1 by omega)) z) =
          Equiv.cast (congrArg (fun d => PointedCGWH.piN d X)
            (show k + 1 + (n + 1) = k + (n + 1) + 1 by omega))
            (((eqToIso (congrArg PointedCGWH.piNFunctor
              (show k + 1 + 1 + n = k + 1 + (n + 1) by omega))).hom.app X) z)
        have castCoherence {a b c : ℕ} (h : a = b) (h' : b + 1 = c)
            (z : PointedCGWH.piN (a + 1) X) :
            (((eqToIso (congrArg PointedCGWH.piNPositiveFunctor h)).hom.app X).hom) z =
              Equiv.cast (congrArg (fun d => PointedCGWH.piN d X)
                (congrArg (fun d => d + 1) h)) z := by
          cases h
          rfl
        rw [castCoherence
          (show k + 1 + n = k + (n + 1) by omega) rfl]
        have typeCastCoherence {a b : ℕ} (h : a = b)
            (z : PointedCGWH.piN a X) :
            ((eqToIso (congrArg PointedCGWH.piNFunctor h)).hom.app X) z =
              Equiv.cast (congrArg (fun d => PointedCGWH.piN d X) h) z := by
          cases h
          rfl
        have htype := typeCastCoherence
          (show k + 1 + 1 + n = k + 1 + (n + 1) by omega) z
        apply Eq.trans _ (congrArg
          (Equiv.cast (congrArg (fun d => PointedCGWH.piN d X)
            (show k + 1 + (n + 1) = k + (n + 1) + 1 by omega))) htype.symm)
        have castPaths {a b c d : ℕ} (h₁ : a = b) (h₂ : b = d)
            (h₃ : a = c) (h₄ : c = d) (z : PointedCGWH.piN a X) :
            Equiv.cast (congrArg (fun e => PointedCGWH.piN e X) h₂)
                (Equiv.cast (congrArg (fun e => PointedCGWH.piN e X) h₁) z) =
              Equiv.cast (congrArg (fun e => PointedCGWH.piN e X) h₄)
                (Equiv.cast (congrArg (fun e => PointedCGWH.piN e X) h₃) z) := by
          cases h₁
          cases h₂
          cases h₃
          rfl
        exact castPaths
          (show k + 2 + n = k + 1 + n + 1 by omega)
          (show k + 1 + n + 1 = k + (n + 1) + 1 by omega)
          (show k + 2 + n = k + 1 + (n + 1) by omega)
          (show k + 1 + (n + 1) = k + (n + 1) + 1 by omega) z






end PointedCGWH.SphereHom
