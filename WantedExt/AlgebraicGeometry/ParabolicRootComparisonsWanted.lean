/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.ParabolicRootComparisonData
public import MathlibExt.AlgebraicGeometry.MonoidSheafCharts

/-!
# Normalized global parabolic construction and source theorem requests

The category, all weighted direct-image operations, periods, native
projection-square mates, full coefficient restriction recipes and
balanced tensor/unit comparisons are fixed in MathlibExt. Construction
selects their source integration data jointly. The canonical tensor
equivalence of abelian categories is the conclusion.

Source: Borne–Vistoli arXiv:1001.0466v2, Theorem6.1. Its hypotheses
are coherent DF structure and coherent Kummer denominator system on
an arbitrary scheme. No SNC or prime-to-characteristic assumption.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.ParabolicRootComparisons

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry DeligneFaltingsSheaves DenominatorRootStacks
open EtaleMonoidInverseImage ParabolicSheafCategories MonoidSheafCharts ParabolicRootComparisonData

variable {X : Scheme.{0}}
  [∀ (Y Z : Scheme.{0}) (f : Y ⟶ Z), HasInverseImage f]

/-- Joint construction fixes Phi on all objects, labelled weight and
coefficient arrows, periods, units, tensors and étale restrictions. -/
public def_wanted normalizedParabolicRootData
    (I : NativeDFImages.{0}) {A B : DeligneFaltingsSheaves.MonoidSheaf X}
    (D : Structure A) (hD : IsDeligneFaltings D)
    (J : DenominatorSystem A B) (G : GroupifiedDF D)
    (R : DenominatorRootStacks.Model I D J.map (𝟙 X)) :
    Data I D J.map G R

/-- Canonical native monoidal Phi is an equivalence of the actual
abelian categories, with the already fixed unit and tensor maps, for a monoidal structure on
the parabolic category with the fixed tensor and unit (part of the result). -/
public def_wanted borneVistoliComparison
    (I : NativeDFImages.{0}) {A B : DeligneFaltingsSheaves.MonoidSheaf X}
    (D : Structure A) (hD : IsDeligneFaltings D)
    (J : DenominatorSystem A B) (G : GroupifiedDF D)
    (R : DenominatorRootStacks.Model I D J.map (𝟙 X))
    (E : Data I D J.map G R) : Comparison I D J.map G R E

end WantedExt.AlgebraicGeometry.ParabolicRootComparisons
