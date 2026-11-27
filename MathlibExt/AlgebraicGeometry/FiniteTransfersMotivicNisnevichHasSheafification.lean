/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NisnevichTransferModels
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Motivic Nisnevich sheafification for finite transfers

This module proves `motivic_nisnevich_has_sheafification`: the Nisnevich
topology on smooth schemes over a field admits sheafification for
`ℤ`-module-valued presheaves.

Sources: Mazza--Voevodsky--Weibel, Lectures 1--3 and 13;
Voevodsky, arXiv:math/0107109v1, §2.
-/

open CategoryTheory CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry.NisnevichTransferModels

/-- Native ordinary Nisnevich module sheafification on the actual smooth scheme site. -/
public theorem motivic_nisnevich_has_sheafification (k : Type) [Field k] :
    HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ) := by
  let : HasLimits (ModuleCat.{1} ℤ) :=
    ModuleCat.hasLimitsOfSize.{1, 1, 1, 0}
  let : PreservesColimitsOfSize.{1, 1}
      (forget₂ (ModuleCat.{1} ℤ) AddCommGrpCat.{1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{1, 0, 1, 1} ℤ
  let : PreservesFilteredColimits (forget (ModuleCat.{1} ℤ)) :=
    comp_preservesFilteredColimits.{1, 1}
      (forget₂ (ModuleCat.{1} ℤ) AddCommGrpCat.{1})
      (forget AddCommGrpCat.{1})
  let : PreservesFilteredColimitsOfSize.{1, 1}
      (forget (ModuleCat.{1} ℤ)) := inferInstance
  infer_instance
