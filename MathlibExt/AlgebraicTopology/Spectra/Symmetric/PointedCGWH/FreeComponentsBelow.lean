/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.Closed
import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FinBijDecomposition

/-!
# Free symmetric module components below their generating degree

For a monoid in Day-convolution symmetric sequences of pointed CGWH spaces, the component in
degree m < n of a module freely generated at cardinality n is initial. The comparison uses the
complete free/evaluation composite.
-/

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Operad.SmallFinBijGroupoid

namespace PointedCGWH

/-- The original native free component is initial below its generating cardinality. -/
def dayFreeAtCardNativeBelowIso_isInitial
    (A : DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid PointedCGWH.{u, v})
    [MonObj A] {n m : ℕ} (h : m < n) (X : PointedCGWH.{u, v}) :
    IsInitial ((Mod.dayFreeAt A (card n) ⋙ Mod.dayEvaluation A (card m)).obj X) :=
  IsInitial.ofIso initialIsInitial ((Mod.dayFreeAtCardBelowIso A h).app X).symm

end PointedCGWH
