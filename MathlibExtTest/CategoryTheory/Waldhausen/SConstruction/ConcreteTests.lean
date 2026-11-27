/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import MathlibExt.Algebra.Category.FGProjectiveCat.Basic
import MathlibExt.CategoryTheory.ExactCategory.Abelian
import MathlibExt.CategoryTheory.Waldhausen.Exact
import MathlibExt.CategoryTheory.Waldhausen.SConstruction.LowDegree
import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Zero

/-!
# Concrete finite-stage consumers

Focused downstream checks for `FGModuleCat ℚ` (abelian exact structure) and
`FGProjectiveCat ℚ` (split exact structure), each with `waldhausenCategory`
installed section-locally. Covers zero-diagram well-formedness, forgetful
fully-faithfulness, and the degree-two cofiber projection applied to the
concrete bundled zero stage.
-/

open CategoryTheory
open CategoryTheory.Waldhausen.SConstruction

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.ConcreteTests

section ModConsumers

local instance : WaldhausenCategoryWithoutGluing (FGModuleCat ℚ) :=
  ExactCategory.waldhausenCategory _

/-- Zero diagram over modules is a finite stage. -/
example : IsStage 2 (zeroDiagram (FGModuleCat ℚ) 2) :=
  isStage_zeroDiagram (FGModuleCat ℚ) 2

/-- Forgetful functor over modules is fully faithful. -/
example : (forget (FGModuleCat ℚ) 2).FullyFaithful :=
  fullyFaithfulForget (FGModuleCat ℚ) 2

/-- Degree-two cofiber data over the concrete bundled zero stage. -/
example : IsCofibrationSequence (C := FGModuleCat ℚ)
    ((zeroDiagram (FGModuleCat ℚ) 2).map
      (horiz (show (0 : Fin 3) ≤ 1 by decide) (show (1 : Fin 3) ≤ 2 by decide)))
    ((zeroDiagram (FGModuleCat ℚ) 2).map
      (vert (show (0 : Fin 3) ≤ 1 by decide) (show (1 : Fin 3) ≤ 2 by decide))) :=
  Stage.cofiber_zero_one_two (FGModuleCat ℚ)
    ((⟨zeroDiagram (FGModuleCat ℚ) 2, isStage_zeroDiagram (FGModuleCat ℚ) 2⟩ :
      Stage (FGModuleCat ℚ) 2))

end ModConsumers

section ProjConsumers

local instance : WaldhausenCategoryWithoutGluing (FGProjectiveCat ℚ) :=
  ExactCategory.waldhausenCategory _

/-- Zero diagram over projectives is a finite stage. -/
example : IsStage 2 (zeroDiagram (FGProjectiveCat ℚ) 2) :=
  isStage_zeroDiagram (FGProjectiveCat ℚ) 2

/-- Forgetful functor over projectives is fully faithful. -/
example : (forget (FGProjectiveCat ℚ) 2).FullyFaithful :=
  fullyFaithfulForget (FGProjectiveCat ℚ) 2

/-- Degree-two cofiber data over the concrete bundled zero stage. -/
example : IsCofibrationSequence (C := FGProjectiveCat ℚ)
    ((zeroDiagram (FGProjectiveCat ℚ) 2).map
      (horiz (show (0 : Fin 3) ≤ 1 by decide) (show (1 : Fin 3) ≤ 2 by decide)))
    ((zeroDiagram (FGProjectiveCat ℚ) 2).map
      (vert (show (0 : Fin 3) ≤ 1 by decide) (show (1 : Fin 3) ≤ 2 by decide))) :=
  Stage.cofiber_zero_one_two (FGProjectiveCat ℚ)
    ((⟨zeroDiagram (FGProjectiveCat ℚ) 2, isStage_zeroDiagram (FGProjectiveCat ℚ) 2⟩ :
      Stage (FGProjectiveCat ℚ) 2))

end ProjConsumers

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.ConcreteTests
