/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.DirichletForm.RegularToQuasiRegular
import MathlibExtTest.Probability.DirichletForm.QuasiRegular

/-!
# Tests for the regular-to-quasi-regular implication

The `L²` inner-product form on two points witnesses the hypotheses with counting measure.
The empty space exercises the case with no pairs of distinct points to separate.
-/

open MeasureTheory
open MathlibExt.Probability.DirichletFormWanted
open MathlibExtTest.Probability.DirichletForm.Basic
open MathlibExtTest.Probability.DirichletForm.QuasiRegular

example : (innerForm (Measure.count : Measure Bool)).IsQuasiRegular :=
  isQuasiRegular_of_isRegular _ (hD := innerForm_isDirichletForm _) innerForm_isRegular

example : (innerForm (0 : Measure Empty)).IsQuasiRegular := by
  apply isQuasiRegular_of_isRegular _ (innerForm_isDirichletForm _)
  refine ⟨fun u _ ε hε => ⟨u, Submodule.mem_top, ⟨0, ae_of_all _ isEmptyElim⟩, ?_⟩,
    fun g ε _ => ⟨g, ⟨0, Submodule.mem_top, ae_of_all _ isEmptyElim⟩, isEmptyElim⟩⟩
  simpa [innerForm_energyOne] using hε
