/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.KTheory.Exact.Quillen.AdmissibleMonoTripleSpanTarget

/-! # Tests for the target comparison of admissible-mono triple spans -/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.AlgebraicKTheory.QuillenAdmissibleMonoTripleSpanTarget

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

#check AdmissibleMonoFlag.admissibleMonoTripleFlag_obj_one
#check AdmissibleMonoFlag.admissibleMonoTripleFlag_obj_four
#check AdmissibleMonoFlag.admissibleMonoTripleFlag_map_one_four
#check AdmissibleMonoFlag.admissibleMonoTripleTargetIso
#check AdmissibleMonoFlag.admissibleMonoTripleTargetIso_projection
#check AdmissibleMonoFlag.admissibleMonoTripleQuillenSpan

#print axioms AdmissibleMonoFlag.admissibleMonoTripleTargetIso
#print axioms AdmissibleMonoFlag.admissibleMonoTripleQuillenSpan

end MathlibExtTest.AlgebraicKTheory.QuillenAdmissibleMonoTripleSpanTarget

end
