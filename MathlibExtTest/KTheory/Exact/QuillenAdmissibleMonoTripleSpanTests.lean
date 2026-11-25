/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.KTheory.Exact.Quillen.AdmissibleMonoTripleSpan

/-! # Tests for Quillen spans from admissible-mono triples -/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open AlgebraicKTheory

universe v u

namespace MathlibExtTest.AlgebraicKTheory.QuillenAdmissibleMonoTripleSpan

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

#check AdmissibleMonoFlag.admissibleMonoTripleFlag
#check AdmissibleMonoFlag.admissibleMonoTripleIntervalSpan
#check AdmissibleMonoFlag.admissibleMonoTriple_comp_admissible
#check AdmissibleMonoFlag.admissibleMonoTripleSourceIso
#check AdmissibleMonoFlag.admissibleMonoTripleSourceIso_projection

#print axioms AdmissibleMonoFlag.admissibleMonoTripleIntervalSpan
#print axioms AdmissibleMonoFlag.admissibleMonoTripleSourceIso

end MathlibExtTest.AlgebraicKTheory.QuillenAdmissibleMonoTripleSpan

end
