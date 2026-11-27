/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.KTheory.Exact.Quillen.AdmissibleMonoQuotient

/-! # Tests for selected quotients of admissible monomorphisms -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.AlgebraicKTheory.QuillenAdmissibleMonoQuotient

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

#check AdmissibleMonoFlag.ofAdmissibleMono
#check AdmissibleMonoFlag.ofAdmissibleMonoTriple
#check AdmissibleMonoFlag.admissibleMonoQuotient
#check AdmissibleMonoFlag.admissibleMonoQuotientπ
#check AdmissibleMonoFlag.comp_admissibleMonoQuotientπ
#check AdmissibleMonoFlag.admissibleMonoQuotient_exact
#check AdmissibleMonoFlag.admissibleMonoQuotientIsoOfEq
#check AdmissibleMonoFlag.admissibleMonoQuotientπ_isoOfEq_hom

example {A B : C} (f : A ⟶ B) (hf : IsAdmissibleMono f) :
    IsAdmissibleExact
      (ShortComplex.mk f
        (AdmissibleMonoFlag.admissibleMonoQuotientπ f hf)
        (AdmissibleMonoFlag.comp_admissibleMonoQuotientπ f hf)) :=
  AdmissibleMonoFlag.admissibleMonoQuotient_exact f hf

#print axioms AdmissibleMonoFlag.admissibleMonoQuotient_exact

end MathlibExtTest.AlgebraicKTheory.QuillenAdmissibleMonoQuotient

end
