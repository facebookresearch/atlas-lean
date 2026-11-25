/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.Factorization

/-!
# Minimal-fibration construction consumer tests

Exercises the public existence packet, Arrow retract, boundary-RLP retraction,
and exact factorization destructuring expected by later recognition code.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.MinimalFibrationConstructionTests

variable {E B : SSet.{u}} {p : E ⟶ B}

example [Fibration p] :
    Nonempty (SSet.MinimalFibration.MinimalSubfibration p) :=
  SSet.MinimalFibration.nonempty_minimalSubfibration p

example (M : SSet.MinimalFibration.MinimalSubfibration p) :
    RetractArrow (M.carrier.ι ≫ p) p :=
  M.retractArrow

example [Fibration p] (M : SSet.MinimalFibration.MinimalSubfibration p) :
    SSet.modelCategoryQuillen.I.{u}.rlp M.sdr.r :=
  M.retraction_mem_I_rlp

example (p : E ⟶ B) [Fibration p] :
    ∃ (E' : SSet.{u}) (r : E ⟶ E') (p' : E' ⟶ B),
      r ≫ p' = p ∧ SSet.MinimalFibration.IsMinimalFibration p' ∧
        SSet.modelCategoryQuillen.I.{u}.rlp r := by
  obtain ⟨E', r, p', fac, hp', hr⟩ :=
    SSet.MinimalFibration.factorization p
  have hp'_fibration : Fibration p' := hp'.1
  exact ⟨E', r, p', fac, ⟨hp'_fibration, hp'.2⟩, hr⟩

#check SSet.MinimalFibration.congr_ι₁_comp
#check SSet.MinimalFibration.congr_ι₀_comp
#check SSet.FiberwiseHomotopy.injective_app_of_isMinimalFibration
#check SSet.FiberwiseHomotopy.surjective_app_of_isMinimalFibration
#check SSet.FiberwiseHomotopy.isIso_of_isMinimalFibration
#check SSet.MinimalFibration.isIso_of_fiberwiseHomotopyEquiv

#print axioms SSet.MinimalFibration.nonempty_minimalSubfibration
#print axioms SSet.MinimalFibration.MinimalSubfibration.retraction_mem_I_rlp
#print axioms SSet.MinimalFibration.factorization

end MathlibExtTest.AlgebraicTopology.SimplicialSet.MinimalFibrationConstructionTests
