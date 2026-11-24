/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexBoundaryRLPRecognition

/-!
# Kan boundary-RLP recognition consumer tests

Checks the forward theorem, fibration equivalence, and exact restricted
property passed to the TopCat model-category constructor.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.KanBoundaryRecognitionTests

variable {X Y : SSet.{u}} {f : X ⟶ Y}

example [SSet.KanComplex X] [SSet.KanComplex Y]
    (hf : SSet.modelCategoryQuillen.I.{u}.rlp f) :
    SSet.KanComplex.W f :=
  SSet.KanComplex.W.of_rlp_I hf

example [SSet.KanComplex X] [SSet.KanComplex Y] [Fibration f] :
    SSet.modelCategoryQuillen.I.{u}.rlp f ↔ SSet.KanComplex.W f :=
  SSet.KanComplex.I_rlp_iff_W_of_fibration f

example :
    ∀ {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y]
      {f : X ⟶ Y},
      SSet.modelCategoryQuillen.I.{u}.rlp f → SSet.KanComplex.W f :=
  SSet.KanComplex.I_rlp_to_W_kanRestricted

#print axioms SSet.KanComplex.W.of_rlp_I
#print axioms SSet.KanComplex.I_rlp_iff_W_of_fibration
#print axioms SSet.KanComplex.I_rlp_to_W_kanRestricted

end MathlibExtTest.AlgebraicTopology.SimplicialSet.KanBoundaryRecognitionTests
