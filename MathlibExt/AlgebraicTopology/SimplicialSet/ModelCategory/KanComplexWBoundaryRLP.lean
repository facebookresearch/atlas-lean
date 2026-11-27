/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.WFibrationBoundaryLifting

/-!
# Boundary lifting for weak Kan fibrations

Let I be the family of simplicial boundary inclusions and J the family of horn inclusions. A map
in KanComplex.W has Kan source and target, induces an equivalence of fundamental groupoids and
gives bijective based homotopy maps in every degree.

A map with right lifting against J that also belongs to W has right lifting against every member
of I. Equivalently, a weak Kan fibration lifts every compatible boundary square. The statement
is uniform in the simplicial-set universe u.
-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace SSet.modelCategoryQuillen

/-- For a simplicial map f:X→Y, assume horn right lifting, Kan source and target, an equivalence on
fundamental groupoids and bijective based homotopy maps in every degree. Then f has right
lifting against every boundary inclusion. This is the inclusion RLP(J)∩KanComplex.W⊆RLP(I) in an
arbitrary universe. -/
theorem J_rlp_inf_W_le_I_rlp :
    J.{u}.rlp ⊓ SSet.KanComplex.W.{u} ≤ I.{u}.rlp := by
  rintro X Y f ⟨hfJ, hfW⟩
  let _ : SSet.KanComplex X := hfW.kanComplex_source
  let _ : SSet.KanComplex Y := hfW.kanComplex_target
  let _ : Fibration f := (fibration_iff f).2 hfJ
  rintro _ _ _ ⟨n⟩
  exact ⟨fun _ => hfW.hasLiftingPropertyFixedTop _ _ _⟩

end SSet.modelCategoryQuillen
