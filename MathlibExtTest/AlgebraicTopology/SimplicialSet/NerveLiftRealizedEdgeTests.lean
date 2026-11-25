/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.AlgebraicTopology.SimplicialSet.NerveLiftRealization

noncomputable section

open CategoryTheory
open scoped Simplicial

universe uC vC uD vD

namespace NerveLiftRealizedEdgeTests

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- The actual forward edge has a whole path homotopy with both original
functor-image vertices fixed for every time. -/
theorem actualForwardWholeEdge (E : C ≌ D) {x y : C} (f : x ⟶ y) :
    let p := ((TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk f))).map
      (realizedNerveEquivalence E).toFun.continuous).cast
        (realizedNerveEquivalence_vertex E x).symm
        (realizedNerveEquivalence_vertex E y).symm
    let q := TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (E.functor.map f)))
    ∃ H : Path.Homotopy p q, ∀ s : unitInterval,
      H (s, 0) = SSet.realizedVertex (ComposableArrows.mk₀ (E.functor.obj x)) ∧
      H (s, 1) = SSet.realizedVertex (ComposableArrows.mk₀ (E.functor.obj y)) := by
  let p := ((TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk f))).map
    (realizedNerveEquivalence E).toFun.continuous).cast
      (realizedNerveEquivalence_vertex E x).symm
      (realizedNerveEquivalence_vertex E y).symm
  obtain ⟨H⟩ := realizedNerveEquivalence_edge_homotopic E f
  refine ⟨H, ?_⟩
  intro s
  exact ⟨(H.eq_fst s (by simp)).trans p.source, (H.eq_fst s (by simp)).trans p.target⟩

/-- The actual inverse edge has a whole path homotopy with both original
inverse-functor vertices fixed for every time. -/
theorem actualInverseWholeEdge (E : C ≌ D) {x y : D} (f : x ⟶ y) :
    let p := ((TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk f))).map
      (realizedNerveEquivalence E).invFun.continuous).cast
        (realizedNerveEquivalence_inv_vertex E x).symm
        (realizedNerveEquivalence_inv_vertex E y).symm
    let q := TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (E.inverse.map f)))
    ∃ H : Path.Homotopy p q, ∀ s : unitInterval,
      H (s, 0) = SSet.realizedVertex (ComposableArrows.mk₀ (E.inverse.obj x)) ∧
      H (s, 1) = SSet.realizedVertex (ComposableArrows.mk₀ (E.inverse.obj y)) := by
  let p := ((TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk f))).map
    (realizedNerveEquivalence E).invFun.continuous).cast
      (realizedNerveEquivalence_inv_vertex E x).symm
      (realizedNerveEquivalence_inv_vertex E y).symm
  obtain ⟨H⟩ := realizedNerveEquivalence_inv_edge_homotopic E f
  refine ⟨H, ?_⟩
  intro s
  exact ⟨(H.eq_fst s (by simp)).trans p.source, (H.eq_fst s (by simp)).trans p.target⟩

#print axioms NerveLiftRealizedEdgeTests.actualForwardWholeEdge
#print axioms NerveLiftRealizedEdgeTests.actualInverseWholeEdge
#print axioms CategoryTheory.realizedNerveEquivalence_edge_homotopic
#print axioms CategoryTheory.realizedNerveEquivalence_inv_edge_homotopic

end NerveLiftRealizedEdgeTests

end
