/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizedCompStruct

/-!
# Realized inverse edges in a category nerve

For an isomorphism in a category, the realized edge of its inverse is
homotopic to the reverse of its realized forward edge. Composition and
identity edges in the nerve supply the path homotopies for the given
isomorphism.
-/

@[expose] public section

universe u v

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial Topology

namespace CategoryTheory

section Part1

private theorem inverse_path_of_null_composite {Y : Type*} [TopologicalSpace Y]
    {x y : Y} (p : Path x y) (q : Path y x)
    (h : (p.trans q).Homotopic (Path.refl x)) : p.Homotopic q.symm := by
  exact (Path.Homotopic.trans_refl p).symm.trans
    (((Path.Homotopic.refl p).hcomp (Path.Homotopic.trans_symm q).symm).trans
      ((Path.Homotopic.trans_assoc p q q.symm).symm.trans
        ((h.hcomp (Path.Homotopic.refl q.symm)).trans (Path.Homotopic.refl_trans q.symm))))

/-- The inverse categorical edge realizes to the endpoint-fixed reverse-edge path class. -/
theorem realizedIso_inv_path {D : Type u} [Category.{v} D] {x y : D} (e : x ≅ y) :
    (TopCat.pathEquiv (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk e.inv))).Homotopic
      (TopCat.pathEquiv (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk e.hom))).symm := by
  obtain ⟨hc⟩ := (CategoryTheory.nerve.nonempty_compStruct_iff
    e.inv e.hom (𝟙 y)).mpr e.inv_hom_id
  have hComp := SSet.realizedCompStructHomotopic hc
  have hId := SSet.realizedEdgePath_id_homotopic (X := nerve D) (nerveEquiv.symm y)
  have hNull :
      ((TopCat.pathEquiv (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk e.inv))).trans
        (TopCat.pathEquiv (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk e.hom)))).Homotopic
          (Path.refl (SSet.realizedVertex (X := nerve D) (nerveEquiv.symm y))) := by
    exact hComp.symm.trans (by simpa only [CategoryTheory.nerve.edgeMk_id] using hId)
  exact inverse_path_of_null_composite _ _ hNull

end Part1

end CategoryTheory

end
