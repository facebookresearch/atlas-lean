/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.GeneratedByCoreflectionWeakHomotopy
public import MathlibExt.Topology.Category.CompactlyGenerated.GeneratedByCounit
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

/-!
# Singular invariance of compact generation

Applying the singular functor to the counit of the compact-generation
coreflection gives an isomorphism. Consequently, the counit is a weak
homotopy equivalence.

The proof specializes the generator-independent result for generated
topologies to compact Hausdorff probes and uses the exact transported-counit
factorization.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology

universe u v

namespace TopCat

private theorem standardSimplex_isGeneratedBy_compactHausProbes
    (n : SimplexCategoryᵒᵖ) :
    IsGeneratedBy CompactlyGenerated.compactHausProbes.{u}
      (Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))) := by
  let S := Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))
  let _ : CompactSpace S := by
    dsimp only [S]
    infer_instance
  let _ : T2Space S :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ
      (Fin (n.unop.len + 1))).t2Space
  let _ : CompactSpace (ULift.{u} S) :=
    Homeomorph.ulift.symm.compactSpace
  let _ : T2Space (ULift.{u} S) :=
    Homeomorph.ulift.symm.t2Space
  let K : CompHaus.{u} := CompHaus.of (ULift.{u} S)
  let _ : IsGeneratedBy CompactlyGenerated.compactHausProbes.{u}
      (ULift.{u} S) := by
    change IsGeneratedBy CompactlyGenerated.compactHausProbes.{u}
      (CompactlyGenerated.compactHausProbes K)
    infer_instance
  exact Homeomorph.ulift.isQuotientMap.isGeneratedBy

/-- The singular functor sends the compact-generation counit to an
isomorphism. -/
theorem toSSet_map_compactlyGeneratedAdjCounit_isIso
    (Y : TopCat.{v}) :
    IsIso (TopCat.toSSet.map
      (CompactlyGenerated.adj.{u, v}.counit.app Y)) := by
  let P := CompactlyGenerated.compactHausProbes.{u}
  let e := CompactlyGenerated.equivalenceGeneratedByTopCat.{u, v}
  let T := TopCat.toGeneratedByTopCat (X := P)
  let U := GeneratedByTopCat.toTopCat (X := P)
  let eToTop : e.functor ⋙ U ≅
      CompactlyGenerated.compactlyGeneratedToTop := Iso.refl _
  let a := eToTop.inv.app ((T ⋙ e.inverse).obj Y)
  let b := U.map (e.counitIso.hom.app (T.obj Y))
  let c := (GeneratedByTopCat.adjCounit (X := P)).app Y
  let _ : IsIso (TopCat.toSSet.map
      a) := inferInstance
  let _ : IsIso (TopCat.toSSet.map b) := inferInstance
  let _ : IsIso (TopCat.toSSet.map c) :=
    TopCat.toSSet_map_generatedByAdjCounit_isIso P
      standardSimplex_isGeneratedBy_compactHausProbes Y
  have hCounit : CompactlyGenerated.adj.{u, v}.counit.app Y =
      a ≫ b ≫ c := by
    simpa only [a, b, c] using
      (@CompactlyGenerated.adj_counit_app_eq_generatedBy.{u, v} Y)
  have hcomp : IsIso (TopCat.toSSet.map (a ≫ b ≫ c)) := by
    rw [TopCat.toSSet.map_comp, TopCat.toSSet.map_comp]
    infer_instance
  exact (congrArg (fun q => IsIso (TopCat.toSSet.map q)) hCounit).symm.mp hcomp

end TopCat

namespace CompactlyGenerated

/-- The compact-generation counit is a weak homotopy equivalence. -/
theorem adjCounit_mem_weakHomotopyEquivalences
    (Y : TopCat.{v}) :
    TopCat.weakHomotopyEquivalences
      (CompactlyGenerated.adj.{u, v}.counit.app Y) := by
  rw [TopCat.mem_weakHomotopyEquivalences_iff]
  let _ : SSet.KanComplex
      (TopCat.toSSet.obj
        ((TopCat.toCompactlyGenerated ⋙
          CompactlyGenerated.compactlyGeneratedToTop).obj Y)) :=
    TopCat.toSSet_obj_kanComplex _
  let _ : SSet.KanComplex
      (TopCat.toSSet.obj ((Functor.id (TopCat.{v})).obj Y)) :=
    TopCat.toSSet_obj_kanComplex _
  let _ : IsIso (TopCat.toSSet.map
      (CompactlyGenerated.adj.{u, v}.counit.app Y)) :=
    @TopCat.toSSet_map_compactlyGeneratedAdjCounit_isIso.{u, v} Y
  exact SSet.KanComplex.W.ofIso
    (asIso (TopCat.toSSet.map
      (CompactlyGenerated.adj.{u, v}.counit.app Y)))

end CompactlyGenerated
