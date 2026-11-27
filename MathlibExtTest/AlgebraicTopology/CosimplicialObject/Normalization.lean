/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

import MathlibExt.AlgebraicTopology.CosimplicialObject.Normalization

/-!
# Cosimplicial normalization clients

These clients exercise the normalization projection and inclusion, their
retraction identity, coefficient functor comparisons and the induced maps on
cohomology. The category universes and the stated additivity or abelian
hypotheses remain independent.
-/

noncomputable section

open CategoryTheory Category Limits AlgebraicTopology

universe uC vC uD vD

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]

/-- Additivity alone carries the actual normalization projection to a quasi-isomorphism. -/
private theorem additive_original_cochain_projection_quasiIso
    (F : C ⥤ D) [F.Additive] (X : CosimplicialObject C) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((normalizedCofaceMapProjection C).app X)) := by
  let p := (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
    ((normalizedCofaceMapProjection C).app X)
  let e := (normalizedCofaceCompMapIso C F).app X
  have hp : p ≫ e.hom = (alternatingCofaceCompMapIso C F).hom.app X ≫
      (normalizedCofaceMapProjection D).app
        (((CosimplicialObject.whiskering C D).obj F).obj X) :=
    normalizedCofaceCompMapIso_projection C F X
  haveI : QuasiIso (p ≫ e.hom) := by
    rw [hp]
    infer_instance
  exact quasiIso_of_comp_right p e.hom

/-- The actual codegenerate-projector kernel includes by the native normalization quasi-iso. -/
private theorem actual_codegenerate_kernel_inclusion_quasiIso (X : CosimplicialObject C) :
    QuasiIso (kernel.ι ((codegenerateCofaceProjector C).app X)) := by
  rw [← normalizedCofaceKernelIso_hom_inclusion C X]
  infer_instance
