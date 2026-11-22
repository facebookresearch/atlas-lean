/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.QuasicategoryFibrations
import MathlibExt.AlgebraicTopology.Quasicategory.CoreFibration

/-!
# Native function-pullback fibrations and their cores

For a monomorphism and an inner fibration with strict equivalence lifting
into a quasicategory, the original internal-Hom pullback comparison is a
categorical fibration. Its literal core map is a Kan fibration. The entire
native pullback object and both projections are retained.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed
open scoped Simplicial

namespace SSet

/-- The original function-pullback target is a quasicategory. -/
theorem pullbackObjObj_quasicategory {A D E B : SSet.{u}}
    (i : A ⟶ D) [Mono i] (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    (sq : MonoidalClosed.internalHom.PullbackObjObj i p) : Quasicategory sq.pt := by
  let _ : Quasicategory E := quasicategory_of_innerFibration p
  let _ : InnerFibration ((pre i).app B) :=
    (categoricalFibrations_iff_innerFibration_and_hasStrictEquivalenceLifting
      ((pre i).app B)).mp (categoricalFibrations_pre_app_of_mono i B) |>.1
  let _ : InnerFibration ((internalHom.map i.op).app B) := by
    change InnerFibration ((pre i).app B)
    infer_instance
  let _ : Quasicategory ((internalHom.obj (Opposite.op A)).obj E) := by
    change Quasicategory ((ihom A).obj E)
    infer_instance
  let _ : InnerFibration sq.fst :=
    ⟨innerFibrations.of_isPullback sq.isPullback.flip InnerFibration.mem⟩
  exact quasicategory_of_innerFibration sq.fst

/-- The actual function-pullback comparison lies in the genuine categorical right class. -/
theorem categoricalFibrations_pullbackObjObjπ {A D E B : SSet.{u}}
    (i : A ⟶ D) [Mono i] (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    [HasStrictEquivalenceLifting p]
    (sq : MonoidalClosed.internalHom.PullbackObjObj i p) : categoricalFibrations sq.π := by
  let _ : Quasicategory sq.pt := pullbackObjObj_quasicategory i p sq
  let _ : InnerFibration sq.π := innerFibration_pullbackObjObjπ sq
  exact (categoricalFibrations_iff_innerFibration_and_hasStrictEquivalenceLifting sq.π).mpr
    ⟨inferInstance, hasStrictEquivalenceLifting_pullbackObjObjπ sq⟩

open scoped SSet.modelCategoryQuillen in
/-- Taking the literal native core of the function-pullback comparison gives a Kan fibration. -/
theorem fibration_core_pullbackObjObjπ {A D E B : SSet.{u}}
    (i : A ⟶ D) [Mono i] (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    [HasStrictEquivalenceLifting p]
    (sq : MonoidalClosed.internalHom.PullbackObjObj i p) :
    HomotopicalAlgebra.Fibration (core.map sq.π) := by
  let _ : Quasicategory sq.pt := pullbackObjObj_quasicategory i p sq
  let _ : InnerFibration sq.π := innerFibration_pullbackObjObjπ sq
  let _ : HasStrictEquivalenceLifting sq.π := hasStrictEquivalenceLifting_pullbackObjObjπ sq
  exact fibration_core_map_of_hasStrictEquivalenceLifting sq.π

end SSet
