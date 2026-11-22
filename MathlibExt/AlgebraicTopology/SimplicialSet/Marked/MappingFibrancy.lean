/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingFullSubcomplex
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct

/-!
# Native fibrancy of the actual minimally parameter-marked mapping complex

The actual full-vertex identification proves quasicategory fibrancy whenever
the original target carrier is a quasicategory. The markings are arbitrary;
no marked model or a replacement functor is assumed. The forgetful map to
the original internal Hom is a monomorphism and an inner fibration.
-/

noncomputable section
universe u
open CategoryTheory MonoidalClosed

namespace SSet.Marked

/-- Forgetting the marks gives the original simplicial function-object simplex. -/
def mappingComplexForget (k : ParameterMarking) (X Y : Marked.{u}) :
    mappingComplex k X Y ⟶ (ihom X.toSSet).obj Y.toSSet :=
  mappingComplexUnderlying k X Y ≫ (parameterMappingIsoIhom X.toSSet Y.toSSet).hom

/-- The actual minimal mapping complex forgets through its original full-vertex inclusion. -/
theorem mappingComplexForget_min_factor (X Y : Marked.{u}) :
    mappingComplexForget .minimal X Y =
      (mappingComplexMinFullIso X Y).hom ≫
        (Subcomplex.full (markedMappingVertices X Y)).ι ≫
          (parameterMappingIsoIhom X.toSSet Y.toSSet).hom := by
  rw [← Category.assoc, mappingComplexMinFullIso_hom_ι]
  rfl

/-- The ordinary prism complex has the original target's native quasicategory fibrancy. -/
theorem parameterMapping_quasicategory (X Y : SSet.{u}) [Quasicategory Y] :
    Quasicategory (parameterMapping X Y) := by
  let _ : Quasicategory ((ihom X).obj Y) := inferInstance
  let _ : InnerFibration (parameterMappingIsoIhom X Y).hom :=
    ⟨innerHornInclusions.rlp_of_isIso _⟩
  exact quasicategory_of_innerFibration (parameterMappingIsoIhom X Y).hom

/-- The minimally parameter-marked mapping complex is a genuine quasicategory. -/
theorem mappingComplexMin_quasicategory (X Y : Marked.{u}) [Quasicategory Y.toSSet] :
    Quasicategory (mappingComplex .minimal X Y) := by
  let _ : Quasicategory (parameterMapping X.toSSet Y.toSSet) :=
    parameterMapping_quasicategory X.toSSet Y.toSSet
  let _ : Quasicategory (Subcomplex.full (markedMappingVertices X Y) : SSet.{u}) :=
    quasicategory_of_innerFibration (Subcomplex.full (markedMappingVertices X Y)).ι
  let _ : InnerFibration (mappingComplexMinFullIso X Y).hom :=
    ⟨innerHornInclusions.rlp_of_isIso _⟩
  exact quasicategory_of_innerFibration (mappingComplexMinFullIso X Y).hom

/-- Forgetting a minimal marked mapping simplex is the native full-subcomplex inner fibration. -/
theorem mappingComplexForget_min_innerFibration (X Y : Marked.{u}) :
    InnerFibration (mappingComplexForget .minimal X Y) := by
  rw [mappingComplexForget_min_factor]
  refine ⟨innerFibrations.comp_mem _ _ (innerHornInclusions.rlp_of_isIso _) ?_⟩
  exact innerFibrations.comp_mem _ _ (InnerFibration.mem)
    (innerHornInclusions.rlp_of_isIso _)

/-- No original mapping simplex is identified with a different one by forgetting its marking. -/
theorem mappingComplexForget_min_mono (X Y : Marked.{u}) : Mono (mappingComplexForget .minimal X Y) := by
  rw [mappingComplexForget_min_factor]
  infer_instance

/-- The original target map commutes with forgetting every whole marked mapping simplex. -/
theorem mappingComplexForget_post (X : Marked.{u}) {Y Z : Marked.{u}} (p : Y ⟶ Z) :
    mappingComplexPost .minimal X p ≫ mappingComplexForget .minimal X Z =
      mappingComplexForget .minimal X Y ≫ (ihom X.toSSet).map p.hom := by
  ext n f
  change leftIhomSimplexOfPrism (f.hom ≫ p.hom) =
    ((ihom X.toSSet).map p.hom).app n (leftIhomSimplexOfPrism f.hom)
  exact (leftIhomSimplexOfPrism_post f.hom p.hom).symm

end SSet.Marked
