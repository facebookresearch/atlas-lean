/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeGeneratingSmallObject

/-!
# Actual free boundary and horn factorizations on the original enriched carrier

The genuine small-object construction factors each whole original map
through an enrichment with the same object labels. The left maps are
actual relative cell complexes. The right maps have the proved scalar
Hom lifting properties on the same original carrier.
No weakness of the left horn cell complexes or enriched model transfer
is asserted here.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FreeFactorization

variable {O : Type u}

/-- The actual countable free boundary small-object factorization functor. -/
def boundaryData : MorphismProperty.FunctorialFactorizationData
    (boundaryFamily O).rlp.llp (boundaryFamily O).rlp :=
  SmallObject.functorialFactorizationData (boundaryFamily O) Cardinal.aleph0.{u}

/-- The actual countable free horn small-object factorization functor. -/
def hornData : MorphismProperty.FunctorialFactorizationData
    (hornFamily O).rlp.llp (hornFamily O).rlp :=
  SmallObject.functorialFactorizationData (hornFamily O) Cardinal.aleph0.{u}

/-- Factor the entire original fixed-object map by the actual free boundary construction. -/
abbrev boundary {C D : FixedObjects O} (p : C ⟶ D) := boundaryData.factorizationData p

/-- Factor the entire original fixed-object map by the actual free horn construction. -/
abbrev horn {C D : FixedObjects O} (p : C ⟶ D) := hornData.factorizationData p

/-- Both actual boundary-factorization maps compose to the same supplied original map. -/
theorem boundary_fac {C D : FixedObjects O} (p : C ⟶ D) :
    (boundary p).i ≫ (boundary p).p = p := (boundary p).fac

/-- Both actual horn-factorization maps compose to the same supplied original map. -/
theorem horn_fac {C D : FixedObjects O} (p : C ⟶ D) :
    (horn p).i ≫ (horn p).p = p := (horn p).fac

/-- The boundary left map is the actual relative free cell complex, with all zero and loop cells retained. -/
def boundaryCells {C D : FixedObjects O} (p : C ⟶ D) :
    RelativeCellComplex.{u}
      (fun (_ : Cardinal.aleph0.{u}.ord.ToType) => (boundaryFamily O).homFamily) (boundary p).i :=
  SmallObject.relativeCellComplexιObj (boundaryFamily O) Cardinal.aleph0.{u} p

/-- The horn left map is the actual relative free cell complex on the same original labels. -/
def hornCells {C D : FixedObjects O} (p : C ⟶ D) :
    RelativeCellComplex.{u}
      (fun (_ : Cardinal.aleph0.{u}.ord.ToType) => (hornFamily O).homFamily) (horn p).i :=
  SmallObject.relativeCellComplexιObj (hornFamily O) Cardinal.aleph0.{u} p

/-- Every original boundary right-leg Hom map is a genuine scalar trivial fibration. -/
theorem boundary_p_original {C D : FixedObjects O} (p : C ⟶ D)
    (a b : (boundary p).Z.val) :
    Fibration ((boundary p).p.val.map a b) ∧
      SSet.realizationWeakEquivalences ((boundary p).p.val.map a b) := by
  have h := congrArg (fun W : MorphismProperty (FixedObjects O) => W (boundary p).p)
    (boundaryFamily_rlp_eq (O := O))
  exact (boundaryGenerators_rlp_iff_original (boundary p).p).mp (h.mp (boundary p).hp) a b

/-- Every original horn right-leg Hom map is a genuine scalar fibration. -/
theorem horn_p_original {C D : FixedObjects O} (p : C ⟶ D)
    (a b : (horn p).Z.val) : Fibration ((horn p).p.val.map a b) := by
  have h := congrArg (fun W : MorphismProperty (FixedObjects O) => W (horn p).p)
    (hornFamily_rlp_eq (O := O))
  exact (hornGenerators_rlp_iff_original (horn p).p).mp (h.mp (horn p).hp) a b

/-- The actual boundary factorization retains every original scalar Hom map through both whole legs. -/
theorem boundary_hom_fac {C D : FixedObjects O} (p : C ⟶ D) (x y : O) :
    homMap (boundary p).i x y ≫ homMap (boundary p).p x y = homMap p x y := by
  have h := congrArg (fun f : C ⟶ D => homMap f x y) (boundary_fac p)
  rw [homMap_comp] at h
  exact h

/-- The actual horn factorization retains every original scalar Hom map through both whole legs. -/
theorem horn_hom_fac {C D : FixedObjects O} (p : C ⟶ D) (x y : O) :
    homMap (horn p).i x y ≫ homMap (horn p).p x y = homMap p x y := by
  have h := congrArg (fun f : C ⟶ D => homMap f x y) (horn_fac p)
  rw [homMap_comp] at h
  exact h

end CategoryTheory.SimplicialEnrichment.FixedObjects.FreeFactorization
