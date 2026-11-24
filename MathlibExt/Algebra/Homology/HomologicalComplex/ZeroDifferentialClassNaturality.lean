/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ZeroDifferentialHomology

/-!
# Naturality of actual classes in zero-differential complexes

The original cycle-class map is the inverse of the earned native homology
coordinate isomorphism. Its naturality follows from the actual middle-map
naturality of those homology coordinates.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {ι : Type w} {c : ComplexShape ι}

/-- The actual cycle-class map is the inverse of the computed zero-map
homology isomorphism. -/
theorem zeroDifferentialClassMap_eq_inv (K : HomologicalComplex C c) (i : ι)
    [K.HasHomology i] (hK : ∀ j k, K.d j k = 0) :
    zeroDifferentialClassMap K i hK = (zeroDifferentialHomologyIso K i hK).inv := by
  apply (cancel_mono (zeroDifferentialHomologyIso K i hK).hom).1
  rw [zeroDifferentialClassMap_homologyIso, Iso.inv_hom_id]

/-- Actual middle elements and actual homology classes have the native
naturality square for a map of zero-differential complexes. -/
@[reassoc]
theorem zeroDifferentialClassMap_naturality {K L : HomologicalComplex C c}
    (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    (hK : ∀ j k, K.d j k = 0) (hL : ∀ j k, L.d j k = 0) :
    zeroDifferentialClassMap K i hK ≫ homologyMap f i =
      f.f i ≫ zeroDifferentialClassMap L i hL := by
  rw [zeroDifferentialClassMap_eq_inv, zeroDifferentialClassMap_eq_inv]
  apply (cancel_mono (zeroDifferentialHomologyIso L i hL).hom).1
  rw [Category.assoc, zeroDifferentialHomologyIso_naturality f i hK hL,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

end HomologicalComplex
