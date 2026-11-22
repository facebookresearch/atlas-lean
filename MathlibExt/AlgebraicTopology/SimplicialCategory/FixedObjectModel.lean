/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectHornAcyclicity
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLimitEvaluation
import MathlibExt.AlgebraicTopology.ModelCategory.OriginalGeneratedModel
import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-!
# The genuine fixed-object simplicial-category model structure

The actual original Hom weak class, free-horn fibration class and
free-boundary cofibration class satisfy all model axioms. The original
word-filtration acyclicity and the two genuine free small-object weak
factorization systems prove both intersections and factorizations.
This model fixes every original object label; no changing-object
Bergner model or unrestricted coherent-nerve Quillen claim is made.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FixedObjectModel

variable (O : Type u)

/-- The actual fixed-object model, with scalar Hom weak maps and genuine free boundary/horn factorizations. -/
@[instance_reducible]
def modelCategory : ModelCategory (FixedObjects O) := by
  let _ : HasFiniteLimits (FixedObjects O) := { out _J _ _ := inferInstance }
  let _ : HasFiniteColimits (FixedObjects O) := { out _J _ _ := inferInstance }
  exact OriginalGeneratedModel.modelCategory
    (boundaryFamily O) (hornFamily O) (weakEquivalences O)
    (weak_twoOutOfThree (O := O)) (trivialFibrations_eq (O := O))
    (trivialCofibrations_le_weakEquivalences (O := O))
    (FreeFactorization.boundaryData (O := O)) (FreeFactorization.hornData (O := O))

variable {O}

/-- The genuine model weak class reads the same entire original Hom maps at every individual source vertex. -/
theorem weakEquivalence_iff_original {C D : FixedObjects O} (f : C ⟶ D) :
    let _ : ModelCategory (FixedObjects O) := modelCategory O
    WeakEquivalence f ↔ ∀ a b : C.val, SSet.realizationWeakEquivalences (f.val.map a b) := by
  dsimp only
  rw [HomotopicalAlgebra.weakEquivalence_iff]
  exact weakEquivalences_original_iff f

/-- Model fibrations are precisely genuine scalar Kan fibrations on the same whole original Hom maps. -/
theorem fibration_iff_original {C D : FixedObjects O} (f : C ⟶ D) :
    let _ : ModelCategory (FixedObjects O) := modelCategory O
    Fibration f ↔ ∀ a b : C.val, Fibration (f.val.map a b) := by
  dsimp only
  rw [HomotopicalAlgebra.fibration_iff]
  change (hornFamily O).rlp f ↔ _
  rw [hornFamily_rlp_eq]
  exact hornGenerators_rlp_iff_original f

/-- Model cofibrations are the actual free-boundary left lifting class on the unchanged original labels. -/
theorem cofibration_iff_freeBoundary {C D : FixedObjects O} (f : C ⟶ D) :
    let _ : ModelCategory (FixedObjects O) := modelCategory O
    Cofibration f ↔ (boundaryFamily O).rlp.llp f := by
  dsimp only
  rw [HomotopicalAlgebra.cofibration_iff]
  rfl

/-- Model trivial cofibrations are exactly the actual free-horn left lifting class, not an assumed
  acyclicity condition. -/
theorem trivialCofibration_iff_freeHorn {C D : FixedObjects O} (f : C ⟶ D) :
    let _ : ModelCategory (FixedObjects O) := modelCategory O
    (Cofibration f ∧ WeakEquivalence f) ↔ (hornFamily O).rlp.llp f := by
  dsimp only
  rw [HomotopicalAlgebra.cofibration_iff, HomotopicalAlgebra.weakEquivalence_iff]
  change (cofibrations O ⊓ weakEquivalences O) f ↔ trivialCofibrations O f
  rw [trivialCofibrations_eq]

end CategoryTheory.SimplicialEnrichment.FixedObjects.FixedObjectModel
