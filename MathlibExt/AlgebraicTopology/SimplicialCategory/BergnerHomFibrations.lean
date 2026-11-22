/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerTwoObjectLifting
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeGeneratingFamilies

/-!
# The actual global Hom-horn right class

Every positive-dimensional horn occurs in the original two-object
generator, and lifting detects every full original Hom map, including
coincident object images. This is the Hom condition in HTT A.3.2.9(i).
Object-equivalence lifting is a separate condition.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.Bergner

/-- Fibrations of every full original Hom, on the same original object function. -/
def homFibrations : MorphismProperty Carrier.{u} :=
  fun _ _ F => ∀ x y, Fibration (F.map x y)

/-- Every original two-object positive-dimensional horn, with all horn positions. -/
def generatingHomHorns : MorphismProperty Carrier.{u} :=
  .ofHoms (fun i : Σ n : ℕ, Fin (n + 2) =>
    BergnerTwoObject.map (Λ[i.1 + 1, i.2]).ι)

instance generatingHomHorns_small : MorphismProperty.IsSmall.{u} generatingHomHorns :=
  MorphismProperty.isSmall_ofHoms _

/-- The actual family includes every dimension and every original horn position. -/
theorem homHorn_mem (n : ℕ) (i : Fin (n + 2)) :
    generatingHomHorns.{u} (BergnerTwoObject.map (Λ[n + 1, i]).ι) :=
  ⟨(⟨n, i⟩ : Σ n : ℕ, Fin (n + 2))⟩

/-- The whole original global horn lifting problems detect exactly every full Hom fibration. -/
theorem generatingHomHorns_rlp_iff {C D : Carrier.{u}} (F : C ⟶ D) :
    generatingHomHorns.rlp F ↔ homFibrations F := by
  constructor
  · intro h x y
    apply (SSet.modelCategoryQuillen.fibration_iff (F.map x y)).mpr
    intro A B i hi
    obtain ⟨n, hn⟩ := (MorphismProperty.iSup_iff _ _).mp hi
    obtain ⟨j⟩ := hn
    exact (BergnerTwoObject.hasLiftingProperty_iff F (Λ[n + 1, j]).ι).mp
      (h _ (homHorn_mem n j)) x y
  · intro h A B i hi
    obtain ⟨⟨n, j⟩⟩ := hi
    apply (BergnerTwoObject.hasLiftingProperty_iff F (Λ[n + 1, j]).ι).mpr
    intro x y
    exact (SSet.modelCategoryQuillen.fibration_iff (F.map x y)).mp (h x y) _
      ((MorphismProperty.iSup_iff _ _).mpr ⟨n, ⟨j⟩⟩)

/-- Equality of the actual whole horn right class and the original all-Hom condition. -/
theorem generatingHomHorns_rlp_eq :
    generatingHomHorns.{u}.rlp = homFibrations := by
  ext C D F
  exact generatingHomHorns_rlp_iff F

/-- The genuine left lifting class of the same full original Hom-horn right maps. -/
abbrev homHornLeft : MorphismProperty Carrier.{u} := homFibrations.llp

end CategoryTheory.SimplicialEnrichment.Bergner
