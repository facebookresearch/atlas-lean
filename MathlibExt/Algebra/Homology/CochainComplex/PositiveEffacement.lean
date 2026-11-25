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

public import MathlibExt.Algebra.Homology.HomotopyCofiber.Homology
public import MathlibExt.CategoryTheory.Functor.Effaceable

/-!
# Effacement of positive cochain cohomology

The inclusion into the identity cofiber is split monic in each degree
and kills cohomology in degrees with a predecessor. For nonnegative
cochains this gives positive-degree effacement. The degree-zero term is
retained.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Cofiber of the identity cochain map. -/
def positiveEffacement (K : CochainComplex C ℕ) [HasHomotopyCofiber (𝟙 K)] :
    CochainComplex C ℕ :=
  homotopyCofiber (𝟙 K)

/-- Canonical inclusion into the identity cofiber. -/
def positiveEffacementMap (K : CochainComplex C ℕ) [HasHomotopyCofiber (𝟙 K)] :
    K ⟶ positiveEffacement K :=
  homotopyCofiber.inr (𝟙 K)

/-- Degreewise retractions of the cofiber inclusion. -/
theorem positiveEffacementMap_mono (K : CochainComplex C ℕ)
    [HasHomotopyCofiber (𝟙 K)] :
    Mono (positiveEffacementMap K) :=
  homotopyCofiber.mono_inr (𝟙 K)

/-- The cofiber inclusion kills positive cohomology under local homology assumptions. -/
theorem positiveEffacementMap_homology_succ_eq_zero (K : CochainComplex C ℕ) (n : ℕ)
    [HasHomotopyCofiber (𝟙 K)]
    [K.HasHomology (n + 1)] [(positiveEffacement K).HasHomology (n + 1)] :
    homologyMap (positiveEffacementMap K) (n + 1) = 0 := by
  rename_i hCF hK hE
  change (homotopyCofiber (𝟙 K)).HasHomology (n + 1) at hE
  letI : (homotopyCofiber (𝟙 K)).HasHomology (n + 1) := hE
  change homologyMap (homotopyCofiber.inr (𝟙 K)) (n + 1) = 0
  rw [← Category.id_comp (homotopyCofiber.inr (𝟙 K))]
  exact @homotopyCofiber.homologyMap_comp_inr_eq_zero C _ _ ℕ (ComplexShape.up ℕ) _
    K K (𝟙 K) hCF n (n + 1) (by rfl) hK hE

/-- Positive cochain cohomology is effaceable. -/
theorem homologyFunctor_isEffaceable_succ
    [HasBinaryBiproducts C] [CategoryWithHomology C] (n : ℕ) :
    (homologyFunctor C (ComplexShape.up ℕ) (n + 1)).IsEffaceable := by
  intro K
  exact ⟨positiveEffacement K, positiveEffacementMap K,
    positiveEffacementMap_mono K, positiveEffacementMap_homology_succ_eq_zero K n⟩

end CochainComplex
