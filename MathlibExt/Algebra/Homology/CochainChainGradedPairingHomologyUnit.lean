/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Algebra.Homology.CochainChainGradedPairingHomology
public import MathlibExt.Algebra.Homology.LinearHomCochainChainPairingAssociativity

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory MonoidalCategory Opposite

universe u

namespace HomologicalComplex.CochainChainGradedPairing

variable (R : Type u) [CommRing R]

/-- A pair-level left-unit identity for a cochain-chain pairing descends to homology. -/
theorem pairHomology_left_unit_of_pair
    {U : CochainComplex (ModuleCat.{u} R) ℕ}
    {K : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CochainChainGradedPairing U K K) (q : ℕ)
    (unitCycles : 𝟙_ (ModuleCat.{u} R) ⟶ U.cycles 0)
    (inputX : K.X q ⟶ K.X (0 + q))
    (inputCycles : K.cycles q ⟶ K.cycles (0 + q))
    (inputHomology : K.homology q ⟶ K.homology (0 + q))
    (inputCycles_i : inputCycles ≫ K.iCycles (0 + q) =
      K.iCycles q ≫ inputX)
    (input_π : K.homologyπ q ≫ inputHomology =
      inputCycles ≫ K.homologyπ (0 + q))
    (hpair :
      ((unitCycles ≫ U.iCycles 0) ▷ K.X q) ≫
          (𝟙 (U.X 0) ⊗ₘ inputX) ≫ P.pair 0 q =
        (λ_ (K.X q)).hom) :
    ((unitCycles ≫ U.homologyπ 0) ▷ K.homology q) ≫
        (𝟙 (U.homology 0) ⊗ₘ inputHomology) ≫ P.pairHomology 0 q =
      (λ_ (K.homology q)).hom := by
  have hcycles :
      (unitCycles ▷ K.cycles q) ≫
          (𝟙 (U.cycles 0) ⊗ₘ inputCycles) ≫ P.pairCycles 0 q =
        (λ_ (K.cycles q)).hom := by
    apply (cancel_mono (K.iCycles q)).1
    simp only [Category.assoc]
    rw [P.pairCycles_i]
    slice_lhs 2 3 =>
      rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.id_comp]
    rw [inputCycles_i]
    rw [MonoidalCategory.whiskerRight_comp_tensorHom_assoc]
    have htensor :
        ((unitCycles ≫ U.iCycles 0) ⊗ₘ (K.iCycles q ≫ inputX)) =
          (((𝟙_ (ModuleCat.{u} R)) ◁ K.iCycles q) ≫
            ((unitCycles ≫ U.iCycles 0) ▷ K.X q) ≫
            (𝟙 (U.X 0) ⊗ₘ inputX)) := by
      calc
        _ = ((unitCycles ≫ U.iCycles 0) ⊗ₘ K.iCycles q) ≫
            (𝟙 (U.X 0) ⊗ₘ inputX) := by
          rw [MonoidalCategory.tensorHom_comp_tensorHom]
          simp
        _ = _ := by
          rw [MonoidalCategory.tensorHom_def]
          simp only [← Category.assoc]
          rw [MonoidalCategory.whisker_exchange]
    rw [htensor]
    simp only [Category.assoc]
    rw [hpair]
    exact MonoidalCategory.leftUnitor_naturality (K.iCycles q)
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a y
  change R at a
  obtain ⟨y₀, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (K.homologyπ q)).mp inferInstance y
  change (P.pairHomology 0 q).hom
      ((U.homologyπ 0).hom (unitCycles.hom a) ⊗ₜ[R]
        inputHomology.hom ((K.homologyπ q).hom y₀)) =
    a • (K.homologyπ q).hom y₀
  have hinput := ConcreteCategory.congr_hom input_π y₀
  change inputHomology.hom ((K.homologyπ q).hom y₀) =
    (K.homologyπ (0 + q)).hom (inputCycles.hom y₀) at hinput
  rw [hinput, pairHomology_π_apply R]
  have h := ConcreteCategory.congr_hom hcycles (a ⊗ₜ[R] y₀)
  change (P.pairCycles 0 q).hom
      (unitCycles.hom a ⊗ₜ[R] inputCycles.hom y₀) = a • y₀ at h
  rw [h, map_smul]

end HomologicalComplex.CochainChainGradedPairing

end
