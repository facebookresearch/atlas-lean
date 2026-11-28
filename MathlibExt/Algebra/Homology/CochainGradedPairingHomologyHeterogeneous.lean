/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.CochainGradedPairingHomologyLaws

/-!
# Heterogeneous associativity and unit identities on homology

For natural-index module cochain complexes over a commutative ring, graded pairings may have
different intermediate and output complexes. A cycle-level associativity square with a
specified map between the two output homology objects descends to the corresponding square on
homology, retaining the tensor associator and all degree parentheses.

Likewise, a cycle-valued unit morphism from the tensor unit and a specified output comparison
map give left or right unit identities on homology when their cycle-level identities hold. The
comparison maps are arbitrary morphisms satisfying these identities.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace HomologicalComplex.CochainGradedPairing

variable (R : Type u) [CommRing R]

/-- Cycle associativity with distinct outputs descends to homology.

For pairings through `K₁₂` and `K₂₃` with outputs `L` and `R'`, fix a map `L.homology
((p+q)+r) ⟶ R'.homology (p+(q+r))`. If the two iterated cycle pairings agree after homology
projection and this map, with the tensor associator, then the two iterated homology pairings
satisfy the same associativity square. -/
theorem pairHomology_associativity
    {K₁ K₂ K₃ K₁₂ K₂₃ L R' : CochainComplex (ModuleCat.{u} R) ℕ}
    (P₁₂ : CochainGradedPairing K₁ K₂ K₁₂)
    (Pₗ : CochainGradedPairing K₁₂ K₃ L)
    (P₂₃ : CochainGradedPairing K₂ K₃ K₂₃)
    (Pᵣ : CochainGradedPairing K₁ K₂₃ R')
    (p q r : ℕ)
    (comparison : L.homology ((p + q) + r) ⟶ R'.homology (p + (q + r)))
    (hcycles :
      (P₁₂.pairCycles p q ⊗ₘ 𝟙 (K₃.cycles r)) ≫
          Pₗ.pairCycles (p + q) r ≫
          L.homologyπ ((p + q) + r) ≫ comparison =
        (α_ (K₁.cycles p) (K₂.cycles q) (K₃.cycles r)).hom ≫
          (𝟙 (K₁.cycles p) ⊗ₘ P₂₃.pairCycles q r) ≫
          Pᵣ.pairCycles p (q + r) ≫ R'.homologyπ (p + (q + r))) :
    (P₁₂.pairHomology p q ⊗ₘ 𝟙 (K₃.homology r)) ≫
        Pₗ.pairHomology (p + q) r ≫ comparison =
      (α_ (K₁.homology p) (K₂.homology q) (K₃.homology r)).hom ≫
        (𝟙 (K₁.homology p) ⊗ₘ P₂₃.pairHomology q r) ≫
        Pᵣ.pairHomology p (q + r) := by
  apply ModuleCat.MonoidalCategory.tensor_ext₃'
  intro x y z
  obtain ⟨x₀, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (K₁.homologyπ p)).mp inferInstance x
  obtain ⟨y₀, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (K₂.homologyπ q)).mp inferInstance y
  obtain ⟨z₀, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (K₃.homologyπ r)).mp inferInstance z
  change comparison.hom
      ((Pₗ.pairHomology (p + q) r).hom
        ((P₁₂.pairHomology p q).hom
            ((K₁.homologyπ p).hom x₀ ⊗ₜ[R] (K₂.homologyπ q).hom y₀) ⊗ₜ[R]
          (K₃.homologyπ r).hom z₀)) =
    (Pᵣ.pairHomology p (q + r)).hom
      ((K₁.homologyπ p).hom x₀ ⊗ₜ[R]
        (P₂₃.pairHomology q r).hom
          ((K₂.homologyπ q).hom y₀ ⊗ₜ[R] (K₃.homologyπ r).hom z₀))
  rw [pairHomology_π_apply R P₁₂, pairHomology_π_apply R Pₗ,
    pairHomology_π_apply R P₂₃, pairHomology_π_apply R Pᵣ]
  have h := ConcreteCategory.congr_hom hcycles ((x₀ ⊗ₜ[R] y₀) ⊗ₜ[R] z₀)
  exact h

/-- Heterogeneous left cycle unit descends to a homology unit.

For a pairing `U × K → L`, a map from the tensor unit to `U.cycles 0`, and a comparison
`L.homology (0+q) → K.homology q`, suppose the cycle-level composite equals the left unitor
followed by homology projection. Then the induced homology unit class satisfies the
corresponding left-unit identity. -/
theorem pairHomology_left_unit
    {U K L : CochainComplex (ModuleCat.{u} R) ℕ}
    (P : CochainGradedPairing U K L) (q : ℕ)
    (unitCycles : 𝟙_ (ModuleCat.{u} R) ⟶ U.cycles 0)
    (comparison : L.homology (0 + q) ⟶ K.homology q)
    (hcycles :
      (unitCycles ▷ K.cycles q) ≫ P.pairCycles 0 q ≫
          L.homologyπ (0 + q) ≫ comparison =
        (λ_ (K.cycles q)).hom ≫ K.homologyπ q) :
    ((unitCycles ≫ U.homologyπ 0) ▷ K.homology q) ≫
        P.pairHomology 0 q ≫ comparison =
      (λ_ (K.homology q)).hom := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a y
  change R at a
  obtain ⟨y₀, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (K.homologyπ q)).mp inferInstance y
  change comparison.hom
      ((P.pairHomology 0 q).hom
        ((U.homologyπ 0).hom (unitCycles.hom a) ⊗ₜ[R]
          (K.homologyπ q).hom y₀)) =
    a • (K.homologyπ q).hom y₀
  rw [pairHomology_π_apply R P]
  have h := ConcreteCategory.congr_hom hcycles (a ⊗ₜ[R] y₀)
  change comparison.hom
      ((L.homologyπ (0 + q)).hom
        ((P.pairCycles 0 q).hom (unitCycles.hom a ⊗ₜ[R] y₀))) =
    (K.homologyπ q).hom (a • y₀) at h
  simpa using h

/-- Heterogeneous right cycle unit descends to a homology unit.

For a pairing `K × U → L`, a map from the tensor unit to `U.cycles 0`, and a comparison
`L.homology (p+0) → K.homology p`, a cycle-level right-unit identity descends to the right
unitor identity on homology. -/
theorem pairHomology_right_unit
    {K U L : CochainComplex (ModuleCat.{u} R) ℕ}
    (P : CochainGradedPairing K U L) (p : ℕ)
    (unitCycles : 𝟙_ (ModuleCat.{u} R) ⟶ U.cycles 0)
    (comparison : L.homology (p + 0) ⟶ K.homology p)
    (hcycles :
      (K.cycles p ◁ unitCycles) ≫ P.pairCycles p 0 ≫
          L.homologyπ (p + 0) ≫ comparison =
        (ρ_ (K.cycles p)).hom ≫ K.homologyπ p) :
    (K.homology p ◁ (unitCycles ≫ U.homologyπ 0)) ≫
        P.pairHomology p 0 ≫ comparison =
      (ρ_ (K.homology p)).hom := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x a
  change R at a
  obtain ⟨x₀, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (K.homologyπ p)).mp inferInstance x
  change comparison.hom
      ((P.pairHomology p 0).hom
        ((K.homologyπ p).hom x₀ ⊗ₜ[R]
          (U.homologyπ 0).hom (unitCycles.hom a))) =
    a • (K.homologyπ p).hom x₀
  rw [pairHomology_π_apply R P]
  have h := ConcreteCategory.congr_hom hcycles (x₀ ⊗ₜ[R] a)
  change comparison.hom
      ((L.homologyπ (p + 0)).hom
        ((P.pairCycles p 0).hom (x₀ ⊗ₜ[R] unitCycles.hom a))) =
    (K.homologyπ p).hom (a • x₀) at h
  simpa using h

end HomologicalComplex.CochainGradedPairing
