/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.LinearAlgebra.Filtration.Exactness

/-!
# Tests for actual filtration quotient maps and finite descent

The first positive stage is the full integer module. The tests compute a
nonidentity quotient map, transfer exactness from the actual quotient maps,
and check that a nonzero initial stage cannot satisfy the transfer theorem.
-/

@[expose] public section

namespace FiltrationExactnessTests

private def oneStage (p : ℕ) : Submodule ℤ ℤ := if p = 0 then ⊥ else ⊤

private theorem identity_preserves :
    ∀ p, ∀ x ∈ oneStage p, (LinearMap.id : ℤ →ₗ[ℤ] ℤ) x ∈ oneStage p := by
  intro p x hx
  exact hx

private theorem zero_preserves :
    ∀ p, ∀ x ∈ oneStage p, (0 : ℤ →ₗ[ℤ] ℤ) x ∈ oneStage p := by
  intro p x hx
  exact (oneStage p).zero_mem

private theorem quotient_identity (p : ℕ) :
    (LinearMap.id : ℤ →ₗ[ℤ] ℤ).filtrationLayerMap
      oneStage oneStage identity_preserves p = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (Submodule.filtrationLower oneStage p) x
  rfl

private theorem quotient_zero (p : ℕ) :
    (0 : ℤ →ₗ[ℤ] ℤ).filtrationLayerMap oneStage oneStage zero_preserves p = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (Submodule.filtrationLower oneStage p) x
  rfl

private theorem quotient_exact (p : ℕ) :
    LinearMap.range ((LinearMap.id : ℤ →ₗ[ℤ] ℤ).filtrationLayerMap
      oneStage oneStage identity_preserves p) =
      LinearMap.ker ((0 : ℤ →ₗ[ℤ] ℤ).filtrationLayerMap
        oneStage oneStage zero_preserves p) := by
  rw [quotient_identity, quotient_zero]
  simp

/-- A genuine exhaustive filtration transfers exactness of its actual quotient maps. -/
theorem integer_exactness_from_quotients :
    LinearMap.range (LinearMap.id : ℤ →ₗ[ℤ] ℤ) = LinearMap.ker (0 : ℤ →ₗ[ℤ] ℤ) := by
  exact LinearMap.range_eq_ker_of_exact_filtrationLayers
    LinearMap.id 0 oneStage oneStage oneStage identity_preserves zero_preserves
    (by simp) (by simp [oneStage]) (fun z => ⟨1, by simp [oneStage]⟩) quotient_exact

private def doubling : ℤ →ₗ[ℤ] ℤ := (2 : ℤ) • LinearMap.id

private theorem doubling_preserves :
    ∀ p, ∀ x ∈ oneStage p, doubling x ∈ oneStage p := by
  intro p x hx
  by_cases hp : p = 0
  · have hx0 : x = 0 := by simpa [oneStage, hp] using hx
    subst x
    simp [oneStage, hp]
  · simp [oneStage, hp]

/-- The quotient map is the original doubling map, including its nonzero value. -/
private theorem quotient_doubling_five :
    LinearMap.filtrationLayerMap doubling oneStage oneStage doubling_preserves 0
        (Submodule.Quotient.mk (⟨5, by simp [oneStage]⟩ : oneStage 1)) =
      Submodule.Quotient.mk (⟨10, by simp [oneStage]⟩ : oneStage 1) := by
  rw [LinearMap.filtrationLayerMap_mkQ]
  rfl

private theorem constant_top_quotient_zero (p : ℕ)
    (q : Submodule.FiltrationLayer (fun _ => (⊤ : Submodule ℤ ℤ)) p) : q = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (Submodule.filtrationLower (fun _ => (⊤ : Submodule ℤ ℤ)) p) q
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Submodule.mem_top

/-- Zero initial stage is a necessary condition: constant-top layers alone give no exactness. -/
theorem nonzero_initial_stage_counterexample :
    (∀ p, ∀ q : Submodule.FiltrationLayer (fun _ => (⊤ : Submodule ℤ ℤ)) p, q = 0) ∧
      LinearMap.range (0 : ℤ →ₗ[ℤ] ℤ) ≠ LinearMap.ker (0 : ℤ →ₗ[ℤ] ℤ) := by
  refine ⟨constant_top_quotient_zero, ?_⟩
  intro h
  have hmem : (1 : ℤ) ∈ LinearMap.range (0 : ℤ →ₗ[ℤ] ℤ) := by
    rw [h]
    simp
  rw [LinearMap.range_zero] at hmem
  exact Int.one_ne_zero hmem

end FiltrationExactnessTests
