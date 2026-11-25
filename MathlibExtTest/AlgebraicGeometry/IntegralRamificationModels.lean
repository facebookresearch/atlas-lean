/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.IntegralRamificationModels
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public noncomputable section

open MathlibExt.AlgebraicGeometry.IntegralRamificationModels

namespace IntegralRamificationModelsTest

variable (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [FiniteDimensional K L] [IsGalois K L]
  {κ V : Type*} [Field κ] [AddCommGroup V] [Module κ V] [Module.Finite κ V]
  (ρ : Gal(L/K) →* Module.End κ V)

omit [FiniteDimensional K L] [IsGalois K L] [Module.Finite κ V] in
/-- The trivial subgroup fixes every vector. -/
theorem invariants_bot :
    Representation.invariants (ρ.comp (⊥ : Subgroup Gal(L/K)).subtype) = ⊤ := by
  ext v
  simp only [Submodule.mem_top, iff_true, Representation.mem_invariants]
  intro g
  obtain ⟨g, hg⟩ := g
  rw [Subgroup.mem_bot] at hg
  subst hg
  simp

/-- Hence the trivial subgroup has codimension zero. -/
example : fixedCodimension K L ρ ⊥ = 0 := by
  rw [fixedCodimension, invariants_bot, finrank_top, Nat.sub_self]

/-- Codimension is the drop of dimension: a nontrivial vector moved by `H`
leaves a proper fixed space, so the codimension is positive. -/
example (H : Subgroup Gal(L/K)) (g : H) (v : V) (hv : ρ g.val v ≠ v) :
    0 < fixedCodimension K L ρ H := by
  have hne : Representation.invariants (ρ.comp H.subtype) ≠ ⊤ := fun h ↦
    hv ((Representation.mem_invariants (ρ.comp H.subtype) v).mp (h ▸ Submodule.mem_top) g)
  have := Submodule.finrank_lt hne
  rw [fixedCodimension]
  omega

/-- The trivial representation has Swan conductor zero, for every cut. -/
example [IsDiscreteValuationRing (Integers R L)] {A : IntegralAction R K L}
    (Q : QuotientActions R K L A) (N : FiniteCut R K L Q) :
    swan R K L (1 : Gal(L/K) →* Module.End κ V) Q N = 0 := by
  have h (H : Subgroup Gal(L/K)) :
      fixedCodimension K L (1 : Gal(L/K) →* Module.End κ V) H = 0 := by
    have : Representation.invariants ((1 : Gal(L/K) →* Module.End κ V).comp H.subtype) = ⊤ := by
      ext v
      simp [Representation.mem_invariants]
    rw [fixedCodimension, this, finrank_top, Nat.sub_self]
  simp [swan, h]

end IntegralRamificationModelsTest
