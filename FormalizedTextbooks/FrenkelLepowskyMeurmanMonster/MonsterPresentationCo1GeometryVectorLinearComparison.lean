/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A checked twenty-four-point source span and faithful image matrix certify the natural kernel. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryUniversalBinary
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix

/-- The coefficient map of any twenty-four-element binary-module family. -/
def monsterCo1GeometryVectorCombination {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (b : Fin 24 → V) : (Fin 24 → ZMod 2) →ₗ[ZMod 2] V where
  toFun a := ∑ j, a j • b j
  map_add' a c := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' s a := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, RingHom.id_apply]

/-- The coefficient image is exactly the span of the actual proposed source family. -/
theorem monsterCo1GeometryVectorCombination_range {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] (b : Fin 24 → V) :
    LinearMap.range (monsterCo1GeometryVectorCombination b) =
      Submodule.span (ZMod 2) (Set.range b) := by
  apply le_antisymm
  · rintro v ⟨a, rfl⟩
    change (∑ j, a j • b j) ∈ Submodule.span (ZMod 2) (Set.range b)
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro v ⟨j, rfl⟩
    refine ⟨Pi.single j 1, ?_⟩
    simp [monsterCo1GeometryVectorCombination, Pi.single_apply]

/-- A proved twenty-four-point source span makes its coefficient map surjective. -/
theorem monsterCo1GeometryVectorCombination_surjective {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] (b : Fin 24 → V)
    (hb : Submodule.span (ZMod 2) (Set.range b) = ⊤) :
    Function.Surjective (monsterCo1GeometryVectorCombination b) := by
  rw [← LinearMap.range_eq_top, monsterCo1GeometryVectorCombination_range, hb]

/-- Complete natural generator images determine the natural coefficient map. -/
theorem monsterCo1GeometryVectorCombination_image {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] (b : Fin 24 → V)
    (f : V →ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (A : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hf : ∀ j, f (b j) = fun i => A i j) (a : Fin 24 → ZMod 2) :
    f (monsterCo1GeometryVectorCombination b a) = A *ᵥ a := by
  change f (∑ j, a j • b j) = _
  rw [map_sum]
  simp only [map_smul, hf]
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- A proved source span and a checked left inverse of its actual image matrix give a trivial
natural kernel, with no source dimension or source injectivity assumption. -/
theorem monsterCo1GeometryVector_natural_injective {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] (b : Fin 24 → V)
    (f : V →ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (A Ai : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hb : Submodule.span (ZMod 2) (Set.range b) = ⊤)
    (hf : ∀ j, f (b j) = fun i => A i j) (hAi : Ai * A = 1) :
    Function.Injective f := by
  intro x y h
  obtain ⟨a, rfl⟩ := monsterCo1GeometryVectorCombination_surjective b hb x
  obtain ⟨c, rfl⟩ := monsterCo1GeometryVectorCombination_surjective b hb y
  rw [monsterCo1GeometryVectorCombination_image b f A hf,
    monsterCo1GeometryVectorCombination_image b f A hf] at h
  have hc := congrArg (fun v => Ai *ᵥ v) h
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hAi, Matrix.one_mulVec,
    Matrix.one_mulVec] at hc
  exact congrArg (monsterCo1GeometryVectorCombination b) hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
