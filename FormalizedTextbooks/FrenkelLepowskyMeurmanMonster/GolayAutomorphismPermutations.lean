/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismSigns

/-! Actual Golay coordinate permutations acting on the actual Leech lattice.
This constructs the permutation part of the monomial subgroup described in
Seysen §9.2 directly from its code-preservation definition. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Relabel integer coordinates by the inverse permutation for a left action. -/
def golayIntegerPermute (p : Equiv.Perm (Fin 24)) (u : Fin 24 → ℤ) : Fin 24 → ℤ :=
  fun i => u (p.symm i)

theorem golayIntegerPermute_mem (p : golayAutomorphismSubgroup)
    (u : Fin 24 → ℤ) (hu : u ∈ leechIntegral) : golayIntegerPermute p.val u ∈ leechIntegral := by
  obtain ⟨m, hm, c, hc, huc, hus⟩ := (mem_leechIntegral_iff_source u).mp hu
  apply (mem_leechIntegral_iff_source _).mpr
  refine ⟨m, hm, golayPermute p.val c, (p.property c).mp hc, ?_, ?_⟩
  · intro i
    exact huc (p.val.symm i)
  · have hsum : ∑ i, golayIntegerPermute p.val u i = ∑ i, u i :=
      Equiv.sum_comp p.val.symm u
    rw [hsum]
    exact hus

/-- The physical coordinate permutation, in the left-action convention. -/
def golayRealPermute (p : Equiv.Perm (Fin 24)) : (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ) where
  toFun x i := x (p.symm i)
  invFun x i := x (p i)
  left_inv x := by ext i; exact congrArg x (p.symm_apply_apply i)
  right_inv x := by ext i; exact congrArg x (p.apply_symm_apply i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem golayRealPermute_apply (p : Equiv.Perm (Fin 24)) (x : Fin 24 → ℝ)
    (i : Fin 24) : golayRealPermute p x i = x (p.symm i) := rfl

theorem golayRealPermute_embedding (p : Equiv.Perm (Fin 24)) (u : Fin 24 → ℤ) :
    golayRealPermute p (leechCoordinateEmbedding u) =
      leechCoordinateEmbedding (golayIntegerPermute p u) := rfl

/-- Actual code-preserving coordinate permutations are actual lattice isometries. -/
def golayPermutationIsometry (p : golayAutomorphismSubgroup) : leechIsomSubgroup :=
  ⟨golayRealPermute p.val, by
    constructor
    · intro x y
      exact Equiv.sum_comp p.val.symm (fun i => x i * y i)
    · have h (p : golayAutomorphismSubgroup) (x : Fin 24 → ℝ) (hx : x ∈ LeechLattice) :
          golayRealPermute p.val x ∈ LeechLattice := by
        obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
        rw [golayRealPermute_embedding]
        exact Submodule.mem_map.mpr ⟨_, golayIntegerPermute_mem p u hu, rfl⟩
      intro x
      constructor
      · exact h p x
      · intro hx
        have hh := h p⁻¹ _ hx
        change (golayRealPermute p.val).symm (golayRealPermute p.val x) ∈ LeechLattice at hh
        simpa only [LinearEquiv.symm_apply_apply] using hh⟩

/-- The concrete permutation part of the monomial lattice group. -/
noncomputable def golayPermutationHom : golayAutomorphismSubgroup →* leechIsomSubgroup where
  toFun := golayPermutationIsometry
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rfl
  map_mul' p q := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
