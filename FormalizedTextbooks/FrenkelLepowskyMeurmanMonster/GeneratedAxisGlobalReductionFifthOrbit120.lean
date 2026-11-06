/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthOrbit120Data
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthGeneration
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFiniteOrbit
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthRoots

/-! The entire actual fifth-axis stabilizer has exactly the checked 120-point
binary orbit at mask four. Both closure and reachability are proved from actual edges. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- The 120 genuine binary vectors of the finite packet. -/
def generatedAxisGlobalFifthOrbit120Point (i : Fin 120) : Fin 24 → ZMod 2 :=
  monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalFifthOrbit120Mask i)

/-- All 120 decoded points are genuinely distinct. -/
theorem generatedAxisGlobalFifthOrbit120Point_injective :
    Function.Injective generatedAxisGlobalFifthOrbit120Point := by
  intro i j hij
  apply generatedAxisGlobalFifthOrbit120_distinct_certificate.2
  rw [← generatedAxisGlobalFifthOrbit120_distinct_certificate.1 i,
    ← generatedAxisGlobalFifthOrbit120_distinct_certificate.1 j]
  exact congrArg (fun x : Fin 24 → ZMod 2 => ∑ k : Fin 24, (x k).val * 2^k.val) hij

/-- Every original projected generator acts by its checked finite packet target. -/
theorem generatedAxisGlobalFifthOrbit120_generator_action (k : Fin 19) (i : Fin 120) :
    (QuotientGroup.mk' signsSubgroup (generatedAxisGlobalFifthSpatial k) : Co1) •
      generatedAxisGlobalFifthOrbit120Point i =
    generatedAxisGlobalFifthOrbit120Point (generatedAxisGlobalFifthOrbit120Target k i) := by
  change co1BinaryAction (QuotientGroup.mk' signsSubgroup (generatedAxisGlobalFifthSpatial k))
    (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalFifthOrbit120Mask i)) = _
  rw [generatedAxisGlobalFifthSpatial_binary, generatedAxisGlobalFifthBinaryColumns_action,
    generatedAxisGlobalFifthOrbit120_certificate.1 k i]
  rfl

/-- Every packet parent descends and acts by a genuine projected stabilizer generator. -/
theorem generatedAxisGlobalFifthOrbit120_descending (i : Fin 120) :
    i = 0 ∨ ∃ j : Fin 120, ∃ k : Fin 19,
      generatedAxisGlobalFifthOrbit120Rank j < generatedAxisGlobalFifthOrbit120Rank i ∧
      (QuotientGroup.mk' signsSubgroup (generatedAxisGlobalFifthSpatial k) : Co1) •
        generatedAxisGlobalFifthOrbit120Point j = generatedAxisGlobalFifthOrbit120Point i := by
  by_cases h : i = 0
  · exact Or.inl h
  · have hp := generatedAxisGlobalFifthOrbit120_certificate.2 i h
    refine Or.inr ⟨generatedAxisGlobalFifthOrbit120Parent i,
      generatedAxisGlobalFifthOrbit120Edge i, hp.1, ?_⟩
    rw [generatedAxisGlobalFifthOrbit120_generator_action, hp.2]

/-- The full actual projected fifth-axis stabilizer orbit is exactly the checked finite packet. -/
theorem generatedAxisGlobalFifthOrbit120_eq :
    MulAction.orbit generatedFifthProjectedAxisStabilizer
      (generatedAxisGlobalFifthOrbit120Point 0) =
      Set.range generatedAxisGlobalFifthOrbit120Point := by
  have ho := generatedAxisGlobalFiniteCarrier_orbit
    (fun k : Fin 19 => (QuotientGroup.mk' signsSubgroup (generatedAxisGlobalFifthSpatial k) : Co1))
    generatedAxisGlobalFifthOrbit120Point 0 generatedAxisGlobalFifthOrbit120Rank
    generatedAxisGlobalFifthOrbit120Point_injective
    (fun k i => ⟨_, generatedAxisGlobalFifthOrbit120_generator_action k i⟩)
    generatedAxisGlobalFifthOrbit120_descending
  change MulAction.orbit generatedAxisGlobalFifthProjectionGenerators _ = _ at ho
  ext x
  constructor
  · rintro ⟨g, hg⟩
    have hm : g.val ∈ generatedAxisGlobalFifthProjectionGenerators := by
      rw [generatedAxisGlobalFifthProjectionGenerators_eq_stabilizer]
      exact g.property
    have hx : x ∈ MulAction.orbit generatedAxisGlobalFifthProjectionGenerators
        (generatedAxisGlobalFifthOrbit120Point 0) := ⟨⟨g.val, hm⟩, hg⟩
    rwa [ho] at hx
  · intro hx
    have hx' : x ∈ MulAction.orbit generatedAxisGlobalFifthProjectionGenerators
        (generatedAxisGlobalFifthOrbit120Point 0) := ho.symm ▸ hx
    obtain ⟨g, hg⟩ := hx'
    have hm : g.val ∈ generatedFifthProjectedAxisStabilizer := by
      rw [← generatedAxisGlobalFifthProjectionGenerators_eq_stabilizer]
      exact g.property
    exact ⟨⟨g.val, hm⟩, hg⟩

/-- The finite packet root is the genuine norm-eight frame root with mask four. -/
theorem generatedAxisGlobalFifthOrbit120_root :
    generatedAxisGlobalFifthOrbit120Point 0 = generatedAxisGlobalFifthRootBinary 1 := rfl

/-- Every packet point belongs to the actual binary Ω orbit, with its exact frame type proved. -/
theorem generatedAxisGlobalFifthOrbit120Point_mem (i : Fin 120) :
    generatedAxisGlobalFifthOrbit120Point i ∈ generatedAxisGlobalBinaryOrbit := by
  obtain ⟨c, hc⟩ := generatedAxisGlobalFifthRoot_mem_orbit 1
  obtain ⟨g, _, hg⟩ := generatedAxisGlobalFiniteCarrier_reachable
    (fun k : Fin 19 => (QuotientGroup.mk' signsSubgroup (generatedAxisGlobalFifthSpatial k) : Co1))
    generatedAxisGlobalFifthOrbit120Point 0 generatedAxisGlobalFifthOrbit120Rank
    generatedAxisGlobalFifthOrbit120_descending i
  refine ⟨g * c, ?_⟩
  change co1BinaryAction (g * c) (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) = _
  change co1BinaryAction c (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) = _ at hc
  rw [map_mul, LinearEquiv.mul_apply, hc, ← generatedAxisGlobalFifthOrbit120_root]
  exact hg

/-- This is an actual 120-point stabilizer orbit, with no assumed source orbit-size entry. -/
theorem generatedAxisGlobalFifthOrbit120_card :
    Nat.card (MulAction.orbit generatedFifthProjectedAxisStabilizer
      (generatedAxisGlobalFifthOrbit120Point 0)) = 120 := by
  rw [generatedAxisGlobalFifthOrbit120_eq,
    ← Nat.card_congr (Equiv.ofInjective _ generatedAxisGlobalFifthOrbit120Point_injective)]
  exact Nat.card_fin 120

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
