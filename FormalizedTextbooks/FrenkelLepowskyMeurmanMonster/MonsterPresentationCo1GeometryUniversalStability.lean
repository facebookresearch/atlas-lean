/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Finite actual-generator image certificates suffice for the source universal-module upper
bound. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryUniversalRepresentation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryFiveQuotient
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual group elements preserving a chosen source-module subspace form a submonoid. -/
def monsterCo1GeometryUniversalPreserver
    (S : Submodule (ZMod 2) MonsterCo1GeometryUniversalModule) : Submonoid Co1 where
  carrier := {g | ∀ v ∈ S, monsterCo1GeometryUniversalAction g v ∈ S}
  one_mem' := by
    intro v hv
    simpa only [monsterCo1GeometryUniversalAction_one, Module.End.one_apply] using hv
  mul_mem' := by
    intro g h hg hh v hv
    rw [monsterCo1GeometryUniversalAction_mul, Module.End.mul_apply]
    exact hg _ (hh _ hv)

/-- Preservation under the five genuine generators implies preservation under all actual Conway
elements. -/
theorem monsterCo1GeometryUniversal_stable_of_five
    (S : Submodule (ZMod 2) MonsterCo1GeometryUniversalModule)
    (hS : ∀ k : Fin 5, ∀ v ∈ S,
      monsterCo1GeometryUniversalAction (monsterCo1FiveGenerator k) v ∈ S) :
    ∀ g : Co1, ∀ v ∈ S, monsterCo1GeometryUniversalAction g v ∈ S := by
  have : Finite Co1 := co1_finite
  have h : Submonoid.closure (Set.range monsterCo1FiveGenerator) ≤
      monsterCo1GeometryUniversalPreserver S := by
    apply Submonoid.closure_le.mpr
    rintro g ⟨k, rfl⟩
    exact hS k
  rw [← Subgroup.closure_toSubmonoid_of_finite, ← monsterCo1FiveSubgroup,
    monsterCo1FiveSubgroup_eq_top] at h
  intro g
  exact h (show g ∈ (⊤ : Subgroup Co1).toSubmonoid from trivial)

/-- A finite candidate span containing the base point and all five generator images contains
every source point.
The explicit image certificates remain inputs here; no universal dimension is assumed. -/
theorem monsterCo1GeometryUniversal_pointSpan_eq_top (b : Fin 24 → MonsterCo1GeometryPoint)
    (hbase : monsterCo1GeometryUniversalPoint monsterCo1GeometryBasePoint ∈
      Submodule.span (ZMod 2) (Set.range (fun i => monsterCo1GeometryUniversalPoint (b i))))
    (himages : ∀ k : Fin 5, ∀ i : Fin 24,
      monsterCo1GeometryUniversalPoint (monsterCo1FiveGenerator k • b i) ∈
        Submodule.span (ZMod 2) (Set.range (fun j => monsterCo1GeometryUniversalPoint (b j)))) :
    Submodule.span (ZMod 2) (Set.range (fun i => monsterCo1GeometryUniversalPoint (b i))) = ⊤ := by
  let S := Submodule.span (ZMod 2) (Set.range (fun i => monsterCo1GeometryUniversalPoint (b i)))
  have hs : ∀ g : Co1, ∀ v ∈ S, monsterCo1GeometryUniversalAction g v ∈ S := by
    apply monsterCo1GeometryUniversal_stable_of_five
    intro k
    have h : S ≤ S.comap (monsterCo1GeometryUniversalAction (monsterCo1FiveGenerator k)) := by
      apply Submodule.span_le.mpr
      rintro v ⟨i, rfl⟩
      change monsterCo1GeometryUniversalAction (monsterCo1FiveGenerator k)
        (monsterCo1GeometryUniversalPoint (b i)) ∈ S
      rw [monsterCo1GeometryUniversalAction_point]
      exact himages k i
    exact fun v hv => h hv
  apply top_unique
  rw [← monsterCo1GeometryUniversalPoint_span]
  apply Submodule.span_le.mpr
  rintro v ⟨p, rfl⟩
  obtain ⟨g, hg⟩ := monsterCo1GeometryPoint_reached p
  have hp := hs g _ hbase
  rw [monsterCo1GeometryUniversalAction_point, hg] at hp
  exact hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
