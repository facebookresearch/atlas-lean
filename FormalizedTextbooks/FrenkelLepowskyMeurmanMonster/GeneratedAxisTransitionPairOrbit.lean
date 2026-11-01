/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionPairCoverage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisEnumerationLocal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisPairLocal

/-! Exact counting of the actual local Ω-centralizer orbit on signed pair axes. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000

/-- The actual local vector action, chosen explicitly before generic pointwise actions. -/
noncomputable instance (priority := 2000) generatedAxisLocalActualSmul : SMul H GriessSpace where
  smul h x := rhoLocal h x

/-- The same actual vector action restricted to the actual local Ω centralizer. -/
noncomputable instance (priority := 2000) generatedAxisLocalOmegaActualSmul :
    SMul localOmegaStabilizer GriessSpace where
  smul h x := rhoLocal h.val x

/-- The actual local representation supplies its genuine action on Griess vectors. -/
noncomputable instance generatedAxisLocalActualAction : MulAction H GriessSpace where
  smul h x := rhoLocal h x
  one_smul x := by
    change rhoLocal 1 x = x
    rw [rhoLocal.map_one]
    rfl
  mul_smul h k x := by
    change rhoLocal (h * k) x = rhoLocal h (rhoLocal k x)
    rw [rhoLocal.map_mul]
    rfl

/-- Restriction of the actual vector action to the actual local Ω centralizer. -/
noncomputable instance generatedAxisLocalOmegaActualAction :
    MulAction localOmegaStabilizer GriessSpace where
  smul h x := rhoLocal h.val x
  one_smul x := by
    change rhoLocal 1 x = x
    rw [rhoLocal.map_one]
    rfl
  mul_smul h k x := by
    change rhoLocal (h.val * k.val) x = rhoLocal h.val (rhoLocal k.val x)
    rw [rhoLocal.map_mul]
    rfl

/-- The 1104 actual signed pair axes, in the original Griess vector space. -/
noncomputable def generatedSignedPairAxes : Set GriessSpace :=
  Set.range (fun z : (Fin 2 × Fin 276) × ZMod 2 => conwayShortAxis (Sum.inl z.1) z.2)

/-- The actual pair labels and signs give distinct actual Griess vectors. -/
theorem generatedSignedPairAxes_injective : Function.Injective
    (fun z : (Fin 2 × Fin 276) × ZMod 2 => conwayShortAxis (Sum.inl z.1) z.2) := by
  intro a b h
  have he : (Sum.inl a.1, a.2) = (Sum.inl b.1, b.2) :=
    @generatedAxis_signed_injective (Sum.inl a.1, a.2) (Sum.inl b.1, b.2) h
  exact Prod.ext
    (Sum.inl.inj (congrArg (fun z : GriessShortIndex × ZMod 2 => z.1) he))
    (congrArg (fun z : GriessShortIndex × ZMod 2 => z.2) he)

/-- There are exactly 1104 actual signed pair axes. -/
theorem generatedSignedPairAxes_card : Nat.card generatedSignedPairAxes = 1104 := by
  change Nat.card (Set.range (fun z : (Fin 2 × Fin 276) × ZMod 2 =>
    conwayShortAxis (Sum.inl z.1) z.2)) = 1104
  rw [← Nat.card_congr (Equiv.ofInjective _ generatedSignedPairAxes_injective)]
  norm_num [Nat.card_prod]

/-- The actual local Ω-centralizer orbit consists of all actual signed pair axes. -/
theorem generatedAxis_localOmega_pair_orbit_eq (p : Fin 276) :
    MulAction.orbit localOmegaStabilizer (conwayAxis p) = generatedSignedPairAxes := by
  rw [← conwayShortAxis_pair_zero p]
  ext x
  constructor
  · rintro ⟨h, rfl⟩
    obtain ⟨t, q, d, he⟩ := generatedAxis_localOmega_pair_image h 0 p 0
    exact ⟨((t, q), d), he.symm⟩
  · rintro ⟨⟨⟨t, q⟩, d⟩, rfl⟩
    exact generatedAxis_pair_localOmega_transitive 0 t p q 0 d

/-- The genuine starting-axis orbit under the local Ω centralizer has size 1104. -/
theorem generatedAxis_localOmega_pair_orbit_card (p : Fin 276) :
    Nat.card (MulAction.orbit localOmegaStabilizer (conwayAxis p)) = 1104 := by
  rw [generatedAxis_localOmega_pair_orbit_eq]
  exact generatedSignedPairAxes_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
