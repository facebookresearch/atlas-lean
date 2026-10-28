/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisEnumerationLocalCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOrbitCoverage

/-! Exact enumeration of the actual first local axis orbit. This proves the
196560 anchor in Höhn–Seysen, arXiv:2508.01037, Lemma 3.3, independently of
the transition matrix and of any numeric Co₁ order. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All actual signed-short axes, as vectors in the original Griess space. -/
noncomputable def generatedSignedShortAxes : Set GriessSpace :=
  Set.range (fun p : GriessShortIndex × ZMod 2 => conwayShortAxis p.1 p.2)

/-- The actual H orbit of the indicated starting signed-short axis. -/
noncomputable def generatedAxisLocalOrbit (r : GriessShortIndex) (c : ZMod 2) :
    Set GriessSpace := {x | ∃ h : H, rhoLocal h (conwayShortAxis r c) = x}

/-- The local orbit consists of every actual short label with both actual signs. -/
theorem generatedAxisLocalOrbit_eq_signed (r : GriessShortIndex) (c : ZMod 2) :
    generatedAxisLocalOrbit r c = generatedSignedShortAxes := by
  ext x
  constructor
  · rintro ⟨h, rfl⟩
    obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h
    refine ⟨(griessShortPermutation f.val.2 r, localShortPhase f r + c), ?_⟩
    exact (generatedAxis_localFiber_image f r c).symm
  · rintro ⟨⟨s, d⟩, rfl⟩
    exact generatedAxis_local_signed_transitive r s c d

/-- The explicit parameterization enumerates exactly 2·98280 distinct actual axes. -/
theorem generatedSignedShortAxes_card : Nat.card generatedSignedShortAxes = 196560 := by
  have he := Nat.card_congr (Equiv.ofInjective
    (fun p : GriessShortIndex × ZMod 2 => conwayShortAxis p.1 p.2)
    generatedAxis_signed_injective)
  change Nat.card (GriessShortIndex × ZMod 2) = Nat.card generatedSignedShortAxes at he
  rw [← he, Nat.card_prod, Nat.card_eq_fintype_card, griessShortIndex_card]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

/-- The actual first local axis orbit has the exact required anchor size. -/
theorem generatedAxisLocalOrbit_card (r : GriessShortIndex) (c : ZMod 2) :
    Nat.card (generatedAxisLocalOrbit r c) = 196560 := by
  rw [generatedAxisLocalOrbit_eq_signed]
  exact generatedSignedShortAxes_card

/-- Every axis counted in this anchor belongs to the actual generated orbit. -/
theorem generatedSignedShortAxes_subset_orbit (r : GriessShortIndex) (c : ZMod 2) :
    generatedSignedShortAxes ⊆ generatedVectorOrbit (conwayShortAxis r c) := by
  intro x hx
  rw [← generatedAxisLocalOrbit_eq_signed r c] at hx
  obtain ⟨h, hh⟩ := hx
  exact ⟨localIntoGenerated h, hh⟩

/-- The anchor as an actual subset of the genuine global axis orbit. -/
noncomputable def generatedAxisLocalAnchor (r : GriessShortIndex) (c : ZMod 2) :=
  {x : generatedVectorOrbit (conwayShortAxis r c) // x.val ∈ generatedSignedShortAxes}

/-- The actual global-orbit anchor counts the same genuine signed-short vectors. -/
noncomputable def generatedAxisLocalAnchorEquiv (r : GriessShortIndex) (c : ZMod 2) :
    generatedSignedShortAxes ≃ generatedAxisLocalAnchor r c where
  toFun x := ⟨⟨x.val, generatedSignedShortAxes_subset_orbit r c x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The first classification fiber has a proved actual-orbit anchor of size 196560. -/
theorem generatedAxisLocalAnchor_card (r : GriessShortIndex) (c : ZMod 2) :
    Nat.card (generatedAxisLocalAnchor r c) = 196560 := by
  rw [← Nat.card_congr (generatedAxisLocalAnchorEquiv r c)]
  exact generatedSignedShortAxes_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
