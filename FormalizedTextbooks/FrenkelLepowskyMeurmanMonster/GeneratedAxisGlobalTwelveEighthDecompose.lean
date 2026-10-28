/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthForestCover
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthShortRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskFinite
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinaryCover
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageBinary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootPairs

/-! Complete actual Eighth-family transition reduction from the checked bitset forest.

Every genuine binary Ω point is reached from one of the 37 type-four forest roots by an actual
element fixing the whole Eighth axis: the forest gives an element of the projected stabilizer,
which lifts to the whole-axis stabilizer; the zero and short roots are excluded by lattice norms.
Every local element then decomposes through a root, with both triality signs. Root
representatives are actual local elements carrying Ω to the root masks (the identity at Ω),
and bindings transfer along the stabilizer action on binary roots. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The 37 type-four forest root masks of the Eighth family, Ω first. -/
def generatedAxisGlobalTwelveEighthRootMask : Fin 37 → ℕ :=
  ![2048, 1, 2, 8, 17, 19, 22, 24, 25, 35, 44, 45, 51, 96, 240, 244, 270, 280, 285, 291, 304, 463,
    808, 1026, 28672, 45056, 53248, 81920, 86016, 8388609, 8388610, 8388611, 8388612, 8388613,
    8388616, 8388631, 8388642]

/-- The zero mask is excluded from the actual binary Ω orbit. -/
theorem generatedAxisGlobalTwelveEighthZeroRoot_not_mem_orbit :
    monsterCo1GeometryBinaryMaskDecode (n := 24) 0 ∉ generatedAxisGlobalBinaryOrbit := by
  intro hz
  exact generatedAxisGlobalBinary_ne_zero ⟨_, hz⟩ monsterCo1GeometryBinaryMaskDecode_zero

/-- A forest root is a type-four root mask or lies outside the binary Ω orbit. -/
theorem generatedAxisGlobalTwelveEighthForestRoot_cases (m : ℕ) (hm : m ∈ eighthForestRoots) :
    (∃ j, generatedAxisGlobalTwelveEighthRootMask j = m) ∨
      monsterCo1GeometryBinaryMaskDecode (n := 24) m ∉ generatedAxisGlobalBinaryOrbit := by
  unfold eighthForestRoots eighthForestTypeFourRoots eighthForestOtherRoots at hm
  rw [List.mem_append] at hm
  rcases hm with hm | hm
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inl ⟨5, rfl⟩
    · exact Or.inl ⟨6, rfl⟩
    · exact Or.inl ⟨7, rfl⟩
    · exact Or.inl ⟨8, rfl⟩
    · exact Or.inl ⟨9, rfl⟩
    · exact Or.inl ⟨10, rfl⟩
    · exact Or.inl ⟨11, rfl⟩
    · exact Or.inl ⟨12, rfl⟩
    · exact Or.inl ⟨13, rfl⟩
    · exact Or.inl ⟨14, rfl⟩
    · exact Or.inl ⟨15, rfl⟩
    · exact Or.inl ⟨16, rfl⟩
    · exact Or.inl ⟨17, rfl⟩
    · exact Or.inl ⟨18, rfl⟩
    · exact Or.inl ⟨19, rfl⟩
    · exact Or.inl ⟨20, rfl⟩
    · exact Or.inl ⟨21, rfl⟩
    · exact Or.inl ⟨22, rfl⟩
    · exact Or.inl ⟨23, rfl⟩
    · exact Or.inl ⟨24, rfl⟩
    · exact Or.inl ⟨25, rfl⟩
    · exact Or.inl ⟨26, rfl⟩
    · exact Or.inl ⟨27, rfl⟩
    · exact Or.inl ⟨28, rfl⟩
    · exact Or.inl ⟨29, rfl⟩
    · exact Or.inl ⟨30, rfl⟩
    · exact Or.inl ⟨31, rfl⟩
    · exact Or.inl ⟨32, rfl⟩
    · exact Or.inl ⟨33, rfl⟩
    · exact Or.inl ⟨34, rfl⟩
    · exact Or.inl ⟨35, rfl⟩
    · exact Or.inl ⟨36, rfl⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
    · exact Or.inr generatedAxisGlobalTwelveEighthZeroRoot_not_mem_orbit
    · exact Or.inr (generatedAxisGlobalTwelveEighthShortRoot_not_mem_orbit 0)
    · exact Or.inr (generatedAxisGlobalTwelveEighthShortRoot_not_mem_orbit 1)
    · exact Or.inr (generatedAxisGlobalTwelveEighthShortRoot_not_mem_orbit 2)
    · exact Or.inr (generatedAxisGlobalTwelveEighthShortRoot_not_mem_orbit 3)
    · exact Or.inr (generatedAxisGlobalTwelveEighthShortRoot_not_mem_orbit 4)
    · exact Or.inr (generatedAxisGlobalTwelveEighthShortRoot_not_mem_orbit 5)
    · exact Or.inr (generatedAxisGlobalTwelveEighthShortRoot_not_mem_orbit 6)
    · exact Or.inr (generatedAxisGlobalTwelveEighthShortRoot_not_mem_orbit 7)
    · exact Or.inr (generatedAxisGlobalTwelveEighthShortRoot_not_mem_orbit 8)
    · exact Or.inr (generatedAxisGlobalTwelveEighthShortRoot_not_mem_orbit 9)
    · exact Or.inr (generatedAxisGlobalTwelveEighthShortRoot_not_mem_orbit 10)
    · exact Or.inr (generatedAxisGlobalTwelveEighthShortRoot_not_mem_orbit 11)
    · exact Or.inr (generatedAxisGlobalTwelveEighthShortRoot_not_mem_orbit 12)
    · exact Or.inr (generatedAxisGlobalTwelveEighthShortRoot_not_mem_orbit 13)

/-- Every genuine binary Ω point is reached from a type-four root mask by an actual element
fixing the whole Eighth axis. -/
theorem generatedAxisGlobalTwelveEighth_binary_cover_masks (x : generatedAxisGlobalBinaryOrbit) :
    ∃ j : Fin 37, ∃ c : H, c ∈ generatedEighthLocalAxisStabilizer ∧
      co1BinaryAction (projH c) (monsterCo1GeometryBinaryMaskDecode (n := 24)
        (generatedAxisGlobalTwelveEighthRootMask j)) = x.val := by
  let b := (generatedAxisGlobalMaskFiniteEquiv 24).symm x.val
  have hb : monsterCo1GeometryBinaryMaskDecode b.val = x.val :=
    (generatedAxisGlobalMaskFiniteEquiv 24).apply_symm_apply x.val
  have hs : generatedAxisGlobalMaskSingular b.val = true := by
    rw [generatedAxisGlobalMaskSingular_iff, hb]
    exact generatedAxisGlobalBinary_squareQuad x
  obtain ⟨m, hm, c, hc, he⟩ := eighthForest_reached_projected b.val b.isLt hs
  obtain ⟨⟨h, hh⟩, rfl⟩ := hc
  have he' : co1BinaryAction (projH h) (monsterCo1GeometryBinaryMaskDecode m) = x.val := by
    rw [← hb]
    exact he
  rcases generatedAxisGlobalTwelveEighthForestRoot_cases m hm with ⟨j, hj⟩ | hn
  · exact ⟨j, h, hh, by rw [hj]; exact he'⟩
  · exfalso
    apply hn
    have hx : monsterCo1GeometryBinaryMaskDecode (n := 24) m =
        (generatedAxisGlobalBinaryAct h⁻¹ x).val := by
      change _ = co1BinaryAction (projH h⁻¹) x.val
      rw [← he', map_inv, map_inv]
      exact (LinearEquiv.symm_apply_apply _ _).symm
    rw [hx]
    exact (generatedAxisGlobalBinaryAct h⁻¹ x).property

/-- The actual binary Ω point has mask 2048. -/
theorem generatedAxisGlobalTwelveEighthOmega_mask :
    monsterCo1GeometryBinaryMaskDecode (n := 24) 2048 =
      Multiplicative.toAdd (qQuotHom sourceOmegaQ) := by
  rw [sourceOmegaQ_eq_frame_class, leechFrame_zero_hyperbolic]
  decide

open Classical in
/-- Actual local representatives of the type-four forest roots; the identity at Ω. -/
def generatedAxisGlobalTwelveEighthRootWord (j : Fin 37) : H :=
  if j = 0 then 1 else
    if h : ∃ r : H, (generatedAxisGlobalBinaryRoot r).val =
        monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalTwelveEighthRootMask j)
    then Classical.choose h else 1

/-- The representative of the Ω root is the identity. -/
theorem generatedAxisGlobalTwelveEighthRootWord_zero :
    generatedAxisGlobalTwelveEighthRootWord 0 = 1 := by
  simp [generatedAxisGlobalTwelveEighthRootWord]

/-- A root mask in the binary Ω orbit is the binary root of its representative. -/
theorem generatedAxisGlobalTwelveEighthRootWord_root (j : Fin 37)
    (hm : monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedAxisGlobalTwelveEighthRootMask j) ∈ generatedAxisGlobalBinaryOrbit) :
    (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveEighthRootWord j)).val =
      monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalTwelveEighthRootMask j) := by
  unfold generatedAxisGlobalTwelveEighthRootWord
  split_ifs with h0 h
  · subst h0
    change co1BinaryAction (projH 1⁻¹) (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) = _
    rw [inv_one, map_one, map_one]
    exact generatedAxisGlobalTwelveEighthOmega_mask.symm
  · exact Classical.choose_spec h
  · exfalso
    apply h
    obtain ⟨c, hc⟩ := hm
    obtain ⟨g, hg⟩ := projH_surjective c
    refine ⟨g⁻¹, ?_⟩
    change co1BinaryAction (projH g⁻¹⁻¹) (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) = _
    rw [inv_inv, hg]
    exact hc

/-- Every actual binary Ω point is reached from the binary root of a representative. -/
theorem generatedAxisGlobalTwelveEighth_binary_cover :
    ∀ x : generatedAxisGlobalBinaryOrbit, ∃ j : Fin 37, ∃ c : H,
      c ∈ generatedEighthLocalAxisStabilizer ∧
        generatedAxisGlobalBinaryAct c
          (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveEighthRootWord j)) = x := by
  intro x
  obtain ⟨j, c, hc, he⟩ := generatedAxisGlobalTwelveEighth_binary_cover_masks x
  have hm : monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedAxisGlobalTwelveEighthRootMask j) ∈ generatedAxisGlobalBinaryOrbit := by
    have hx : monsterCo1GeometryBinaryMaskDecode (n := 24)
        (generatedAxisGlobalTwelveEighthRootMask j) =
          (generatedAxisGlobalBinaryAct c⁻¹ x).val := by
      change _ = co1BinaryAction (projH c⁻¹) x.val
      rw [← he, map_inv, map_inv]
      exact (LinearEquiv.symm_apply_apply _ _).symm
    rw [hx]
    exact (generatedAxisGlobalBinaryAct c⁻¹ x).property
  refine ⟨j, c, hc, ?_⟩
  apply Subtype.ext
  change co1BinaryAction (projH c)
    (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveEighthRootWord j)).val = x.val
  rw [generatedAxisGlobalTwelveEighthRootWord_root j hm]
  exact he

/-- Every actual local element admits a phase-correct transition decomposition at the roots. -/
theorem generatedAxisGlobalTwelveEighth_actual_decompose (h : H) :
    ∃ j : Fin 37, ∃ n c : H, n ∈ localOmegaStabilizer ∧ c ∈ generatedEighthLocalAxisStabilizer ∧
      (h = n * generatedAxisGlobalTwelveEighthRootWord j * c ∨
        h = n * (inclQ singletonCocodeQ * generatedAxisGlobalTwelveEighthRootWord j) * c) :=
  generatedAxisGlobal_decompose_two_signs generatedEighthLocalAxisStabilizer
    generatedAxisGlobalTwelveEighthRootWord
    (generatedAxisGlobal_decompose_of_binary_cover generatedEighthLocalAxisStabilizer
      generatedAxisGlobalTwelveEighthRootWord generatedAxisGlobalTwelveEighth_binary_cover) h

/-- The root vectors suffice for all actual Eighth-family triality transitions. -/
theorem generatedAxisGlobalTwelveEighth_triality_of_actual_destinations {ι : Type*}
    (v : ι → GriessSpace)
    (hpositive : ∀ j : Fin 37,
      sExtra (rhoLocal (generatedAxisGlobalTwelveEighthRootWord j) generatedEighthAxis) ∈
        generatedLocalOrbitUnion v)
    (hnegative : ∀ j : Fin 37,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveEighthRootWord j) generatedEighthAxis) ∈
        generatedLocalOrbitUnion v) :
    ∀ h : H, sExtra (rhoLocal h generatedEighthAxis) ∈ generatedLocalOrbitUnion v := by
  intro h
  obtain ⟨j, n, c, hn, hc, he⟩ := generatedAxisGlobalTwelveEighth_actual_decompose h
  have hfix : rhoLocal c generatedEighthAxis = generatedEighthAxis := hc
  rcases he with he | he
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix]
    obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (generatedAxisGlobalTwelveEighthRootWord j) generatedEighthAxis)
    rw [← hk]
    exact generatedLocalOrbitUnion_local v k (hpositive j)
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix]
    obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (inclQ singletonCocodeQ * generatedAxisGlobalTwelveEighthRootWord j)
        generatedEighthAxis)
    rw [← hk]
    apply generatedLocalOrbitUnion_local v k
    rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobal_singleton_triality_exchange]
    exact generatedLocalOrbitUnion_local v (inclQ singletonCocodeQ) (hnegative j)

/-- Both triality images at a root representative lie in an actual local orbit union as soon as
both images at an explicit local element `h` do, when an actual whole-axis fixer carries the
root mask to the binary root of `h`. -/
theorem generatedAxisGlobalTwelveEighth_root_of_binding {ι : Type*} (v : ι → GriessSpace)
    (j : Fin 37) (h c : H) (hc : c ∈ generatedEighthLocalAxisStabilizer)
    (hroot : co1BinaryAction (projH c)
      (monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalTwelveEighthRootMask j)) =
        (generatedAxisGlobalBinaryRoot h).val)
    (hpos : sExtra (rhoLocal h generatedEighthAxis) ∈ generatedLocalOrbitUnion v)
    (hneg : sExtra⁻¹ (rhoLocal h generatedEighthAxis) ∈ generatedLocalOrbitUnion v) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveEighthRootWord j) generatedEighthAxis) ∈
        generatedLocalOrbitUnion v ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveEighthRootWord j) generatedEighthAxis) ∈
        generatedLocalOrbitUnion v := by
  have hm : monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedAxisGlobalTwelveEighthRootMask j) ∈ generatedAxisGlobalBinaryOrbit := by
    have hx : monsterCo1GeometryBinaryMaskDecode (n := 24)
        (generatedAxisGlobalTwelveEighthRootMask j) =
          (generatedAxisGlobalBinaryAct c⁻¹ (generatedAxisGlobalBinaryRoot h)).val := by
      change _ = co1BinaryAction (projH c⁻¹) (generatedAxisGlobalBinaryRoot h).val
      rw [← hroot, map_inv, map_inv]
      exact (LinearEquiv.symm_apply_apply _ _).symm
    rw [hx]
    exact (generatedAxisGlobalBinaryAct c⁻¹ (generatedAxisGlobalBinaryRoot h)).property
  have hb : generatedAxisGlobalBinaryAct c
      (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveEighthRootWord j)) =
        generatedAxisGlobalBinaryRoot h := by
    apply Subtype.ext
    change co1BinaryAction (projH c)
      (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveEighthRootWord j)).val = _
    rw [generatedAxisGlobalTwelveEighthRootWord_root j hm]
    exact hroot
  exact generatedAxisGlobalTwelve_root_pair_mem v generatedEighthAxis h
    (generatedAxisGlobalTwelveEighthRootWord j) c hc hb hpos hneg

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
