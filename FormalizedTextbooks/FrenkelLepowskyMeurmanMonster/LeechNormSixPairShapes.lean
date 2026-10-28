/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixCatalog

/-! The five possible coordinate families of norm-six vectors paired with a two-point norm-four
vector. Coordinates retain the original integer normalization. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The allowed absolute coordinate values in each actual norm-six shape. -/
def leechNormSixCoordinateAllowed (s : Fin 4) (k : ℕ) : Prop :=
  if s = 0 then k = 0 ∨ k = 2
  else if s = 1 then k = 0 ∨ k = 2 ∨ k = 4
  else if s = 2 then k = 1 ∨ k = 5
  else k = 1 ∨ k = 3

instance (s : Fin 4) (k : ℕ) : Decidable (leechNormSixCoordinateAllowed s k) :=
  inferInstanceAs (Decidable (if s = 0 then k = 0 ∨ k = 2
    else if s = 1 then k = 0 ∨ k = 2 ∨ k = 4
    else if s = 2 then k = 1 ∨ k = 5 else k = 1 ∨ k = 3))

/-- The paired coordinates give one dodecad, two octad, or two odd families. -/
def leechNormSixPairPattern (s : Fin 4) (a b : ℤ) : Prop :=
  if s = 0 then a = 2 ∧ b = 2
  else if s = 1 then (a = 4 ∧ b = 0) ∨ (a = 0 ∧ b = 4) ∨ (a = 2 ∧ b = 2)
  else if s = 2 then (a = 5 ∧ b = -1) ∨ (a = -1 ∧ b = 5)
  else (a = 3 ∧ b = 1) ∨ (a = 1 ∧ b = 3)

instance (s : Fin 4) (a b : ℤ) : Decidable (leechNormSixPairPattern s a b) :=
  inferInstanceAs (Decidable (if s = 0 then a = 2 ∧ b = 2
    else if s = 1 then (a = 4 ∧ b = 0) ∨ (a = 0 ∧ b = 4) ∨ (a = 2 ∧ b = 2)
    else if s = 2 then (a = 5 ∧ b = -1) ∨ (a = -1 ∧ b = 5)
    else (a = 3 ∧ b = 1) ∨ (a = 1 ∧ b = 3)))

/-- Every coordinate occurs in its complete original absolute-value catalogue. -/
theorem leechNormSix_coordinate_allowed (u : Fin 24 → ℤ) (s : Fin 4)
    (hb : ∀ i, (u i).natAbs ≤ 8)
    (hs : leechNormEightMultiplicity u = leechNormSixShapeCounts s) (i : Fin 24) :
    leechNormSixCoordinateAllowed s (u i).natAbs := by
  let k : Fin 9 := ⟨(u i).natAbs, Nat.lt_succ_of_le (hb i)⟩
  have hp : 0 < leechNormEightMultiplicity u k := by
    apply Finset.card_pos.mpr
    exact ⟨i, by simp [k]⟩
  rw [hs] at hp
  have hcheck : ∀ s : Fin 4, ∀ k : Fin 9,
      0 < leechNormSixShapeCounts s k → leechNormSixCoordinateAllowed s k.val := by
    decide +kernel
  exact hcheck s k hp

/-- The original square norm and pairing force exactly the five coordinate families. -/
theorem leechNormSix_pair_catalog (u : leechIntegral)
    (hs : leechSquareSum u.val = 48) (p q : Fin 24) (hpair : u.val p + u.val q = 4) :
    ∃ s : Fin 4, leechNormEightMultiplicity u.val = leechNormSixShapeCounts s ∧
      leechNormSixPairPattern s (u.val p) (u.val q) := by
  obtain ⟨s, hs'⟩ := leechNormSix_catalog u hs
  refine ⟨s, hs', ?_⟩
  have hb (i : Fin 24) := leechNormSix_natAbs_le u.val hs i
  have ha (i : Fin 24) := leechNormSix_coordinate_allowed u.val s
    (fun j => (hb j).trans (by decide)) hs' i
  have hcheck : ∀ s : Fin 4, ∀ a b : Fin 13,
      let x : ℤ := (a.val : ℤ) - 6
      let y : ℤ := (b.val : ℤ) - 6
      leechNormSixCoordinateAllowed s x.natAbs →
      leechNormSixCoordinateAllowed s y.natAbs → x + y = 4 →
      leechNormSixPairPattern s x y := by
    decide +kernel
  let a : Fin 13 := ⟨(u.val p + 6).toNat, by have := hb p; omega⟩
  let b : Fin 13 := ⟨(u.val q + 6).toNat, by have := hb q; omega⟩
  have hx : (a.val : ℤ) - 6 = u.val p := by dsimp [a]; have := hb p; omega
  have hy : (b.val : ℤ) - 6 = u.val q := by dsimp [b]; have := hb q; omega
  have h := hcheck s a b
  dsimp only at h
  rw [hx, hy] at h
  exact h (ha p) (ha q) hpair

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
