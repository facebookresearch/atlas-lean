/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1GeometryPolarLocalPentads

/-! Normalized odd norm-eight vectors, retaining their genuine source residues. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem polarLocal_scalar (x : ℤ) (hb : x.natAbs ≤ 8)
    (hr : (x : ZMod 4) = 1) (h7 : x.natAbs ≠ 7) : x = 1 ∨ x = -3 ∨ x = 5 := by
  have ha : |x| ≤ (8 : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hb
  have ht : ∀ a : Fin 17,
      let x : ℤ := a.val - 8
      (x : ZMod 4) = 1 → x.natAbs ≠ 7 → x = 1 ∨ x = -3 ∨ x = 5 := by
    decide +kernel
  let a : Fin 17 := ⟨(x + 8).toNat, by omega⟩
  have hx : (a.val : ℤ) - 8 = x := by dsimp [a]; omega
  have hh := ht a
  dsimp only at hh
  rw [hx] at hh
  exact hh hr h7

/-- Every normalized coordinate has its exact value among one, negative three and five. -/
theorem monsterCo1PolarLocal_normalized_values (u : leechIntegral)
    (hn : leechSquareSum u.val = 64) (hr : ∀ i, (u.val i : ZMod 4) = 1) :
    ∀ i, u.val i = 1 ∨ u.val i = -3 ∨ u.val i = 5 := by
  have h7 : leechNormEightMultiplicity u.val 7 = 0 := by
    rcases monsterCo1PolarLocal_residue_shapes u hn hr with h | h <;>
      rw [h] <;> decide +kernel
  intro i
  apply polarLocal_scalar (u.val i) (leechNormEight_natAbs_le u.val hn i) (hr i)
  intro hi
  have hm : i ∈ Finset.univ.filter fun j => (u.val j).natAbs = 7 := by simp [hi]
  have he := Finset.card_eq_zero.mp h7
  change (Finset.univ.filter fun j => (u.val j).natAbs = 7) = ∅ at he
  rw [he] at hm
  exact Finset.notMem_empty i hm

/-- The pentad odd shape is exactly a genuine pentad vector after source-sign normalization. -/
theorem monsterCo1PolarLocal_normalized_pentad (u : leechIntegral)
    (hn : leechSquareSum u.val = 64) (hr : ∀ i, (u.val i : ZMod 4) = 1)
    (hs : leechNormEightMultiplicity u.val = leechNormEightShapeCounts 7) :
    ∃ P : Finset (Fin 24), P.card = 5 ∧ u.val = monsterCo1PolarPentadVector P := by
  classical
  let P := Finset.univ.filter fun i => u.val i = -3
  have hval := monsterCo1PolarLocal_normalized_values u hn hr
  have h3 (i : Fin 24) : (u.val i).natAbs = 3 ↔ u.val i = -3 := by
    rcases hval i with h | h | h <;> simp [h]
  have h5 : leechNormEightMultiplicity u.val 5 = 0 := by rw [hs]; decide +kernel
  have hn5 (i : Fin 24) : u.val i ≠ 5 := by
    intro hi
    have hm : i ∈ Finset.univ.filter fun j => (u.val j).natAbs = 5 := by simp [hi]
    have he := Finset.card_eq_zero.mp h5
    change (Finset.univ.filter fun j => (u.val j).natAbs = 5) = ∅ at he
    rw [he] at hm
    exact Finset.notMem_empty i hm
  refine ⟨P, ?_, ?_⟩
  · have hc := congrFun hs 3
    change (Finset.univ.filter fun i => (u.val i).natAbs = 3).card = 5 at hc
    simpa only [h3] using hc
  · funext i
    by_cases hi : u.val i = -3
    · simp [monsterCo1PolarPentadVector, P, hi]
    · have hu : u.val i = 1 := (hval i).resolve_right (fun h => h.elim hi (hn5 i))
      simp [monsterCo1PolarPentadVector, P, hu]

/-- Actual code automorphisms carry every pentad to the first five coordinates. -/
theorem monsterCo1PolarPentad_to_standard (P : Finset (Fin 24)) (hP : P.card = 5) :
    ∃ p : golayAutomorphismSubgroup,
      golayIntegerPermute p.val (monsterCo1PolarPentadVector P) =
        monsterCo1PolarPentadVector (Finset.univ.filter fun i : Fin 24 => i.val < 5) := by
  classical
  have hc : Fintype.card {i : Fin 24 // i ∈ P} = 5 := by simp [hP]
  let e : Fin 5 ≃ {i : Fin 24 // i ∈ P} :=
    (Fintype.equivFinOfCardEq hc).symm
  let a : Fin 5 → Fin 24 := fun j => (e j).val
  have ha : Function.Injective a := Subtype.val_injective.comp e.injective
  obtain ⟨p, hp⟩ := golayAutomorphism_maps_firstFive a ha
  refine ⟨p⁻¹, ?_⟩
  funext i
  have hi : p.val i ∈ P ↔ i.val < 5 := by
    constructor
    · intro hm
      obtain ⟨j, hj⟩ := e.surjective ⟨p.val i, hm⟩
      have hji : p.val (Fin.castAdd 19 j) = p.val i := by
        rw [hp]
        exact congrArg Subtype.val hj
      have h := congrArg Fin.val (p.val.injective hji)
      simpa only [Fin.val_castAdd] using h ▸ j.isLt
    · intro hlt
      let j : Fin 5 := ⟨i.val, hlt⟩
      have hj : Fin.castAdd 19 j = i := Fin.ext rfl
      rw [← hj, hp]
      exact (e j).property
  change (if p.val i ∈ P then -3 else 1 : ℤ) = _
  simp only [monsterCo1PolarPentadVector, Finset.mem_filter, Finset.mem_univ, true_and, hi]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
