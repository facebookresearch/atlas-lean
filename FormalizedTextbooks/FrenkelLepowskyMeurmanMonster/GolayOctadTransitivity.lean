/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Transitivity on actual Golay octads, deduced from the proved five-point action. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismOctads
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismTransitivity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem golay_support_card (c : Fin 24 → ZMod 2) :
    Fintype.card {i : Fin 24 // c i = 1} = ∑ i, (c i).val := by
  classical
  have hbit : ∀ b : ZMod 2, b.val = if b = 1 then 1 else 0 := by decide
  simp_rw [hbit]
  simp [Fintype.card_subtype]

/-- Every actual octad is carried to the standard first-eight-coordinate octad. -/
theorem golayOctad_to_standard (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode)
    (hw : ∑ i, (c i).val = 8) :
    ∃ p : golayAutomorphismSubgroup, golayPermute p.val c = golayStandardOctad := by
  classical
  have hcard : Fintype.card {i : Fin 24 // c i = 1} = 8 :=
    (golay_support_card c).trans hw
  have he : Nonempty (Fin 5 ↪ {i : Fin 24 // c i = 1}) :=
    Function.Embedding.nonempty_of_card_le (by simp [hcard])
  let e : Fin 5 ↪ {i : Fin 24 // c i = 1} := Classical.choice he
  let a : Fin 5 → Fin 24 := fun j => (e j).val
  let b : Fin 5 → Fin 24 := fun j => Fin.castAdd 19 j
  have ha : Function.Injective a := Subtype.val_injective.comp e.injective
  have hb : Function.Injective b := by
    intro j k h
    exact Fin.ext (congrArg (fun i : Fin 24 => i.val) h)
  obtain ⟨p, hp⟩ := golayAutomorphism_five_transitive a b ha hb
  refine ⟨p, golayOctad_unique_through_first_five _ _
    ((p.property c).mp hc) golayStandardOctad_mem ?_ golayStandardOctad_weight ?_⟩
  · exact (Equiv.sum_comp p.val.symm (fun i => (c i).val)).trans hw
  · intro i hi
    let j : Fin 5 := ⟨i.val, hi⟩
    have hbi : b j = i := Fin.ext rfl
    have hpi : p.val.symm i = a j := by
      rw [← hbi, ← hp j, p.val.symm_apply_apply]
    refine ⟨?_, ?_⟩
    · change c (p.val.symm i) = 1
      rw [hpi]
      exact (e j).property
    · simp [golayStandardOctad, show i.val < 8 by omega]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
