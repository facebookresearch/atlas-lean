/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































import Code.Inequalities.ReimerCompression

open Finset
open scoped NNReal FinsetFamily

namespace StatMech.Walls

open StatMech ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]







omit [Fintype E] in




theorem memberFiber_to_inter (i : E) (𝒜 : Finset (Finset E)) {s : Finset E} (hi : i ∉ s) :
    insert i s ∈ Down.compression i 𝒜 ↔ (insert i s ∈ 𝒜) ∧ (s ∈ 𝒜) := by
  rw [Down.mem_compression, Finset.erase_insert hi, Finset.insert_idem]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, h2⟩
    · exact absurd h2 h1
  · rintro ⟨h1, h2⟩
    exact Or.inl ⟨h1, h2⟩

omit [Fintype E] in




theorem nonMemberFiber_to_union (i : E) (𝒜 : Finset (Finset E)) {s : Finset E} (hi : i ∉ s) :
    s ∈ Down.compression i 𝒜 ↔ (insert i s ∈ 𝒜) ∨ (s ∈ 𝒜) := by
  rw [Down.mem_compression, Finset.erase_eq_of_notMem hi]
  constructor
  · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
    · exact Or.inr h1
    · exact Or.inl h2
  · rintro (h | h)
    · by_cases hs : s ∈ 𝒜
      · exact Or.inl ⟨hs, hs⟩
      · exact Or.inr ⟨hs, h⟩
    · exact Or.inl ⟨h, h⟩









def raiseCoord (i : E) (ω : ConfigSpace E) : ConfigSpace E := Function.update ω i true

omit [Fintype E] in
@[simp] lemma raiseCoord_self (i : E) (ω : ConfigSpace E) : raiseCoord i ω i = true := by
  simp [raiseCoord]

omit [Fintype E] in
lemma raiseCoord_of_ne {i j : E} (h : j ≠ i) (ω : ConfigSpace E) :
    raiseCoord i ω j = ω j := by simp [raiseCoord, Function.update_of_ne h]




lemma cfgSupport_raiseCoord (i : E) (ω : ConfigSpace E) :
    cfgSupport (raiseCoord i ω) = insert i (cfgSupport ω) := by
  ext j
  simp only [mem_cfgSupport, raiseCoord, Function.update, Finset.mem_insert, mem_cfgSupport]
  by_cases h : j = i
  · subst h; simp
  · simp [h]




lemma mem_image_cfgSupport_iff (𝒜 : Finset (ConfigSpace E)) (ω : ConfigSpace E) :
    cfgSupport ω ∈ 𝒜.image cfgSupport ↔ ω ∈ 𝒜 := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨ω', hω', heq⟩
    have hωeq : ω' = ω := by
      have := congrArg supportCfg heq
      rwa [supportCfg_cfgSupport, supportCfg_cfgSupport] at this
    rwa [hωeq] at hω'
  · intro hω; exact ⟨ω, hω, rfl⟩









theorem rc_memberFiber_to_inter (i : E) (𝒜 : Finset (ConfigSpace E)) {ω : ConfigSpace E}
    (hω : ω i = false) :
    raiseCoord i ω ∈ downCompress i 𝒜 ↔ (raiseCoord i ω ∈ 𝒜) ∧ (ω ∈ 𝒜) := by
  have hi : i ∉ cfgSupport ω := by simp [mem_cfgSupport, hω]
  rw [mem_downCompress, cfgSupport_raiseCoord,
    memberFiber_to_inter i (𝒜.image cfgSupport) hi,
    ← cfgSupport_raiseCoord, mem_image_cfgSupport_iff, mem_image_cfgSupport_iff]





theorem rc_nonMemberFiber_to_union (i : E) (𝒜 : Finset (ConfigSpace E)) {ω : ConfigSpace E}
    (hω : ω i = false) :
    ω ∈ downCompress i 𝒜 ↔ (raiseCoord i ω ∈ 𝒜) ∨ (ω ∈ 𝒜) := by
  have hi : i ∉ cfgSupport ω := by simp [mem_cfgSupport, hω]
  rw [mem_downCompress, nonMemberFiber_to_union i (𝒜.image cfgSupport) hi,
    ← cfgSupport_raiseCoord, mem_image_cfgSupport_iff, mem_image_cfgSupport_iff]







theorem rc_downCompress_fibers (i : E) (𝒜 : Finset (ConfigSpace E)) {ω : ConfigSpace E}
    (hω : ω i = false) :
    (raiseCoord i ω ∈ downCompress i 𝒜 ↔ (raiseCoord i ω ∈ 𝒜) ∧ (ω ∈ 𝒜)) ∧
    (ω ∈ downCompress i 𝒜 ↔ (raiseCoord i ω ∈ 𝒜) ∨ (ω ∈ 𝒜)) :=
  ⟨rc_memberFiber_to_inter i 𝒜 hω, rc_nonMemberFiber_to_union i 𝒜 hω⟩









private noncomputable def ind (p : Prop) [Decidable p] : ℕ := if p then 1 else 0





theorem rc_downCompress_fiber_count (i : E) (𝒜 : Finset (ConfigSpace E)) {ω : ConfigSpace E}
    (hω : ω i = false) :
    ind (raiseCoord i ω ∈ downCompress i 𝒜) + ind (ω ∈ downCompress i 𝒜)
      = ind (raiseCoord i ω ∈ 𝒜) + ind (ω ∈ 𝒜) := by
  classical
  simp only [ind]
  rw [if_congr (rc_memberFiber_to_inter i 𝒜 hω) rfl rfl,
    if_congr (rc_nonMemberFiber_to_union i 𝒜 hω) rfl rfl]
  by_cases hm : raiseCoord i ω ∈ 𝒜 <;> by_cases hn : ω ∈ 𝒜 <;>
    simp [hm, hn]









theorem rc_fiber_univ_high (i : E) {ω : ConfigSpace E} (hω : ω i = false) :
    raiseCoord i ω ∈ downCompress i (Finset.univ : Finset (ConfigSpace E)) := by
  rw [rc_memberFiber_to_inter i _ hω]
  exact ⟨Finset.mem_univ _, Finset.mem_univ _⟩




theorem rc_fiber_empty_low (i : E) {ω : ConfigSpace E} (hω : ω i = false) :
    ω ∉ downCompress i (∅ : Finset (ConfigSpace E)) := by
  rw [rc_nonMemberFiber_to_union i _ hω]
  rintro (h | h) <;> exact absurd h (Finset.notMem_empty _)






theorem rc_fiber_cases (i : E) (𝒜 : Finset (ConfigSpace E)) {ω : ConfigSpace E}
    (hω : ω i = false) :
    (raiseCoord i ω ∈ downCompress i 𝒜 ↔ (raiseCoord i ω ∈ 𝒜 ∧ ω ∈ 𝒜)) ∧
    (ω ∈ downCompress i 𝒜 ↔ (raiseCoord i ω ∈ 𝒜 ∨ ω ∈ 𝒜)) :=
  rc_downCompress_fibers i 𝒜 hω

end StatMech.Walls
