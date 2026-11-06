/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOctadNormEightShapes

/-! Coordinate preparation by the actual standard-octad stabilizer. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The integral coordinate E8 section is preserved in both directions. -/
def generatedStandardOctadPreserves (e : leechIsomSubgroup) : Prop :=
  ∀ u : leechIntegral,
    generatedStandardOctadSupported (leechIntegralAction e u).val ↔
      generatedStandardOctadSupported u.val

/-- Preservation composes in the actual lattice action. -/
theorem generatedStandardOctadPreserves_mul (e f : leechIsomSubgroup)
    (he : generatedStandardOctadPreserves e) (hf : generatedStandardOctadPreserves f) :
    generatedStandardOctadPreserves (e * f) := by
  intro u
  rw [map_mul, LinearEquiv.mul_apply]
  exact (he (leechIntegralAction f u)).trans (hf u)

/-- Section preservation also holds for the actual inverse. -/
theorem generatedStandardOctadPreserves_inv (e : leechIsomSubgroup)
    (he : generatedStandardOctadPreserves e) : generatedStandardOctadPreserves e⁻¹ := by
  intro u
  have h := he (leechIntegralAction e⁻¹ u)
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h
  exact h.symm

/-- Four positions in the standard octad can be moved to its first tetrad
by an actual Golay automorphism preserving that octad. -/
theorem generatedStandardOctad_prepare_four (a : Fin 4 → Fin 24)
    (ha : Function.Injective a) (hin : ∀ j, (a j).val < 8) :
    ∃ p : golayAutomorphismSubgroup,
      golayPermute p.val golayStandardOctad = golayStandardOctad ∧
      ∀ j, p.val (a j) = Fin.castAdd 20 j := by
  classical
  let a8 : Fin 4 → Fin 8 := fun j => ⟨(a j).val, hin j⟩
  have ha8 : Function.Injective a8 := by
    intro i j h
    apply ha
    exact Fin.ext (congrArg (fun k : Fin 8 => k.val) h)
  have hn : ¬ Function.Surjective a8 := by
    intro hs
    have hc := Fintype.card_le_of_surjective a8 hs
    norm_num at hc
  obtain ⟨v, hv⟩ : ∃ v : Fin 8, v ∉ Set.range a8 := by
    simpa only [Function.Surjective, Set.mem_range, not_forall, not_exists] using hn
  let a5 : Fin 5 → Fin 8 := Fin.snoc a8 v
  have ha5 : Function.Injective a5 := Fin.snoc_injective_of_injective ha8 hv
  let aa : Fin 5 → Fin 24 := fun j => Fin.castAdd 16 (a5 j)
  let bb : Fin 5 → Fin 24 := fun j => Fin.castAdd 19 j
  have haa : Function.Injective aa := by
    intro i j h
    exact ha5 (Fin.ext (congrArg (fun k : Fin 24 => k.val) h))
  have hbb : Function.Injective bb := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin 24 => k.val) h)
  obtain ⟨p, hp⟩ := golayAutomorphism_five_transitive aa bb haa hbb
  refine ⟨p, ?_, ?_⟩
  · apply golayOctad_unique_through_first_five
      (golayPermute p.val golayStandardOctad) golayStandardOctad
      ((p.property golayStandardOctad).mp golayStandardOctad_mem) golayStandardOctad_mem
      ((Equiv.sum_comp p.val.symm (fun i => (golayStandardOctad i).val)).trans
        golayStandardOctad_weight) golayStandardOctad_weight
    intro i hi
    let j : Fin 5 := ⟨i.val, hi⟩
    have hbi : bb j = i := Fin.ext rfl
    have hpi : p.val.symm i = aa j := by
      rw [← hbi, ← hp j, p.val.symm_apply_apply]
    constructor
    · change golayStandardOctad (p.val.symm i) = 1
      rw [hpi]
      simp [golayStandardOctad, aa]
    · simp [golayStandardOctad, show i.val < 8 by omega]
  · intro j
    have haa' : aa j.castSucc = a j := by
      apply Fin.ext
      simp [aa, a5, a8]
    have hbb' : bb j.castSucc = Fin.castAdd 20 j := Fin.ext rfl
    simpa only [haa', hbb'] using hp j.castSucc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
