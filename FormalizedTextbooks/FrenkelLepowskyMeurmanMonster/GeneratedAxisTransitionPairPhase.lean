/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionOmegaProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalCompletionCode
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismIncidence
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechShortTransitivityCoordinates

/-! Both pair-axis signs are realized inside the actual local Ω centralizer. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every actual source code lift lies in the actual local Ω centralizer. -/
theorem generatedAxis_sourceCode_mem_localOmega (d : Fin 4096) (ε : ZMod 2) :
    inclQ (sourceQCode d ε) ∈ localOmegaStabilizer := by
  rw [localOmegaStabilizer, Subgroup.mem_centralizer_singleton_iff,
    ← map_mul, ← map_mul, sourceQCode_commute_omega]

/-- Either pair-short phase can be chosen without moving the actual Ω element. -/
theorem generatedAxis_pair_localOmega_phase (s : Fin 2) (p : Fin 276) (δ : ZMod 2) :
    ∃ q : Q, inclQ q ∈ localOmegaStabilizer ∧
      localShortPhase (localFiberIncl q) (Sum.inl (s, p)) = δ := by
  let i := (griessCoordinatePair p).1
  let j := (griessCoordinatePair p).2
  have hij : i ≠ j := griessCoordinatePair_ne p
  let a : Fin 2 → Fin 24 := ![i, j]
  have ha : Function.Injective a := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [a]
  obtain ⟨b, hb, hba⟩ := leechShort_extend_tuple (by decide : 2 < 24) a ha
  obtain ⟨f, hf, hfb⟩ := leechShort_extend_tuple (by decide : 3 < 24) b hb
  have hfi : f 0 = i := (hfb 0).trans (hba 0)
  have hfj : f 1 = j := (hfb 1).trans (hba 1)
  obtain ⟨code, hc⟩ := golayCode_four_coordinate_surjective f hf ![δ, 0, 0, 0]
  let d := golayCodeLabelEquiv.symm code
  have hd : golayEncoder (golayLabelCoefficients d) = code.val := by
    exact congrArg Subtype.val (golayCodeLabelEquiv.apply_symm_apply code)
  have hi : code.val i = δ := by
    have h := congrFun hc 0
    simpa [hfi] using h
  have hj : code.val j = 0 := by
    have h := congrFun hc 1
    simpa [hfj] using h
  refine ⟨sourceQCode d 0, generatedAxis_sourceCode_mem_localOmega d 0, ?_⟩
  rw [sourceQCode_pair_phase, hd]
  exact (congrArg₂ (· + ·) hi hj).trans (add_zero δ)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
