/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































import Code.Walls.rc5_core

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace







section Ingredients

variable {β : Type*} [DecidableEq β]






theorem rc11_engine_count_identity (𝒜 ℬ : Finset (Finset β)) :
    (boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ :=
  rc5_doubled_box_count 𝒜 ℬ





theorem rc11_engine_downDown_mono (𝒜 ℬ : Finset (Finset β)) (i : β) :
    dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) :=
  rc5_dpairsCount_downDown_mono 𝒜 ℬ i





theorem rc11_engine_deficit_identity (𝒜 ℬ : Finset (Finset β)) (i : β) :
    (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ) - dpairsCount 𝒜 ℬ
      = (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ)
        - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i)
            (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i) :=
  rc5_deficit_identity 𝒜 ℬ i




theorem rc11_engine_sweep_card (cs : List β) (𝒜 : Finset (Finset β)) :
    (iterDownComp cs 𝒜).card = 𝒜.card :=
  rc5_iterDownComp_card cs 𝒜





theorem rc11_engine_converges (𝒜 ℬ : Finset (Finset β)) :
    ∃ cs : List β, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset β))
      ∧ dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ) := by
  obtain ⟨cs, hcs, hmono, _⟩ := rc2_blendpoint_converges 𝒜
  exact ⟨cs, hcs, hmono ℬ⟩






theorem rc11_engine_harrisKleitman (𝒜 ℬ : Finset (Finset β))
    (h𝒜 : IsLowerSet (𝒜 : Set (Finset β))) (hℬ : IsLowerSet (ℬ : Set (Finset β))) (i : β) :
    dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i)
      ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i) :=
  rc2_blendpoint_favourable h𝒜 hℬ i

end Ingredients








section Engine

variable {β : Type*} [DecidableEq β]





















theorem rc11_compressionEngine (𝒜 ℬ : Finset (Finset β)) :
    ((boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ)
      ∧ (∀ i : β, dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ))
      ∧ (∀ i : β, (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ)
            - dpairsCount 𝒜 ℬ
          = (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ)
            - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i)
                (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i))
      ∧ (∀ cs : List β, (iterDownComp cs 𝒜).card = 𝒜.card)
      ∧ (∃ cs : List β, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset β))
            ∧ dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ))
      ∧ (IsLowerSet (𝒜 : Set (Finset β)) → IsLowerSet (ℬ : Set (Finset β)) → ∀ i : β,
            dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i)
              ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)) :=
  ⟨rc11_engine_count_identity 𝒜 ℬ,
    fun i => rc11_engine_downDown_mono 𝒜 ℬ i,
    fun i => rc11_engine_deficit_identity 𝒜 ℬ i,
    fun cs => rc11_engine_sweep_card cs 𝒜,
    rc11_engine_converges 𝒜 ℬ,
    fun h𝒜 hℬ i => rc11_engine_harrisKleitman 𝒜 ℬ h𝒜 hℬ i⟩





theorem rc11_compressionEngine_eq_core (𝒜 ℬ : Finset (Finset β)) :
    rc11_compressionEngine 𝒜 ℬ = rc5_core_compressionEngine 𝒜 ℬ :=
  rfl

end Engine









section Deficit

variable {β : Type*} [DecidableEq β]







theorem rc11_engine_gain_nonneg (𝒜 ℬ : Finset (Finset β)) (i : β) :
    (0 : ℤ) ≤ (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ)
        - dpairsCount 𝒜 ℬ := by
  rw [rc11_engine_deficit_identity 𝒜 ℬ i]
  have h := rc5_deficit_nonneg 𝒜 ℬ i
  linarith

end Deficit








section Nonvacuity





theorem rc11_engine_count_identity_collapse :
    (boxDoubled rc5_collapseFamily rc5_collapseFamily).card = 3 :=
  rc5_collapse_boxDoubled



theorem rc11_engine_count_identity_empty_left {β : Type*} [DecidableEq β]
    (ℬ : Finset (Finset β)) :
    (boxDoubled (∅ : Finset (Finset β)) ℬ).card = 0 :=
  rc5_doubled_box_count_empty_left ℬ

end Nonvacuity

end StatMech.Walls
