/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































import Code.Walls.rc6deficitform
import Code.Walls.rc6relabelinvariance
import Code.Walls.rc6eventdowncompression
import Code.Walls.rc6blmonovariant
import Code.Walls.rc6hallavailable
import Code.Walls.rc6canonicalwitness
import Code.Walls.rc6overlapsplit
import Code.Walls.rc6localmirror
import Code.Walls.rc5_core
import Code.Inequalities.Reimer2000Close

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace










section CanonMirror

variable {α : Type*} [Fintype α] [DecidableEq α]

open Classical in




noncomputable def rc6_canonMirror (A B : Set (ConfigSpace α)) (ω : ConfigSpace α) :
    ConfigSpace α :=
  rc6_mirrorL (↑(canonicalWitness A B ω).2.2) ω

open Classical in









theorem rc6_canonMirror_mem (A B : Set (ConfigSpace α)) {ω : ConfigSpace α}
    (hω : ω ∈ disjointOccurrence A B) :
    rc6_canonMirror A B ω ∈ A ∩ rmr_reflect B := by
  obtain ⟨hA, hB, hKL⟩ := canonicalWitness_occursOn hω
  exact rc6_mirrorL_mem (Finset.disjoint_coe.mpr hKL) hA hB

open Classical in


theorem rc6_canonMirror_mapsTo (A B : Set (ConfigSpace α)) :
    Set.MapsTo (rc6_canonMirror A B) (disjointOccurrence A B) (A ∩ rmr_reflect B) :=
  fun _ hω => rc6_canonMirror_mem A B hω






theorem rc6_boxReflectInjection_of_canonMirror_injOn (A B : Set (ConfigSpace α))
    (hinj : Set.InjOn (rc6_canonMirror A B) {ω | ω ∈ disjointOccurrence A B}) :
    rc5_BoxReflectInjection A B :=
  ⟨rc6_canonMirror A B, hinj, fun _ hω => rc6_canonMirror_mem A B hω⟩

end CanonMirror









section MirrorInjectivity

variable {α : Type*} [Fintype α] [DecidableEq α]

open Classical in





def rc6_MirrorInjectivity (A B : Set (ConfigSpace α)) : Prop :=
  ∃ S : ConfigSpace α → (α → Bool),
    (∀ ω, ω ∈ disjointOccurrence A B →
        rc6_mirrorL {a | S ω a = true} ω ∈ A ∩ rmr_reflect B) ∧
      Set.InjOn (fun ω => rc6_mirrorL {a | S ω a = true} ω)
        {ω | ω ∈ disjointOccurrence A B}

open Classical in
omit [Fintype α] [DecidableEq α] in



theorem rc6_boxReflectInjection_of_mirrorInjectivity (A B : Set (ConfigSpace α))
    (h : rc6_MirrorInjectivity A B) : rc5_BoxReflectInjection A B := by
  obtain ⟨S, hmem, hinj⟩ := h
  exact ⟨fun ω => rc6_mirrorL {a | S ω a = true} ω, hinj, hmem⟩

end MirrorInjectivity


















theorem rc6_witnessTied_injectivity_false : ¬ poc_WitnessInjection rbi_A rbi_B :=
  poc_witnessInjection_rbi_false










def rc6_MirrorInjectivityAll : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), rc6_MirrorInjectivity A B





theorem rc6_reimerCardFormAll_of_mirrorInjectivityAll (h : rc6_MirrorInjectivityAll) :
    ReimerCardFormAll :=
  fun n A B =>
    rc5_core_reimerCardForm_of_injection
      (rc6_boxReflectInjection_of_mirrorInjectivity A B (h n A B))







theorem rc6_injectionAll_iff_reimerCardFormAll :
    rc5_BoxReflectInjectionAll ↔ ReimerCardFormAll :=
  rc5_core_injectionAll_iff_reimerCardFormAll

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in



theorem rc6_reimer_inequality_of_injectionAll (h : rc5_BoxReflectInjectionAll) {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  rc5_core_reimer_inequality_of_injectionAll h hp A B






section Engine

variable {β : Type*} [DecidableEq β]







theorem rc6_compressionEngine (𝒜 ℬ : Finset (Finset β)) :
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
  rc5_core_compressionEngine 𝒜 ℬ

end Engine







section Headline

variable {α : Type*} [Fintype α] [DecidableEq α]

open Classical in




















theorem rc6_cardform_all (A B : Set (ConfigSpace α)) :
    (∀ ω, ω ∈ disjointOccurrence A B → rc6_canonMirror A B ω ∈ A ∩ rmr_reflect B)
      ∧ (rc5_BoxReflectInjectionAll ↔ ReimerCardFormAll)
      ∧ (ReimerCardFormAll ↔ ReimerResidue)
      ∧ (rc6_MirrorInjectivityAll → ReimerCardFormAll)
      ∧ ¬ poc_WitnessInjection rbi_A rbi_B :=
  ⟨fun _ hω => rc6_canonMirror_mem A B hω,
    rc6_injectionAll_iff_reimerCardFormAll,
    rc5_core_reimerCardFormAll_iff_residue,
    rc6_reimerCardFormAll_of_mirrorInjectivityAll,
    rc6_witnessTied_injectivity_false⟩

end Headline







section Nonvacuity

variable {α : Type*} [Fintype α] [DecidableEq α]



theorem rc6_injection_rbi : rc5_BoxReflectInjection rbi_A rbi_B :=
  rc5_core_injection_rbi

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in


theorem rc6_injection_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    rc5_BoxReflectInjection A B :=
  rc5_core_injection_of_disjoint_support hA hB hST

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in

theorem rc6_injection_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) : rc5_BoxReflectInjection A B :=
  rc5_core_injection_of_box_empty hbox


theorem rc6_injection_one (A B : Set (ConfigSpace (Fin 1))) : rc5_BoxReflectInjection A B :=
  rc5_core_injection_one A B

end Nonvacuity

end StatMech.Walls
