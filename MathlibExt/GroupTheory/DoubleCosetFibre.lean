/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_DoubleCoset_natCard_fibre_quotient_eq_natCard_quotient_inf_map_conj.lean`
and
`P2M/Sol/S_DoubleCoset_natCard_fibre_quotient_eq_natCard_quotient_inf_map_conj.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

@[expose] public section

open scoped Pointwise

namespace DoubleCoset

private def conjStab {G : Type*} [Group G] (V : Subgroup G) (β : G) : Subgroup G :=
  V.map (MulAut.conj β).toMonoidHom

private theorem mem_conjStab {G : Type*} [Group G] {V : Subgroup G} {β x : G} :
    x ∈ conjStab V β ↔ ∃ μ ∈ V, β * μ * β⁻¹ = x := by
  simp only [conjStab, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

private def fibrationMap {G : Type*} [Group G] {Γ U V : Subgroup G} (hΓU : Γ ≤ U) :
    DoubleCoset.Quotient (Γ : Set G) (V : Set G) →
      DoubleCoset.Quotient (U : Set G) (V : Set G) :=
  Quotient.lift (fun g => DoubleCoset.mk U V g) fun a b hab => by
    obtain ⟨γ, hγ, v, hv, rfl⟩ := DoubleCoset.rel_iff.mp hab
    exact (DoubleCoset.eq.mpr ⟨γ, hΓU hγ, v, hv, rfl⟩)

private theorem fibrationMap_mk {G : Type*} [Group G] {Γ U V : Subgroup G} (hΓU : Γ ≤ U)
    (g : G) :
    fibrationMap (V := V) hΓU (DoubleCoset.mk Γ V g) = DoubleCoset.mk U V g :=
  rfl

private def Fibre {G : Type*} [Group G] {Γ U V : Subgroup G} (hΓU : Γ ≤ U)
    (q : DoubleCoset.Quotient (U : Set G) (V : Set G)) : Type _ :=
  {x : DoubleCoset.Quotient (Γ : Set G) (V : Set G) // fibrationMap hΓU x = q}

private theorem toFibre_mem {G : Type*} [Group G] {Γ U V : Subgroup G} (hΓU : Γ ≤ U)
    (β : G) (ν : U) :
    fibrationMap (V := V) hΓU (DoubleCoset.mk Γ V ((ν : G) * β)) =
      DoubleCoset.mk U V β := by
  rw [fibrationMap_mk]
  exact DoubleCoset.eq.mpr
    ⟨(ν : G)⁻¹, U.inv_mem ν.2, 1, V.one_mem, by group⟩

private noncomputable def fibreEquiv {G : Type*} [Group G] {Γ U V : Subgroup G}
    (hΓU : Γ ≤ U) (β : G) :
    DoubleCoset.Quotient ((Γ.subgroupOf U : Subgroup U) : Set U)
        (((U ⊓ conjStab V β).subgroupOf U : Subgroup U) : Set U) ≃
      Fibre (V := V) hΓU (DoubleCoset.mk U V β) := by
  refine Equiv.ofBijective
    (Quotient.lift
      (fun ν : U =>
        (⟨DoubleCoset.mk Γ V ((ν : G) * β), toFibre_mem hΓU β ν⟩ :
          Fibre (V := V) hΓU (DoubleCoset.mk U V β)))
      ?_) ⟨?_, ?_⟩
  · intro ν ν' hrel
    obtain ⟨a, ha, b, hb, hb'⟩ := DoubleCoset.rel_iff.mp hrel
    obtain ⟨μ, hμ, hμ'⟩ := mem_conjStab.mp (Subgroup.mem_subgroupOf.mp hb).2
    refine Subtype.ext ?_
    refine DoubleCoset.eq.mpr
      ⟨(a : G), Subgroup.mem_subgroupOf.mp ha, μ, hμ, ?_⟩
    have hcoe : (ν' : G) = (a : G) * (ν : G) * (b : G) := congrArg Subtype.val hb'
    rw [hcoe, ← hμ']
    group
  · intro q q'
    induction q using Quotient.inductionOn' with
    | h ν =>
      induction q' using Quotient.inductionOn' with
      | h ν' =>
        intro hqq'
        have h1 : DoubleCoset.mk Γ V ((ν : G) * β) = DoubleCoset.mk Γ V ((ν' : G) * β) :=
          congrArg Subtype.val hqq'
        obtain ⟨γ, hγ, μ, hμ, key⟩ := DoubleCoset.eq.mp h1
        have h2 : (ν' : G) = γ * ((ν : G) * β) * μ * β⁻¹ := by
          rw [← key]; group
        have hkey : (ν : G)⁻¹ * γ⁻¹ * (ν' : G) = β * μ * β⁻¹ := by
          rw [h2]; group
        have hsU : (ν : G)⁻¹ * γ⁻¹ * (ν' : G) ∈ U :=
          U.mul_mem (U.mul_mem (U.inv_mem ν.2) (U.inv_mem (hΓU hγ))) ν'.2
        have hsconj : (ν : G)⁻¹ * γ⁻¹ * (ν' : G) ∈ conjStab V β :=
          mem_conjStab.mpr ⟨μ, hμ, hkey.symm⟩
        refine DoubleCoset.eq.mpr
          ⟨⟨γ, hΓU hγ⟩, Subgroup.mem_subgroupOf.mpr hγ,
           ⟨(ν : G)⁻¹ * γ⁻¹ * (ν' : G), hsU⟩,
           Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hsU, hsconj⟩), ?_⟩
        refine Subtype.ext ?_
        show (ν' : G) = γ * (ν : G) * ((ν : G)⁻¹ * γ⁻¹ * (ν' : G))
        group
  · rintro ⟨x, hx⟩
    induction x using Quotient.inductionOn' with
    | h g =>
      rw [show (Quotient.mk'' g : DoubleCoset.Quotient (Γ : Set G) (V : Set G)) =
            DoubleCoset.mk Γ V g from rfl, fibrationMap_mk] at hx
      obtain ⟨u, hu, v, hv, hβ⟩ := DoubleCoset.eq.mp hx
      refine ⟨Quotient.mk'' ⟨u⁻¹, U.inv_mem hu⟩, Subtype.ext ?_⟩
      show DoubleCoset.mk Γ V (u⁻¹ * β) = DoubleCoset.mk Γ V g
      exact DoubleCoset.eq.mpr
        ⟨1, Γ.one_mem, v⁻¹, V.inv_mem hv, by rw [hβ]; group⟩

private theorem card_fibre {G : Type*} [Group G] {Γ U V : Subgroup G} (hΓU : Γ ≤ U)
    (β : G) :
    Nat.card (Fibre (V := V) hΓU (DoubleCoset.mk U V β)) =
      Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf U : Subgroup U) : Set U)
        (((U ⊓ conjStab V β).subgroupOf U : Subgroup U) : Set U)) :=
  (Nat.card_congr (fibreEquiv hΓU β)).symm

private def fibreInlineEquiv {G : Type*} [Group G] {Γ U V : Subgroup G} (hΓU : Γ ≤ U)
    (β : G) :
    {q : DoubleCoset.Quotient (Γ : Set G) (V : Set G) //
        ∃ g : G, DoubleCoset.mk Γ V g = q ∧ DoubleCoset.mk U V g = DoubleCoset.mk U V β} ≃
      Fibre (V := V) hΓU (DoubleCoset.mk U V β) :=
  Equiv.subtypeEquivRight fun q => by
    constructor
    · rintro ⟨g, rfl, hg⟩
      rw [show DoubleCoset.mk Γ V g =
          (Quotient.mk'' g : DoubleCoset.Quotient (Γ : Set G) (V : Set G)) from rfl,
        fibrationMap_mk]
      exact hg
    · intro hq
      induction q using Quotient.inductionOn' with
      | h g => exact ⟨g, rfl, by rwa [fibrationMap_mk] at hq⟩

/-- The fibre of the natural map `Γ \ G / V → U \ G / V` over the double coset
of `β` has the cardinality of the double-coset quotient of `U` by
`Γ` (viewed in `U`) and by `U ∩ β V β⁻¹` (viewed in `U`). -/
public theorem natCard_fibre_quotient_eq_natCard_quotient_inf_map_conj
    {G : Type*} [Group G] {Γ U : Subgroup G} (V : Subgroup G) (hΓU : Γ ≤ U) (β : G) :
    Nat.card {q : DoubleCoset.Quotient (Γ : Set G) (V : Set G) //
        ∃ g : G, DoubleCoset.mk Γ V g = q ∧ DoubleCoset.mk U V g = DoubleCoset.mk U V β}
      = Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf U : Subgroup U) : Set U)
          (((U ⊓ V.map (MulAut.conj β).toMonoidHom).subgroupOf U : Subgroup U) : Set U)) :=
  (Nat.card_congr (fibreInlineEquiv (V := V) hΓU β)).trans (card_fibre hΓU β)

end DoubleCoset
