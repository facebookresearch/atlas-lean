/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsLocallyConstant_exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport.lean`
and
`P2M/Sol/S_IsLocallyConstant_exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport.lean`
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

public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Tactic.Group

/-!
# A uniform stabilizer neighborhood of a locally constant compactly supported function

A locally constant function `Φ` on a topological group is invariant under
right (hence left) multiplication by elements of some open neighborhood `W`
of `1`. The proof covers the support by finitely many translates of
small neighborhoods on which `Φ` is constant.
-/

@[expose] public section

namespace LocallyConstantAux

open Topology Filter Set
open scoped Pointwise

variable {G M : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Zero M]

/-- One-sided version: a locally constant compactly supported function is
invariant under right multiplication by a neighborhood of `1`. -/
private theorem exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport_right
    (Φ : G → M) (hlc : IsLocallyConstant Φ) (hcs : HasCompactSupport Φ) :
    ∃ W : Set G, IsOpen W ∧ (1 : G) ∈ W ∧ ∀ g : G, ∀ w ∈ W, Φ (g * w) = Φ g := by
  classical
  have hO : ∀ g : G, IsOpen (Φ ⁻¹' {Φ g}) := fun g => hlc {Φ g}
  have hV : ∀ g : G, ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧
      V * V ⊆ (fun w => g * w) ⁻¹' (Φ ⁻¹' {Φ g}) := by
    intro g
    have hU : (fun w => g * w) ⁻¹' (Φ ⁻¹' {Φ g}) ∈ 𝓝 (1 : G) := by
      refine ((hO g).preimage (continuous_const_mul g)).mem_nhds ?_
      simp
    obtain ⟨V, hVo, hV1, hVV⟩ := exists_open_nhds_one_mul_subset hU
    exact ⟨V, hVo, hV1, hVV⟩
  choose V hVo hV1 hVV using hV
  set K := tsupport Φ with hK
  have hKc : IsCompact K := hcs
  obtain ⟨t, htK, hcover⟩ := hKc.elim_nhds_subcover
    (fun g => (fun h => g⁻¹ * h) ⁻¹' V g) (by
    intro g _
    refine ((hVo g).preimage (continuous_const_mul g⁻¹)).mem_nhds ?_
    simp [hV1 g])
  refine ⟨⋂ g ∈ t, (V g ∩ (fun w => w⁻¹) ⁻¹' V g), ?_, ?_, ?_⟩
  · refine isOpen_biInter_finset fun g _ => (hVo g).inter ((hVo g).preimage continuous_inv)
  · simp only [mem_iInter, mem_inter_iff, mem_preimage, inv_one]
    exact fun g _ => ⟨hV1 g, hV1 g⟩
  intro h w hw
  simp only [mem_iInter, mem_inter_iff, mem_preimage] at hw
  have key : ∀ g ∈ t, ∀ x v : G, g⁻¹ * x ∈ V g → v ∈ V g → Φ (x * v) = Φ g := by
    intro g hg x v hx hv
    have hmem : g⁻¹ * x * v ∈ V g * V g := Set.mul_mem_mul hx hv
    have := hVV g hmem
    simp only [mem_preimage, mem_singleton_iff] at this
    rw [← this]
    congr 1
    group
  by_cases h1 : h ∈ K
  · obtain ⟨g, hg, hgh⟩ : ∃ g ∈ t, h ∈ (fun h' => g⁻¹ * h') ⁻¹' V g := by
      simpa only [mem_iUnion, exists_prop] using hcover h1
    rw [key g hg h w hgh (hw g hg).1, ← mul_one h, key g hg h 1 hgh (hV1 g)]
  · by_cases h2 : h * w ∈ K
    · obtain ⟨g, hg, hgh⟩ : ∃ g ∈ t, h * w ∈ (fun h' => g⁻¹ * h') ⁻¹' V g := by
        simpa only [mem_iUnion, exists_prop] using hcover h2
      have e1 : Φ (h * w * 1) = Φ g := key g hg (h * w) 1 hgh (hV1 g)
      have e2 : Φ (h * w * w⁻¹) = Φ g := key g hg (h * w) w⁻¹ hgh (hw g hg).2
      rw [mul_one] at e1
      rw [mul_inv_cancel_right] at e2
      rw [e1, e2]
    · have z1 : Φ h = 0 := image_eq_zero_of_notMem_tsupport h1
      have z2 : Φ (h * w) = 0 := image_eq_zero_of_notMem_tsupport h2
      rw [z1, z2]

end LocallyConstantAux

namespace IsLocallyConstant

/-- A locally constant compactly supported function on a topological group is
invariant under left and right multiplication by elements of some open
neighborhood of `1`. -/
theorem exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport
    {G M : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Zero M]
    (Φ : G → M) (hlc : IsLocallyConstant Φ) (hcs : HasCompactSupport Φ) :
    ∃ W : Set G, IsOpen W ∧ (1 : G) ∈ W ∧
      ∀ g : G, ∀ w ∈ W, Φ (g * w) = Φ g ∧ Φ (w * g) = Φ g := by
  obtain ⟨W₁, hW₁o, hW₁1, hW₁⟩ :=
    LocallyConstantAux.exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport_right
      Φ hlc hcs
  let Ψ : Gᵐᵒᵖ → M := fun x => Φ (MulOpposite.unop x)
  have hΨlc : IsLocallyConstant Ψ := hlc.comp_continuous MulOpposite.continuous_unop
  have hΨcs : HasCompactSupport Ψ := hcs.comp_homeomorph MulOpposite.opHomeomorph.symm
  obtain ⟨W₂, hW₂o, hW₂1, hW₂⟩ :=
    LocallyConstantAux.exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport_right
      Ψ hΨlc hΨcs
  refine ⟨W₁ ∩ MulOpposite.op ⁻¹' W₂, hW₁o.inter (hW₂o.preimage MulOpposite.continuous_op),
    ⟨hW₁1, by simpa using hW₂1⟩, fun g w hw => ⟨hW₁ g w hw.1, ?_⟩⟩
  have := hW₂ (MulOpposite.op g) (MulOpposite.op w) hw.2
  simpa [Ψ] using this

end IsLocallyConstant
