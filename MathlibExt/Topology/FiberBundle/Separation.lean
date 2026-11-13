/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Total spaces of fiber bundles are Hausdorff

The total space of a fiber bundle is Hausdorff when the base and the model fiber are
Hausdorff. Points in different fibers are separated through the continuous projection,
while points in the same fiber lie in the open source of one local trivialization.
-/

@[expose] public section

namespace FiberBundle

variable {B : Type*} {F : Type*} {E : B → Type*}
variable [TopologicalSpace B] [TopologicalSpace F]
variable [TopologicalSpace (Bundle.TotalSpace F E)]
variable [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
variable [T2Space B] [T2Space F]

/-- The total space of a fiber bundle over a Hausdorff base with Hausdorff fiber is Hausdorff. -/
instance t2Space_totalSpace : T2Space (Bundle.TotalSpace F E) := by
  rw [t2Space_iff]
  intro x y hxy
  by_cases hproj : x.proj = y.proj
  · have hx : x ∈ (trivializationAt F E x.proj).source :=
      FiberBundle.mem_trivializationAt_proj_source
    have hy0 : y ∈ (trivializationAt F E y.proj).source :=
      FiberBundle.mem_trivializationAt_proj_source
    have hy : y ∈ (trivializationAt F E x.proj).source := by
      rwa [← hproj] at hy0
    have hs : IsOpen (trivializationAt F E x.proj).source :=
      (trivializationAt F E x.proj).toOpenPartialHomeomorph.open_source
    have hec : ContinuousOn ⇑(trivializationAt F E x.proj)
        (trivializationAt F E x.proj).source :=
      Bundle.Trivialization.continuousOn _
    have hinj : Set.InjOn ⇑(trivializationAt F E x.proj)
        (trivializationAt F E x.proj).source :=
      (trivializationAt F E x.proj).toOpenPartialHomeomorph.injOn
    have hval : ContinuousOn
        (Subtype.val : ↥(trivializationAt F E x.proj).source → _) Set.univ :=
      continuous_subtype_val.continuousOn
    have hcomp : ContinuousOn
        ((trivializationAt F E x.proj) ∘ Subtype.val) Set.univ :=
      hec.comp hval (fun p _ => p.property)
    have hf_cont : Continuous
        (fun p : ↥(trivializationAt F E x.proj).source =>
          (trivializationAt F E x.proj) p.val) :=
      continuousOn_univ.mp hcomp
    let a : ↥(trivializationAt F E x.proj).source := ⟨x, hx⟩
    let b : ↥(trivializationAt F E x.proj).source := ⟨y, hy⟩
    have hfab : (trivializationAt F E x.proj) a.val ≠
        (trivializationAt F E x.proj) b.val :=
      fun h => hxy (hinj a.property b.property h)
    obtain ⟨u, v, hu_open, hv_open, hau, hbv, huv⟩ :=
      t2_separation hfab
    have hu_s : IsOpen
        ((fun p : ↥(trivializationAt F E x.proj).source =>
          (trivializationAt F E x.proj) p.val) ⁻¹' u) :=
      hu_open.preimage hf_cont
    have hv_s : IsOpen
        ((fun p : ↥(trivializationAt F E x.proj).source =>
          (trivializationAt F E x.proj) p.val) ⁻¹' v) :=
      hv_open.preimage hf_cont
    obtain ⟨U, hU_open, hU_eq⟩ := isOpen_induced_iff.mp hu_s
    obtain ⟨V, hV_open, hV_eq⟩ := isOpen_induced_iff.mp hv_s
    have hau_mem : a ∈
        ((fun p : ↥(trivializationAt F E x.proj).source =>
          (trivializationAt F E x.proj) p.val) ⁻¹' u) := hau
    have ha_pre : a ∈
        (Subtype.val : ↥(trivializationAt F E x.proj).source → _) ⁻¹' U :=
      hU_eq.symm ▸ hau_mem
    have hxU : x ∈ U := ha_pre
    have hbv_mem : b ∈
        ((fun p : ↥(trivializationAt F E x.proj).source =>
          (trivializationAt F E x.proj) p.val) ⁻¹' v) := hbv
    have hb_pre : b ∈
        (Subtype.val : ↥(trivializationAt F E x.proj).source → _) ⁻¹' V :=
      hV_eq.symm ▸ hbv_mem
    have hyV : y ∈ V := hb_pre
    have hdisj_pre : Disjoint
        ((fun p : ↥(trivializationAt F E x.proj).source =>
          (trivializationAt F E x.proj) p.val) ⁻¹' u)
        ((fun p : ↥(trivializationAt F E x.proj).source =>
          (trivializationAt F E x.proj) p.val) ⁻¹' v) :=
      Set.disjoint_left.mpr (fun p hp1 hp2 =>
        (Set.disjoint_left.mp huv hp1) hp2)
    have hdisjUV : Disjoint
        (U ∩ (trivializationAt F E x.proj).source)
        (V ∩ (trivializationAt F E x.proj).source) := by
      refine Set.disjoint_left.mpr (fun z hz1 hz2 => ?_)
      have hzU : (⟨z, hz1.2⟩ :
          ↥(trivializationAt F E x.proj).source) ∈
          (Subtype.val : ↥(trivializationAt F E x.proj).source → _) ⁻¹' U :=
        hz1.1
      have hzV : (⟨z, hz1.2⟩ :
          ↥(trivializationAt F E x.proj).source) ∈
          (Subtype.val : ↥(trivializationAt F E x.proj).source → _) ⁻¹' V :=
        hz2.1
      have hp_u : (⟨z, hz1.2⟩ :
          ↥(trivializationAt F E x.proj).source) ∈
          ((fun p : ↥(trivializationAt F E x.proj).source =>
            (trivializationAt F E x.proj) p.val) ⁻¹' u) :=
        hU_eq ▸ hzU
      have hp_v : (⟨z, hz1.2⟩ :
          ↥(trivializationAt F E x.proj).source) ∈
          ((fun p : ↥(trivializationAt F E x.proj).source =>
            (trivializationAt F E x.proj) p.val) ⁻¹' v) :=
        hV_eq ▸ hzV
      exact (Set.disjoint_left.mp hdisj_pre hp_u) hp_v
    exact ⟨U ∩ (trivializationAt F E x.proj).source,
      V ∩ (trivializationAt F E x.proj).source,
      hU_open.inter hs, hV_open.inter hs,
      ⟨hxU, hx⟩, ⟨hyV, hy⟩, hdisjUV⟩
  · exact separated_by_continuous (FiberBundle.continuous_proj F E) hproj

end FiberBundle
