/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Separability along open maps

An open map with separable target and separable fibers has separable source.
For an additive homomorphism, its nonempty fibers are translations of its
actual kernel. Neither a continuous section nor a splitting is assumed.
-/

@[expose] public section

open Set TopologicalSpace Topology

universe uX uY uG uH

/-- Let `X` and `Y` be topological spaces, with `Y` separable. Assume the map `f : X → Y` is open
and each subspace fibre of `f` is separable.

An open map with separable target and separable fibers has separable source. The map need not be
continuous or surjective. -/
theorem IsOpenMap.separableSpace_of_separable_fibers
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    [SeparableSpace Y] {f : X → Y} (hf : IsOpenMap f)
    (hFib : ∀ y : Y, SeparableSpace {x : X // f x = y}) : SeparableSpace X := by
  classical
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense Y
  have hFiberDense (y : Y) :
      ∃ d : Set {x : X // f x = y}, d.Countable ∧ Dense d := by
    let : SeparableSpace {x : X // f x = y} := hFib y
    exact exists_countable_dense _
  choose d hdc hdd using hFiberDense
  let S : Set X := ⋃ y ∈ D, Subtype.val '' d y
  refine ⟨⟨S, hDc.biUnion (fun y _ ↦ (hdc y).image Subtype.val), ?_⟩⟩
  refine dense_iff_inter_open.2 fun U hU hUne ↦ ?_
  obtain ⟨y, hyU, hyD⟩ := hDd.inter_open_nonempty (f '' U) (hf U hU) (hUne.image f)
  obtain ⟨x, hxU, hfx⟩ := hyU
  have hOpen : IsOpen (Subtype.val ⁻¹' U : Set {z : X // f z = y}) :=
    hU.preimage continuous_subtype_val
  obtain ⟨z, hzU, hzd⟩ := (hdd y).inter_open_nonempty
    (Subtype.val ⁻¹' U) hOpen ⟨⟨x, hfx⟩, hxU⟩
  refine ⟨z.val, hzU, ?_⟩
  exact mem_iUnion.2 ⟨y, mem_iUnion.2 ⟨hyD, mem_image_of_mem Subtype.val hzd⟩⟩

/-- Let `G` be a topological additive group and let `H` be a separable topological space with an
additive-group structure. Assume the additive homomorphism `f : G → H` is open and its kernel is
separable.

An open additive homomorphism into a separable space has separable domain when its kernel is
separable. No target group topology or continuity of the homomorphism is required. -/
theorem IsOpenMap.separableSpace_of_separable_ker
    {G : Type uG} {H : Type uH} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [AddGroup H] [TopologicalSpace H]
    [SeparableSpace H] (f : G →+ H) (hf : IsOpenMap f)
    [SeparableSpace f.ker] : SeparableSpace G := by
  classical
  apply hf.separableSpace_of_separable_fibers
  intro y
  cases isEmpty_or_nonempty {x : G // f x = y} with
  | inl hEmpty =>
      let := hEmpty
      infer_instance
  | inr hNonempty =>
      let x : {x : G // f x = y} := Classical.choice hNonempty
      let translate : f.ker → {z : G // f z = y} := fun k ↦
        ⟨k.val + x.val, by
          rw [map_add, (AddMonoidHom.mem_ker).1 k.property, zero_add, x.property]⟩
      have hContinuous : Continuous translate :=
        (continuous_subtype_val.add continuous_const).subtype_mk _
      have hSurjective : Function.Surjective translate := by
        intro z
        refine ⟨⟨z.val - x.val, ?_⟩, ?_⟩
        · exact (AddMonoidHom.mem_ker).2 (by rw [map_sub, z.property, x.property, sub_self])
        · apply Subtype.ext
          exact sub_add_cancel z.val x.val
      exact hSurjective.denseRange.separableSpace hContinuous
