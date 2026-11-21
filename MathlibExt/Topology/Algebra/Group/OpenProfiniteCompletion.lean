/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Mathlib/Topology/Algebra/Category/ProfiniteGrp/Limits.lean` (Mathlib):
Copyright (c) 2024 Nailin Guan. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Nailin Guan, Youle Fang, Jujian Zhang, Yuyang Zhao

`Mathlib/Topology/Algebra/Category/ProfiniteGrp/Completion.lean` (Mathlib):
Copyright (c) 2026 Adam Topaz. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Adam Topaz
-/

module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

/-!
# Open profinite completion from open finite-index normal subgroups.

Corrects the source formalization: an open subgroup of an arbitrary
topological group need not have finite index. We index by open *and*
finite-index normal subgroups.
-/

@[expose] public section

open CategoryTheory
open scoped Pointwise

universe u

namespace ProfiniteGrp.OpenProfiniteCompletion

/-- Open finite-index normal subgroups of `G`, the index category. -/
abbrev Index (G : Type u) [Group G] [TopologicalSpace G] :=
  { H : FiniteIndexNormalSubgroup G // IsOpen (H : Set G) }

/-- Finite-group diagram `G ⧸ H` with projection maps. -/
def finiteGrpDiagram (G : Type u) [Group G]
    [TopologicalSpace G] : Index G ⥤ FiniteGrp.{u} where
  obj H := FiniteGrp.of <| G ⧸ H.1.toSubgroup
  map f :=
    FiniteGrp.ofHom <| QuotientGroup.map _ _ (MonoidHom.id _) f.le
  map_id H := by ext ⟨x⟩; rfl
  map_comp f g := by ext ⟨x⟩; rfl

/-- Profinite diagram obtained by forgetting to `ProfiniteGrp`. -/
def diagram (G : Type u) [Group G] [TopologicalSpace G] :
    Index G ⥤ ProfiniteGrp.{u} :=
  finiteGrpDiagram G ⋙ forget₂ (FiniteGrp.{u}) (ProfiniteGrp.{u})

/-- Open profinite completion as the limit of `diagram G`. -/
def completion (G : Type u) [Group G] [TopologicalSpace G] :
    ProfiniteGrp.{u} :=
  ProfiniteGrp.limit (diagram G)

/-- Canonical map `G → completion G` sending `x` to `(mk x)_H`. -/
def etaFn (G : Type u) [Group G] [TopologicalSpace G]
    (x : G) : completion G :=
  ⟨fun _ => QuotientGroup.mk x, fun _ _ _ => rfl⟩

/-- Coordinate evaluation of `etaFn`. -/
@[simp]
theorem etaFn_apply (G : Type u) [Group G] [TopologicalSpace G] (x : G)
    (H : Index G) : ((etaFn G x).val H : G ⧸ H.1.toSubgroup) =
    QuotientGroup.mk x :=
  rfl

/-- Continuity of `etaFn`; needs only separate continuity of `*`. -/
theorem etaFn_continuous (G : Type u) [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] : Continuous (etaFn G) := by
  apply continuous_induced_rng.mpr (continuous_pi _)
  intro H
  apply Continuous.mk
  intro s _hs
  let s' : Set (G ⧸ H.1.toSubgroup) := {x | x ∈ s}
  change IsOpen ((QuotientGroup.mk' H.1.toSubgroup) ⁻¹' s')
  rw [← (Set.biUnion_preimage_singleton (QuotientGroup.mk' H.1.toSubgroup) s')]
  refine isOpen_iUnion (fun i ↦ isOpen_iUnion (fun _ ↦ ?_))
  convert! IsOpen.leftCoset H.2 (Quotient.out i)
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  conv_lhs => rhs; rw [← QuotientGroup.out_eq' i]
  change (↑x : G ⧸ H.1.toSubgroup) = ↑(Quotient.out i) ↔
    x ∈ Quotient.out i • (↑H.1.toSubgroup : Set G)
  rw [eq_comm, QuotientGroup.eq]
  exact Iff.symm Set.mem_smul_set_iff_inv_smul_mem

/-- Canonical continuous monoid hom into the completion. -/
def eta (G : Type u) [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] : G →ₜ* completion G where
  toFun := etaFn G
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := etaFn_continuous G

/-- Algebraic density of `etaFn`, following Mathlib `denseRange`. -/
theorem denseRange_etaFn (G : Type u) [Group G] [TopologicalSpace G] :
    DenseRange (etaFn G) := by
  unfold etaFn completion
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, uDefaultSpec⟩
  rw [← hsv, Set.mem_preimage] at uDefaultSpec
  rcases (isOpen_pi_iff.mp hsO) _ uDefaultSpec with ⟨J, _fJ, hJ1, hJ2⟩
  let M : Subgroup G := iInf fun (j : J) ↦ j.1.1.toSubgroup
  have hMNormal : M.Normal :=
    Subgroup.normal_iInf_normal fun _ ↦ inferInstance
  have hMFinite : M.FiniteIndex := by
    apply Subgroup.finiteIndex_iInf
    infer_instance
  have hMOpen : IsOpen (M : Set G) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun j ↦ j.1.2
  let m : Index G := ⟨{
    toSubgroup := M
    isNormal' := hMNormal
    isFiniteIndex' := hMFinite }, hMOpen⟩
  rcases QuotientGroup.mk'_surjective M (spc m) with ⟨origin, horigin⟩
  use ⟨fun _ ↦ QuotientGroup.mk origin, fun _ _ _ ↦ rfl⟩
  refine ⟨?_, origin, rfl⟩
  rw [← hsv]
  apply hJ2
  intro a a_in_J
  let M_to_Na : m ⟶ a :=
    (iInf_le (fun (j : J) ↦ j.1.1.toSubgroup) ⟨a, a_in_J⟩).hom
  rw [← (⟨fun _ ↦ QuotientGroup.mk origin, fun _ _ _ ↦ rfl⟩ :
    ProfiniteGrp.limit (diagram G)).property M_to_Na]
  change (finiteGrpDiagram G).map M_to_Na (QuotientGroup.mk' M origin) ∈ _
  rw [horigin]
  exact Set.mem_of_eq_of_mem (hspc M_to_Na) (hJ1 a a_in_J).2

/-- Corrected endpoint: density of `eta` under separate continuity of `*`. -/
theorem denseRange_eta (G : Type u) [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] : DenseRange (eta G) :=
  denseRange_etaFn G

end ProfiniteGrp.OpenProfiniteCompletion
