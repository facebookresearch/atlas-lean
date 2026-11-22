/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Algebra.StrongCompleteness

-- The predicate applies to every finite-index subgroup.
example (G : Type*) [Group G] [TopologicalSpace G] (h : IsStronglyComplete G)
    (H : Subgroup G) (hH : H.FiniteIndex) : IsOpen (H : Set G) :=
  h H hH

-- Discrete groups are strongly complete: every subgroup is open.
example (G : Type*) [Group G] [TopologicalSpace G] [DiscreteTopology G] :
    IsStronglyComplete G :=
  fun _H _ => isOpen_discrete _

-- Specialization of the profinite characterization.
example (P : ProfiniteGrp.{0}) :
    IsStronglyComplete ↥P ↔
      Function.Bijective (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of ↥P)) :=
  ProfiniteGrp.ProfiniteCompletion.isStronglyComplete_iff_bijective_etaFn P

-- The closed-subgroup helper needs only surjectivity.
example (P : ProfiniteGrp.{0}) (N : FiniteIndexNormalSubgroup (GrpCat.of ↥P))
    (hsurj : Function.Surjective
      (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of ↥P))) :
    IsClosed (N.toSubgroup : Set ↥P) :=
  ProfiniteGrp.ProfiniteCompletion.isClosed_toSubgroup_of_surjective_etaFn P N hsurj

-- The open-subgroup helper needs only surjectivity.
example (P : ProfiniteGrp.{0}) (N : FiniteIndexNormalSubgroup (GrpCat.of ↥P))
    (hsurj : Function.Surjective
      (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of ↥P))) :
    IsOpen (N.toSubgroup : Set ↥P) :=
  ProfiniteGrp.ProfiniteCompletion.isOpen_toSubgroup_of_surjective_etaFn P N hsurj

-- A concrete finite profinite group: strong completeness holds independently of the
-- characterization because its only subgroup is the whole (one-element) group.
def finiteUnit : ProfiniteGrp :=
  ProfiniteGrp.ofFiniteGrp (FiniteGrp.of Unit)

private theorem finiteUnit_isStronglyComplete : IsStronglyComplete (finiteUnit : Type) := by
  intro H _
  have hH : (H : Set (finiteUnit : Type)) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    cases x
    exact H.one_mem
  rw [hH]
  exact isOpen_univ

-- The characterization now checks bijectivity of the canonical map for this finite example.
example : Function.Bijective
    (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (finiteUnit : Type))) := by
  exact (ProfiniteGrp.ProfiniteCompletion.isStronglyComplete_iff_bijective_etaFn finiteUnit).mp
    finiteUnit_isStronglyComplete

-- An explicit finite-index normal subgroup exercises the open-subgroup helper as well.
example : IsOpen ((⊤ : Subgroup (finiteUnit : Type)) : Set (finiteUnit : Type)) := by
  let N : FiniteIndexNormalSubgroup (GrpCat.of (finiteUnit : Type)) :=
    { toSubgroup := ⊤ }
  have hbij : Function.Bijective
      (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (finiteUnit : Type))) := by
    exact (ProfiniteGrp.ProfiniteCompletion.isStronglyComplete_iff_bijective_etaFn finiteUnit).mp
      finiteUnit_isStronglyComplete
  exact ProfiniteGrp.ProfiniteCompletion.isOpen_toSubgroup_of_surjective_etaFn
    finiteUnit N hbij.2
