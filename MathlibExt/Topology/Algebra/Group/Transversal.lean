/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.GroupTheory.Complement
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Continuity of right transversals of open subgroups

The existing right-coset representative is locally constant when the subgroup is open.
Both components of the existing complement equivalence are then continuous.
-/

@[expose] public section

namespace Subgroup.IsComplement

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Subgroup G} {T : Set G}

/-- The existing right-coset representative of an open subgroup is locally constant. -/
theorem isLocallyConstant_toRightFun (hT : IsComplement (H : Set G) T)
    (hOpen : IsOpen (H : Set G)) : IsLocallyConstant hT.toRightFun := by
  let : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology_iff.mpr hOpen
  have hq : IsLocallyConstant (fun g : G => (QuotientGroup.mk g⁻¹ : G ⧸ H)) :=
    (IsLocallyConstant.iff_continuous _).mpr
      (QuotientGroup.continuous_mk.comp continuous_inv)
  have hc := hq.comp
    (hT.rightQuotientEquiv ∘ (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm)
  have heq (g : G) :
      (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
        (QuotientGroup.mk g⁻¹ : G ⧸ H) = Quotient.mk'' g := by
    change Quotient.mk'' (g⁻¹)⁻¹ = Quotient.mk'' g
    rw [inv_inv]
  simpa only [Function.comp_def, heq, toRightFun] using hc

/-- The transversal component of the existing complement equivalence is continuous. -/
theorem continuous_equiv_snd (hT : IsComplement (H : Set G) T)
    (hOpen : IsOpen (H : Set G)) : Continuous (fun g : G => (hT.equiv g).2) := by
  have heq : hT.toRightFun = fun g => (hT.equiv g).2 := by
    funext g
    apply hT.rightQuotientEquiv.symm.injective
    change Quotient.mk'' (hT.toRightFun g : G) = Quotient.mk'' ((hT.equiv g).2 : G)
    change Quotient.mk'' (hT.rightQuotientEquiv (Quotient.mk'' g) : G) =
      Quotient.mk'' ((hT.equiv g).2 : G)
    rw [mk''_rightQuotientEquiv]
    exact Quotient.sound' (by
      simpa only [QuotientGroup.rightRel_apply, RightCosetEquivalence,
        rightCoset_eq_iff] using hT.rightCosetEquivalence_equiv_snd g)
  rw [← heq]
  exact (hT.isLocallyConstant_toRightFun hOpen).continuous

/-- The subgroup component of the existing complement equivalence is continuous. -/
theorem continuous_equiv_fst (hT : IsComplement (H : Set G) T)
    (hOpen : IsOpen (H : Set G)) : Continuous (fun g : G => (hT.equiv g).1) := by
  apply Continuous.subtype_mk
  have hs := (hT.continuous_equiv_snd hOpen).subtype_val
  have hmul : Continuous (fun g : G => g * ((hT.equiv g).2 : G)⁻¹) :=
    continuous_id.mul hs.inv
  simpa only [equiv_fst_eq_mul_inv] using hmul

end Subgroup.IsComplement
