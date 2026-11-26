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
# Continuous factor coordinates for an open-subgroup transversal

Let `H` be an open subgroup of a topological group `G` and `T` a right transversal, so every `g`
has a unique decomposition `g=ht` with `h∈H`, `t∈T`.

The representative function `g ↦ t` is locally constant. Both coordinates of the complement
equivalence `G ≃ H×T` are continuous. Normality of `H` is not required.
-/

@[expose] public section

namespace Subgroup.IsComplement

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Subgroup G} {T : Set G}

/-- **Locally constant representative of an open-subgroup right coset.** Let `G` be a
topological group, `H≤G` open and `T` a right transversal with unique factorization
`g=ht`, `h∈H`, `t∈T`. The function selecting `t` is locally constant. -/
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

/-- **Continuous transversal coordinate of the group complement equivalence.** For an open
subgroup `H` of a topological group `G` and right transversal `T`, the map `g ↦ t∈T` in
the unique factorization `g=ht` is continuous. -/
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

/-- **Continuous subgroup coordinate of the group complement equivalence.** For an open
subgroup `H` of a topological group `G` and right transversal `T`, the map `g ↦ h∈H` in
`g=ht` is continuous. The subgroup need not be normal. -/
theorem continuous_equiv_fst (hT : IsComplement (H : Set G) T)
    (hOpen : IsOpen (H : Set G)) : Continuous (fun g : G => (hT.equiv g).1) := by
  apply Continuous.subtype_mk
  have hs := (hT.continuous_equiv_snd hOpen).subtype_val
  have hmul : Continuous (fun g : G => g * ((hT.equiv g).2 : G)⁻¹) :=
    continuous_id.mul hs.inv
  simpa only [equiv_fst_eq_mul_inv] using hmul

end Subgroup.IsComplement
