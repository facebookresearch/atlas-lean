/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PairingCore
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Op

/-!
# Original indexed pairing cores under opposite and whole simplex isomorphisms

The original index family and every dimension are retained. Opposite
reverses the actual missing-face index; an isomorphism transports the
whole original simplex. The native nondegeneracy, unique-face and
ancestral order equations prove properness and regularity. No new rank
or target lifting condition is supplied.
-/

noncomputable section
universe u v
open CategoryTheory
open scoped Simplicial

namespace SSet.Subcomplex.PairingCore

variable {X : SSet.{u}} {A : X.Subcomplex} (h : PairingCore.{v, u} A)

/-- Opposite keeps the original indexed dimensions and full simplices while reversing their exact
  missing-face indices. -/
def op : A.op.PairingCore where
  ι := h.ι
  dim := h.dim
  simplex s := opObjEquiv.symm (h.simplex s)
  index s := (h.index s).rev
  nonDegenerate₁ s := (opObjEquiv_mem_nonDegenerate_iff X _).mp (h.nonDegenerate₁ s)
  nonDegenerate₂ s := by
    rw [op_δ, Fin.rev_rev, Equiv.apply_symm_apply]
    exact (opObjEquiv_mem_nonDegenerate_iff X _).mp (h.nonDegenerate₂ s)
  notMem₁ s := h.notMem₁ s
  notMem₂ s := by
    rw [op_δ, Fin.rev_rev, Equiv.apply_symm_apply]
    exact h.notMem₂ s
  injective_type₁' hh := h.injective_type₁' (congrArg (S.opEquiv (X := X)) hh)
  injective_type₂' hh := by
    simp only [op_δ, Fin.rev_rev, Equiv.apply_symm_apply] at hh
    exact h.injective_type₂' (congrArg (S.opEquiv (X := X)) hh)
  type₁_ne_type₂' s t hh := by
    simp only [op_δ, Fin.rev_rev, Equiv.apply_symm_apply] at hh
    exact h.type₁_ne_type₂' s t (congrArg (S.opEquiv (X := X)) hh)
  surjective' x := by
    obtain ⟨s, hs | hs⟩ := h.surjective' (Subcomplex.N.opEquiv x)
    · exact ⟨s, Or.inl (congrArg (S.opEquiv (X := X)).symm hs)⟩
    · refine ⟨s, Or.inr ?_⟩
      rw [op_δ, Fin.rev_rev, Equiv.apply_symm_apply]
      exact congrArg (S.opEquiv (X := X)).symm hs

/-- The opposite type-I simplex is precisely the original native opposite simplex. -/
theorem op_type₁ (s : h.ι) : h.op.type₁ s = Subcomplex.N.opEquiv.symm (h.type₁ s) := rfl

/-- Its type-II simplex is the same native opposite face, with the original face index reversed. -/
theorem op_type₂ (s : h.ι) : h.op.type₂ s = Subcomplex.N.opEquiv.symm (h.type₂ s) := by
  apply (Subcomplex.N.ext_iff _ _).mpr
  apply (SSet.N.ext_iff _ _).mpr
  change S.mk (X.op.δ (h.index s).rev (opObjEquiv.symm (h.simplex s))) =
    S.mk (opObjEquiv.symm (X.δ (h.index s) (h.simplex s)))
  rw [op_δ, Fin.rev_rev, Equiv.apply_symm_apply]

/-- The opposite keeps exactly the original ancestral relation on the original index family. -/
theorem op_ancestralRel_iff (s t : h.ι) : h.op.AncestralRel s t ↔ h.AncestralRel s t := by
  change (s ≠ t ∧ h.op.type₂ s < h.op.type₁ t) ↔ (s ≠ t ∧ h.type₂ s < h.type₁ t)
  rw [op_type₁, op_type₂]
  exact and_congr Iff.rfl Subcomplex.N.opEquiv.symm.lt_iff_lt

instance oppositeCoreProper [h.IsProper] : h.op.IsProper where
  isUniquelyCodimOneFace s := by
    have h₂ : (h.op.type₂ s).toS = S.opEquiv.symm (h.type₂ s).toS :=
      congrArg (fun z : A.op.N => z.toS) (h.op_type₂ s)
    have h₁ : (h.op.type₁ s).toS = S.opEquiv.symm (h.type₁ s).toS :=
      congrArg (fun z : A.op.N => z.toS) (h.op_type₁ s)
    exact (congrArg₂ S.IsUniquelyCodimOneFace h₂ h₁).mpr (h.isUniquelyCodimOneFace s).op

instance oppositeCoreRegular [h.IsRegular] : h.op.IsRegular where
  wf := by
    have he : h.op.AncestralRel = h.AncestralRel := by
      funext s t
      exact propext (h.op_ancestralRel_iff s t)
    rw [he]
    exact IsRegular.wf h

variable {Y : SSet.{u}} {B : Y.Subcomplex} (e : Y ≅ X) (hA : A.preimage e.hom = B)

/-- Transport each entire original indexed simplex through the supplied isomorphism, retaining every
  dimension and missing-face index. -/
def ofIso : B.PairingCore where
  ι := h.ι
  dim := h.dim
  simplex s := e.inv.app _ (h.simplex s)
  index := h.index
  nonDegenerate₁ s := (nonDegenerate_iff_of_isIso e.inv _).mpr (h.nonDegenerate₁ s)
  nonDegenerate₂ s := by
    rw [← SSet.δ_naturality_apply]
    exact (nonDegenerate_iff_of_isIso e.inv _).mpr (h.nonDegenerate₂ s)
  notMem₁ s := by
    have hB : B.preimage e.inv = A := by rw [← hA, ← preimage_comp, e.inv_hom_id, preimage_id]
    exact hB ▸ h.notMem₁ s
  notMem₂ s := by
    rw [← SSet.δ_naturality_apply]
    have hB : B.preimage e.inv = A := by rw [← hA, ← preimage_comp, e.inv_hom_id, preimage_id]
    exact hB ▸ h.notMem₂ s
  injective_type₁' hh := by
    apply h.injective_type₁'
    have hz := congrArg (S.equivOfIso e) hh
    simpa [S.equivOfIso] using hz
  injective_type₂' hh := by
    apply h.injective_type₂'
    have hz := congrArg (S.equivOfIso e) hh
    simpa [S.equivOfIso, ← SSet.δ_naturality_apply] using hz
  type₁_ne_type₂' s t hh := by
    apply h.type₁_ne_type₂' s t
    have hz := congrArg (S.equivOfIso e) hh
    simpa [S.equivOfIso, ← SSet.δ_naturality_apply] using hz
  surjective' x := by
    obtain ⟨s, hs | hs⟩ := h.surjective' (Subcomplex.N.orderIsoOfIso e hA x)
    · change (S.equivOfIso e) x.toS = S.mk (h.simplex s) at hs
      exact ⟨s, Or.inl (((S.equivOfIso e).symm_apply_eq).mpr hs.symm).symm⟩
    · change (S.equivOfIso e) x.toS = S.mk (X.δ (h.index s) (h.simplex s)) at hs
      refine ⟨s, Or.inr ?_⟩
      rw [← SSet.δ_naturality_apply]
      exact (((S.equivOfIso e).symm_apply_eq).mpr hs.symm).symm

/-- The transported type-I simplex is exactly the inverse image of the same original native
  simplex. -/
theorem ofIso_type₁ (s : h.ι) :
    (h.ofIso e hA).type₁ s = (Subcomplex.N.orderIsoOfIso e hA).symm (h.type₁ s) := rfl

/-- The transported type-II simplex retains the original whole face under the same inverse
  isomorphism. -/
theorem ofIso_type₂ (s : h.ι) :
    (h.ofIso e hA).type₂ s = (Subcomplex.N.orderIsoOfIso e hA).symm (h.type₂ s) := by
  apply (Subcomplex.N.ext_iff _ _).mpr
  apply (SSet.N.ext_iff _ _).mpr
  change S.mk (Y.δ (h.index s) (e.inv.app _ (h.simplex s))) =
    S.mk (e.inv.app _ (X.δ (h.index s) (h.simplex s)))
  rw [← SSet.δ_naturality_apply]

/-- The original ancestral relation and original index family are unchanged by the entire simplex
  isomorphism. -/
theorem ofIso_ancestralRel_iff (s t : h.ι) :
    (h.ofIso e hA).AncestralRel s t ↔ h.AncestralRel s t := by
  change (s ≠ t ∧ (h.ofIso e hA).type₂ s < (h.ofIso e hA).type₁ t) ↔
    (s ≠ t ∧ h.type₂ s < h.type₁ t)
  rw [ofIso_type₁, ofIso_type₂]
  exact and_congr Iff.rfl (Subcomplex.N.orderIsoOfIso e hA).symm.lt_iff_lt

instance isoCoreProper [h.IsProper] : (h.ofIso e hA).IsProper where
  isUniquelyCodimOneFace s := by
    have h₂ : ((h.ofIso e hA).type₂ s).toS = (S.equivOfIso e).symm (h.type₂ s).toS :=
      congrArg (fun z : B.N => z.toS) (h.ofIso_type₂ e hA s)
    have h₁ : ((h.ofIso e hA).type₁ s).toS = (S.equivOfIso e).symm (h.type₁ s).toS :=
      congrArg (fun z : B.N => z.toS) (h.ofIso_type₁ e hA s)
    exact (congrArg₂ S.IsUniquelyCodimOneFace h₂ h₁).mpr
      ((h.isUniquelyCodimOneFace s).of_iso e.symm)

instance isoCoreRegular [h.IsRegular] : (h.ofIso e hA).IsRegular where
  wf := by
    have he : (h.ofIso e hA).AncestralRel = h.AncestralRel := by
      funext s t
      exact propext (h.ofIso_ancestralRel_iff e hA s t)
    rw [he]
    exact IsRegular.wf h

end SSet.Subcomplex.PairingCore
