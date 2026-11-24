/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.ConeSimplexBoundary
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

/-!
# Actual over-slice lifting at an intrinsic terminal vertex

The full terminal-boundary criterion supplies actual lifts for the
original over-slice projection against every standard boundary. The
existing monomorphism lifting-class theorem then supplies lifts against
any original monomorphism. Both the entire prescribed source cone and
the original projected map are retained; no relative filler is assumed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SSet.WalkingAdjunction.TerminalCorner

variable {H : SSet.{u}} (t : (Δ[0] : SSet.{u}) ⟶ H)

/-- The original over-slice projection is the whole base of its original cone. -/
theorem cone_base {A : SSet.{u}} (q : A ⟶ sliceOver H t) :
    joinInl A Δ[0] ≫ (sliceOver.homEquiv H t A q).val = q ≫ sliceOver.proj H t := by
  rw [sliceOver.homEquiv_apply]
  dsimp only [Subtype.val]
  rw [← Category.assoc, ← map_comp_joinInl, Category.assoc, sliceOver.joinInl_evaluation]

private theorem cone_precomp {A B : SSet.{u}} (q : B ⟶ sliceOver H t) (i : A ⟶ B) :
    (sliceOver.homEquiv H t A (i ≫ q)).val =
      (join.map i).app Δ[0] ≫ (sliceOver.homEquiv H t B q).val := by
  simp only [sliceOver.homEquiv_apply, Category.assoc,
    CategoryTheory.Functor.map_comp, NatTrans.comp_app]

/-- Intrinsic terminality gives actual original over-slice boundary lifts in every dimension. -/
theorem hasLiftingProperty_boundary (ht : RightTerminalVertex t) (n : ℕ) :
    HasLiftingProperty (SSet.boundary n).ι (sliceOver.proj H t) where
  sq_hasLift {top bottom} sq := by
    let d : ConeSimplexBoundary.Data n H := {
      leading := bottom
      cone := (sliceOver.homEquiv H t (∂Δ[n] : SSet.{u}) top).val
      base := (cone_base t top).trans sq.w }
    have ha : ConeSimplexBoundary.apex d = t :=
      (sliceOver.homEquiv H t (∂Δ[n] : SSet.{u}) top).property
    have hd : RightTerminalVertex (ConeSimplexBoundary.apex d) := ha.symm ▸ ht
    obtain ⟨q, qb, qc⟩ := ConeSimplexBoundary.exists_terminal_extension d hd
    have qa : joinInr (Δ[n] : SSet.{u}) Δ[0] ≫ q = t := by
      have h := congrArg (fun f => joinInr (∂Δ[n] : SSet.{u}) Δ[0] ≫ f) qc
      rw [← Category.assoc, joinInr_comp_map] at h
      exact h.trans ha
    let l : (Δ[n] : SSet.{u}) ⟶ sliceOver H t := (sliceOver.homEquiv H t Δ[n]).symm ⟨q, qa⟩
    have hl : (sliceOver.homEquiv H t Δ[n] l).val = q :=
      congrArg Subtype.val ((sliceOver.homEquiv H t Δ[n]).apply_symm_apply ⟨q, qa⟩)
    refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
    · apply (sliceOver.homEquiv H t (∂Δ[n] : SSet.{u})).injective
      apply Subtype.ext
      rw [cone_precomp, hl]
      exact qc
    · exact (cone_base t l).symm.trans ((congrArg (fun f => joinInl Δ[n] Δ[0] ≫ f) hl).trans qb)

/-- The actual over-slice projection at an intrinsic terminal vertex lifts every monomorphism. -/
theorem hasLiftingProperty_mono (ht : RightTerminalVertex t)
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i] : HasLiftingProperty i (sliceOver.proj H t) := by
  have hp : modelCategoryQuillen.I.rlp (sliceOver.proj H t) := by
    rintro _ _ _ ⟨n⟩
    exact hasLiftingProperty_boundary t ht n
  have hm : (MorphismProperty.monomorphisms SSet.{u}).rlp (sliceOver.proj H t) := by
    rw [SSet.rlp_monomorphisms]
    exact hp
  exact hm i (MorphismProperty.monomorphisms.infer_property i)

end SSet.WalkingAdjunction.TerminalCorner
