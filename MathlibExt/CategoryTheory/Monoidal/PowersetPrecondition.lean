/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Monoidal.PowersetVerification
public import Mathlib.Order.FixedPoints

/-!
# Liberal preconditions and greatest safe feedback invariants

Relational universal preimage, Mathlib's `SetRel.core`, is the backward assertion
transformer right adjoint to direct image. It characterizes powerset verification
and reverses composition, while respecting the disjoint-union tensor comparison.
Every terminating output must satisfy the postcondition; no output is required.

For finite-path feedback, the safe hidden states form the greatest fixed point
of the one-step safety transformer. The external liberal precondition is one
safe step into either a good output or this greatest hidden invariant. In
particular, infinite executions alone cannot violate partial correctness.

The verification setting is that of Arthan, Martin, Mathiesen and Oliva,
*A General Framework for Sound and Complete Floyd-Hoare Logics*, Section 4.3,
https://arxiv.org/abs/0807.1016. The fixed-point characterization here is derived
from the existing finite-path semantics using Mathlib's Knaster–Tarski API.
-/

@[expose] public section
open CategoryTheory MonoidalCategory
open scoped MonoidalCategory
universe u
namespace CategoryTheory.PowersetVerification

/-- Backward partial correctness: all related outputs satisfy the postcondition. -/
def liberalPre {X Y : SumRelCat.{u}} (f : X ⟶ Y) : assertions Y →o assertions X :=
  ⟨f.rel.core, SetRel.core_mono⟩

/-- Relational direct image and liberal precondition are adjoint. -/
theorem image_liberalPre_gc {X Y : SumRelCat.{u}} (f : X ⟶ Y) :
    GaloisConnection (directImage f) (liberalPre f) := f.rel.image_core_gc

/-- Powerset verification is equivalently inclusion in the liberal precondition. -/
theorem map_rel_iff_subset_liberalPre {X Y : SumRelCat.{u}} (f : X ⟶ Y)
    (P : Set X) (Q : Set Y) :
    (P, Q) ∈ (verification.map f).rel ↔ P ⊆ liberalPre f Q :=
  image_liberalPre_gc f P Q

@[simp] theorem liberalPre_id (X : SumRelCat.{u}) :
    liberalPre (𝟙 X) = OrderHom.id := by
  ext Q x
  simp [liberalPre]

@[simp] theorem liberalPre_comp {X Y Z : SumRelCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    liberalPre (f ≫ g) = (liberalPre f).comp (liberalPre g) := by
  ext Q x
  simp only [liberalPre, SumRelCat.rel_comp, OrderHom.coe_mk, OrderHom.comp_coe,
    Function.comp_apply, SetRel.core_comp]

@[simp] theorem liberalPre_univ {X Y : SumRelCat.{u}} (f : X ⟶ Y) :
    liberalPre f Set.univ = Set.univ := SetRel.core_univ

/-- Liberal preconditions preserve conjunction of postconditions. -/
theorem liberalPre_inter {X Y : SumRelCat.{u}} (f : X ⟶ Y) (P Q : Set Y) :
    liberalPre f (P ∩ Q) = liberalPre f P ∩ liberalPre f Q := f.rel.core_inter P Q

/-- The backward transformer respects the powerset tensor comparison. -/
theorem liberalPre_tensor {X Y U V : SumRelCat.{u}} (f : X ⟶ Y) (g : U ⟶ V)
    (Q : Set Y × Set V) :
    liberalPre (f ⊗ₘ g) (tensorOrderIso Y V Q) =
      tensorOrderIso X U (liberalPre f Q.1, liberalPre g Q.2) := by
  ext z
  cases z <;> simp [liberalPre, SetRel.core, Sum.forall, tensorOrderIso]

/-- One-step safety on the hidden wire, with a fixed external postcondition. -/
def feedbackStep {X Y U : SumRelCat.{u}} (f : X ⊗ U ⟶ Y ⊗ U) (Q : Set Y) :
    Set U →o Set U where
  toFun I := {u | Sum.inr u ∈ liberalPre f (tensorOrderIso Y U (Q, I))}
  monotone' := by
    intro I J h u hu
    have hsum : tensorOrderIso Y U (Q, I) ⊆ tensorOrderIso Y U (Q, J) :=
      (tensorOrderIso Y U).monotone ⟨le_rfl, h⟩
    exact (liberalPre f).monotone hsum hu

/-- One safe step into the safe invariant is equivalent to safety of every finite path. -/
theorem mem_liberalPre_safeInvariant_iff {X Y U : SumRelCat.{u}}
    (f : X ⊗ U ⟶ Y ⊗ U) (Q : Set Y) (s : Sum X U) :
    s ∈ liberalPre f (tensorOrderIso Y U (Q, safeInvariant f Q)) ↔
      ∀ y, SumRelCat.FeedbackPath f s y → y ∈ Q := by
  constructor
  · intro hs y hp
    cases hp with
    | output hf => exact (tensorOrderIso_inl Y U _ _).mp (hs hf)
    | step hf hp => exact ((tensorOrderIso_inr Y U _ _).mp (hs hf)) y hp
  · intro hs t hf
    cases t with
    | inl y => exact (tensorOrderIso_inl Y U _ _).mpr (hs y (.output hf))
    | inr v => exact (tensorOrderIso_inr Y U _ _).mpr (fun y hp => hs y (.step hf hp))

/-- Safe hidden states are fixed by one-step backward reasoning. -/
theorem feedbackStep_safeInvariant {X Y U : SumRelCat.{u}}
    (f : X ⊗ U ⟶ Y ⊗ U) (Q : Set Y) :
    feedbackStep f Q (safeInvariant f Q) = safeInvariant f Q := by
  ext v
  exact mem_liberalPre_safeInvariant_iff f Q (Sum.inr v)

/-- Every post-fixed hidden assertion is contained in the safe invariant. -/
theorem subset_safeInvariant {X Y U : SumRelCat.{u}} (f : X ⊗ U ⟶ Y ⊗ U)
    (Q : Set Y) (I : Set U) (hI : I ⊆ feedbackStep f Q I) : I ⊆ safeInvariant f Q := by
  have sound : ∀ {s : Sum X U} {y : Y}, SumRelCat.FeedbackPath f s y →
      s ∈ liberalPre f (tensorOrderIso Y U (Q, I)) → y ∈ Q := by
    intro s y hp
    induction hp with
    | output hf =>
      intro hs
      exact (tensorOrderIso_inl Y U _ _).mp (hs hf)
    | step hf _ ih =>
      intro hs
      exact ih (hI ((tensorOrderIso_inr Y U _ _).mp (hs hf)))
  intro v hv y hp
  exact sound hp (hI hv)

/-- The greatest safe hidden invariant is the greatest fixed point of one-step safety. -/
theorem safeInvariant_eq_gfp {X Y U : SumRelCat.{u}} (f : X ⊗ U ⟶ Y ⊗ U) (Q : Set Y) :
    safeInvariant f Q = (feedbackStep f Q).gfp := by
  apply le_antisymm
  · exact (feedbackStep f Q).le_gfp (feedbackStep_safeInvariant f Q).ge
  · exact (feedbackStep f Q).gfp_le (fun I hI => subset_safeInvariant f Q I hI)

/-- Feedback preconditions are one safe external step into the greatest hidden invariant. -/
theorem liberalPre_feedback {X Y U : SumRelCat.{u}} (f : X ⊗ U ⟶ Y ⊗ U) (Q : Set Y) :
    liberalPre (SumRelCat.feedback f) Q =
      {x | Sum.inl x ∈ liberalPre f (tensorOrderIso Y U (Q, (feedbackStep f Q).gfp))} := by
  rw [← safeInvariant_eq_gfp]
  ext x
  exact (mem_liberalPre_safeInvariant_iff f Q (Sum.inl x)).symm

end CategoryTheory.PowersetVerification
