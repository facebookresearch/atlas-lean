/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import CSLibExt.Languages.IMP.CategoricalHoare
public import MathlibExt.CategoryTheory.Monoidal.PowersetPrecondition

/-!
# IMP liberal preconditions as categorical greatest fixed points

The relational backward transformer agrees with the existing IMP `wlp`.
The guarded while functional is exactly the one-step hidden safety transformer
of the categorical loop body. Thus the generic greatest-safe-invariant theorem
identifies the existing while `wlp` as its greatest fixed point and gives a
coinduction rule for backward reasoning about loops.

This uses the flowchart semantics of Arthan, Martin, Mathiesen and Oliva,
*A General Framework for Sound and Complete Floyd-Hoare Logics*, Section 4.3
and Figure 10, https://arxiv.org/abs/0807.1016. The greatest-fixed-point result
is derived from the existing finite-path and IMP big-step semantics. Assertions
are arbitrary predicates, and the result concerns partial correctness only.
-/

@[expose] public section
namespace Cslib.IMP.CategoricalHoare
open CategoryTheory PowersetVerification

/-- The categorical universal preimage is the existing IMP liberal precondition. -/
theorem liberalPre_commandRel (c : Cmd) (Q : Assertion) :
    liberalPre (commandRel c) {s | Q s} = {s | wlp c Q s} := rfl

/-- Hoare derivability can be checked by inclusion in the categorical precondition. -/
theorem derivable_iff_subset_liberalPre (c : Cmd) (P Q : Assertion) :
    IMP.Derivable P c Q ↔ {s | P s} ⊆ liberalPre (commandRel c) {s | Q s} :=
  (derivable_iff_triple c P Q).trans (map_rel_iff_subset_liberalPre _ _ _)

/-- One backward while step: establish the postcondition on exit, or preserve the assertion. -/
def whileStep (b : BExp) (c : Cmd) (Q : Assertion) : Set State →o Set State where
  toFun I := {s | (b.eval s = false → Q s) ∧ (b.eval s = true → wlp c (fun t => t ∈ I) s)}
  monotone' := by
    intro I J h s hs
    exact ⟨hs.1, fun hb t hc => h (hs.2 hb hc)⟩

/-- The IMP guarded functional is the generic categorical hidden safety transformer. -/
theorem feedbackStep_loopBody (b : BExp) (c : Cmd) (Q : Assertion) :
    feedbackStep (loopBody b c) {s | Q s} = whileStep b c Q := by
  ext I s
  constructor
  · intro h
    constructor
    · intro hb
      exact (tensorOrderIso_inl states states _ s).mp (h ⟨hb, rfl⟩)
    · intro hb t hc
      exact (tensorOrderIso_inr states states _ t).mp (h ⟨hb, hc⟩)
  · intro h t ht
    cases t with
    | inl t =>
      change b.eval s = false ∧ t = s at ht
      obtain ⟨hb, rfl⟩ := ht
      exact (tensorOrderIso_inl states states _ _).mpr (h.1 hb)
    | inr t =>
      exact (tensorOrderIso_inr states states _ t).mpr (h.2 ht.1 ht.2)

/-- The hidden safe states for a while body coincide with its operational liberal precondition. -/
theorem safeInvariant_loopBody (b : BExp) (c : Cmd) (Q : Assertion) :
    safeInvariant (loopBody b c) {s | Q s} = {s | wlp (.while b c) Q s} := by
  ext s
  constructor
  · intro h t ht
    exact h t ((loopBody_path_iff b c (Sum.inr s) t).mpr ht)
  · intro h t ht
    exact h ((loopBody_path_iff b c (Sum.inr s) t).mp ht)

/-- The while liberal precondition is the greatest fixed point of its guarded functional. -/
theorem wlp_while_eq_gfp (b : BExp) (c : Cmd) (Q : Assertion) :
    {s | wlp (.while b c) Q s} = (whileStep b c Q).gfp := by
  rw [← safeInvariant_loopBody, safeInvariant_eq_gfp, feedbackStep_loopBody]

/-- Post-fixed assertions entail the loop precondition, without a termination premise. -/
theorem while_coinduction (b : BExp) (c : Cmd) (Q : Assertion) (I : Set State)
    (hI : I ⊆ whileStep b c Q I) : I ⊆ {s | wlp (.while b c) Q s} := by
  rw [wlp_while_eq_gfp]
  exact (whileStep b c Q).le_gfp hI

end Cslib.IMP.CategoricalHoare
