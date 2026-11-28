/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.IMP.SeparationLogic

/-!
# Separating implication and safe backward preconditions

`HAssertion.wand R Q` describes the heaps which, when extended by any
disjoint heap satisfying `R` at the same store, satisfy `Q`. Separating
conjunction and this implication satisfy `star_entails_iff_entails_wand`.

`safePre c Q` is the weakest precondition for the existing fault-avoiding
partial correctness semantics `SepValid`: it requires safety and `Q` at
every terminating output, including every allocation choice. It does
not require termination. Its frame inequality retains the frame rule's
condition on modified store variables; the adjunction gives the
corresponding wand formulation.

These are the assertion and specification semantics of J. C. Reynolds,
*Separation Logic: A Logic for Shared Mutable Data Structures*, LICS 2002,
Sections 3–4: <https://www.cs.cmu.edu/~jcr/seplogic.pdf>.
-/

@[expose] public section

namespace Cslib.IMP

namespace HAssertion

/-- Separating implication: every disjoint extension satisfying `R`
at the same store makes the combined heap satisfy `Q`. -/
def wand (R Q : HAssertion) : HAssertion :=
  fun s h => ∀ hf, Heap.Disjoint h hf → R s hf → Q s (h ∪ hf)

/-- Separating conjunction is left adjoint to separating implication. -/
theorem star_entails_iff_entails_wand {P R Q : HAssertion} :
    (P ⋆ R).Entails Q ↔ P.Entails (wand R Q) := by
  constructor
  · intro hPQ s h hP hf hd hR
    exact hPQ ⟨h, hf, hd, rfl, hP, hR⟩
  · intro hPQ s h hstar
    obtain ⟨h₁, hf, hd, rfl, hP, hR⟩ := hstar
    exact hPQ hP hf hd hR

/-- A wand can be applied to a separately owned argument. -/
theorem star_wand_elim {R Q : HAssertion} :
    (wand R Q ⋆ R).Entails Q :=
  star_entails_iff_entails_wand.mpr (entails_refl _)

/-- Extending by the empty heap leaves an assertion unchanged. -/
theorem wand_emp {Q : HAssertion} : wand emp Q = Q := by
  funext s h
  apply propext
  constructor
  · intro hw
    simpa using hw ∅ (Heap.disjoint_empty_right h) rfl
  · intro hQ hf _hd hemp
    have heq : hf = ∅ := hemp
    simpa [heq] using hQ

/-- Wand is contravariant in its argument and covariant in its result. -/
theorem wand_mono {R R' Q Q' : HAssertion}
    (hR : R'.Entails R) (hQ : Q.Entails Q') :
    (wand R Q).Entails (wand R' Q') := by
  intro s h hw hf hd hR'
  exact hQ (hw hf hd (hR hR'))

end HAssertion

open HAssertion
open scoped HAssertion

/-- The weakest precondition for safe partial correctness: no reachable
fault and the postcondition at every terminating output. Safe divergent
executions are allowed. -/
def safePre (c : HeapCmd) (Q : HAssertion) : HAssertion :=
  fun s h => Safe (c, s, h) ∧
    ∀ ⦃s' h'⦄, HSteps (c, s, h) (.skip, s', h') → Q s' h'

namespace safePre

/-- Validity is exactly entailment of the safe backward precondition. -/
theorem valid_iff {P Q : HAssertion} {c : HeapCmd} :
    SepValid P c Q ↔ P.Entails (safePre c Q) := Iff.rfl

/-- The safe backward precondition itself establishes validity. -/
theorem valid (c : HeapCmd) (Q : HAssertion) :
    SepValid (safePre c Q) c Q := fun {_s _h} hp => hp

/-- Weakening a postcondition weakens its safe precondition. -/
theorem mono {P Q : HAssertion} (c : HeapCmd) (hPQ : P.Entails Q) :
    (safePre c P).Entails (safePre c Q) := by
  intro s h hp
  exact ⟨hp.1, fun {_t _k} hs => hPQ (hp.2 hs)⟩

/-- Safe preconditions preserve conjunction on the same heap. -/
theorem hand (c : HeapCmd) (P Q : HAssertion) :
    safePre c (HAssertion.hand P Q) =
      HAssertion.hand (safePre c P) (safePre c Q) := by
  funext s h
  apply propext
  constructor
  · intro hp
    exact ⟨⟨hp.1, fun {_t _k} hs => (hp.2 hs).1⟩,
      ⟨hp.1, fun {_t _k} hs => (hp.2 hs).2⟩⟩
  · intro hp
    exact ⟨hp.1.1, fun {_t _k} hs => ⟨hp.1.2 hs, hp.2.2 hs⟩⟩

/-- Skip has precisely its postcondition as safe precondition. -/
theorem skip (Q : HAssertion) : safePre .skip Q = Q := by
  funext s h
  exact propext ⟨fun hp => hp.2 .refl, fun hQ => SepValid.skip Q hQ⟩

/-- The constantly true postcondition still requires safety. -/
theorem true_iff {c : HeapCmd} {s : State} {h : Heap} :
    safePre c (fun _ _ => True) s h ↔ Safe (c, s, h) :=
  ⟨And.left, fun hs => ⟨hs, fun {_t _k} _ => trivial⟩⟩

/-- If `R` does not depend on the variables that `c` modifies (`c.modVars`), then
`safePre c Q ⋆ R` entails `safePre c (Q ⋆ R)`. -/
theorem frame {c : HeapCmd} {Q R : HAssertion}
    (hR : ∀ ⦃s h s'⦄, R s h →
      (∀ x, x ∉ c.modVars → s' x = s x) → R s' h) :
    (safePre c Q ⋆ R).Entails (safePre c (Q ⋆ R)) :=
  valid_iff.mp (SepValid.frame (valid c Q) hR)

/-- If `R` does not depend on the variables that `c` modifies (`c.modVars`), then
`safePre c Q` entails `wand R (safePre c (Q ⋆ R))`. -/
theorem frame_wand {c : HeapCmd} {Q R : HAssertion}
    (hR : ∀ ⦃s h s'⦄, R s h →
      (∀ x, x ∉ c.modVars → s' x = s x) → R s' h) :
    (safePre c Q).Entails (wand R (safePre c (Q ⋆ R))) :=
  star_entails_iff_entails_wand.mp (frame hR)

end safePre

end Cslib.IMP
