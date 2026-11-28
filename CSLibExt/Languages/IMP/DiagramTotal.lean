/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import CSLibExt.Languages.IMP.DiagramVCG
public import CSLibExt.Languages.IMP.TotalPrecondition

/-!
# Total correctness of compiled IMP diagrams

The compiler's existing execution correspondence transports `wp`, `TValid`, and
syntactic total-correctness derivability to finite output witnesses of compiled
IMP diagrams. While preconditions retain their least-fixed-point description.
Successful annotated partial verification conditions can be combined with a
separate source termination proof to give both a diagram Hoare derivation and
a terminating output satisfying its postcondition.

These statements concern diagrams compiled from deterministic IMP. Existence
of a finite output is not offered as a general must-termination semantics for
arbitrary diagrams or nondeterministic programs. The annotation generator
continues to prove partial correctness; it does not infer ranking functions.

The flowchart interpretation follows Arthan, Martin, Mathiesen and Oliva,
*A General Framework for Sound and Complete Floyd-Hoare Logics*, Section 4.3,
https://arxiv.org/abs/0807.1016. Total correctness follows the existing IMP API
and Nipkow and Klein, *Concrete Semantics*, Section 12.5,
https://concrete-semantics.cs.tum.edu/concrete-semantics.pdf.
-/

@[expose] public section
namespace Cslib.IMP.DiagramCompiler
open CategoryTheory

/-- A finite compiled output satisfying the postcondition is exactly source `wp`. -/
theorem compiled_wp_iff (c : Cmd) (Q : Assertion) (s : State) :
    (∃ t, (s, t) ∈ ((compile c).denote interpret SumRelCat.symmetricTrace).rel ∧ Q t) ↔
      wp c Q s := by
  rw [denote_compile]
  rfl

/-- Total correctness is preserved and reflected by compilation of IMP programs. -/
theorem compiled_tvalid_iff (c : Cmd) (P Q : Assertion) :
    (∀ s, P s → ∃ t,
      (s, t) ∈ ((compile c).denote interpret SumRelCat.symmetricTrace).rel ∧ Q t) ↔
      TValid P c Q := by
  rw [denote_compile]
  rfl

/-- Compiled output witnesses characterize the existing total-correctness proof system. -/
theorem compiled_tderivable_iff (c : Cmd) (P Q : Assertion) :
    (∀ s, P s → ∃ t,
      (s, t) ∈ ((compile c).denote interpret SumRelCat.symmetricTrace).rel ∧ Q t) ↔
      TDerivable P c Q :=
  (compiled_tvalid_iff c P Q).trans tderivable_iff_tvalid.symm

/-- Compiled while outputs retain the source predicate least-fixed-point characterization. -/
theorem compiled_while_iff_lfp (b : BExp) (c : Cmd) (Q : Assertion) (s : State) :
    (∃ t, (s, t) ∈ ((compile (.while b c)).denote interpret
      SumRelCat.symmetricTrace).rel ∧ Q t) ↔ s ∈ (wp.whileStep b c Q).lfp := by
  rw [compiled_wp_iff, ← wp.while_eq_lfp]
  rfl

/-- Combine partial verification conditions with a separate termination proof.
The supplied annotation is preserved; termination is an explicit additional premise. -/
theorem annotated_total (c : ACmd) (P Q : Assertion)
    (hP : P.Entails (c.pre Q)) (hvc : c.vc Q)
    (hterm : ∀ s, P s → ∃ t, BigStep c.strip s t) :
    TracedHoare.Derivable interpret PowersetVerification.verification
      {s | P s} (compile c.strip) {s | Q s} ∧
    (∀ s, P s → ∃ t, (s, t) ∈ ((compile c.strip).denote interpret
      SumRelCat.symmetricTrace).rel ∧ Q t) := by
  refine ⟨annotated_derivable c P Q hP hvc, ?_⟩
  intro s hs
  obtain ⟨t, ht⟩ := hterm s hs
  exact ⟨t, (execution_iff _ _ _).mpr ht, (c.vc_sound Q hvc).sound (hP hs) ht⟩

end Cslib.IMP.DiagramCompiler
