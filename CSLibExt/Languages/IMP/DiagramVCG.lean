/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import CSLibExt.Languages.IMP.DiagramCompiler
public import CSLibExt.Languages.IMP.VCG
public import CSLibExt.Logics.Hoare.TracedVCG

/-!
# Compiling IMP verification conditions into diagram annotations

`annotate` structurally translates the existing invariant-annotated IMP syntax.
Its diagram index is exactly the existing compiler applied to the erased command.
It retains each supplied loop invariant and computes wire assertions using the
existing backward precondition function. No completeness oracle or search for
annotations is used in the translation.

The generated diagram obligations are equivalent to the existing IMP verification
conditions together with entailment of the computed precondition. Thus successful
source certificates and their failed obligations are faithfully transported.
The annotations and assertions remain semantic; this is partial correctness,
not automatic invariant synthesis or a termination checker.

Sources: Nipkow and Klein, *Concrete Semantics*, Section 12.4; Arthan, Martin,
Mathiesen and Oliva, *A General Framework for Sound and Complete Floyd-Hoare Logics*,
Section 4.3 and Figure 10, https://arxiv.org/abs/0807.1016.
-/

@[expose] public section
namespace Cslib.IMP.DiagramCompiler
open CategoryTheory CategoricalHoare PowersetVerification
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped MonoidalCategory

/-- Compile invariant annotations structurally, using the source generator's preconditions. -/
def annotate : (c : ACmd) → (Q : Assertion) → TracedHoare.Annotation verification (compile c.strip)
  | .skip, _ => .atom Atom.skip
  | .assign name value, _ => .atom (Atom.assign name value)
  | .seq c d, Q => .seq {s | d.pre Q s} (annotate c (d.pre Q)) (annotate d Q)
  | .ite b c d, Q =>
      .seq (sumAssertion (d.pre Q) (c.pre Q)) (.atom (Atom.branch b))
        (.seq (sumAssertion Q Q)
          (.tensor {s | d.pre Q s} {s | c.pre Q s} {s | Q s} {s | Q s}
            (annotate d Q) (annotate c Q)) (.atom Atom.join))
  | .while I b c, Q =>
      .feedback {s | I s} (sumAssertion I I) (sumAssertion Q I)
        (.seq {s | I s} (.atom Atom.join)
          (.seq (sumAssertion Q (c.pre I)) (.atom (Atom.branch b))
            (.tensor {s | Q s} {s | c.pre I s} {s | Q s} {s | I s}
              (.atom Atom.skip) (annotate c I))))

private theorem mu_sum (P Q R S : Assertion) :
    (({s | P s}, {s | Q s}), sumAssertion R S) ∈ (μ verification states states).rel ↔
      P.Entails R ∧ Q.Entails S := by
  change tensorOrderIso states states ({s | P s}, {s | Q s}) ≤
    tensorOrderIso states states ({s | R s}, {s | S s}) ↔ _
  exact (tensorOrderIso states states).le_iff_le

private theorem delta_sum (P Q R S : Assertion) :
    (sumAssertion P Q, ({s | R s}, {s | S s})) ∈ (δ verification states states).rel ↔
      P.Entails R ∧ Q.Entails S := by
  change (tensorOrderIso states states).symm (sumAssertion P Q) ≤ _ ↔ _
  rw [sumAssertion, OrderIso.symm_apply_apply]
  rfl

private theorem skip_vc (P Q : Assertion) :
    (TracedHoare.Annotation.atom (F := verification) Atom.skip).vc interpret
      {s | P s} {s | Q s} ↔ P.Entails Q := by
  change VerificationFunctor.Triple verification (commandRel .skip) _ _ ↔ _
  rw [commandRel_skip, VerificationFunctor.triple_id_iff]
  rfl

private theorem assign_vc (P Q : Assertion) (x : Nat) (a : AExp) :
    (TracedHoare.Annotation.atom (F := verification) (Atom.assign x a)).vc interpret
      {s | P s} {s | Q s} ↔ P.Entails (Q.subst x a) := by
  change VerificationFunctor.Triple verification (commandRel (.assign x a)) _ _ ↔ _
  rw [triple_iff_valid]
  constructor
  · intro h s hs
    exact h hs (.assign s x a)
  · intro h s t hs ht
    obtain rfl := BigStep.assign_iff.mp ht
    exact h hs

private theorem join_vc (P Q : Assertion) :
    (TracedHoare.Annotation.atom (F := verification) Atom.join).vc interpret
      (sumAssertion P P) {s | Q s} ↔ P.Entails Q := by
  change (interpret Atom.join).rel.image (sumAssertion P P) ⊆ {s | Q s} ↔ _
  constructor
  · intro h s hs
    exact h ⟨.inl s, (tensorOrderIso_inl states states _ s).mpr hs, rfl⟩
  · rintro h t ⟨s, hs, hst⟩
    change t = controlState s at hst
    subst t
    cases s with
    | inl s => exact h ((tensorOrderIso_inl states states _ s).mp hs)
    | inr s => exact h ((tensorOrderIso_inr states states _ s).mp hs)

private theorem branch_vc (b : BExp) (P R S : Assertion) :
    (TracedHoare.Annotation.atom (F := verification) (Atom.branch b)).vc interpret
      {s | P s} (sumAssertion R S) ↔
      P.Entails (fun s => if b.eval s = true then S s else R s) := by
  change (interpret (Atom.branch b)).rel.image {s | P s} ⊆ sumAssertion R S ↔ _
  constructor
  · intro h s hs
    cases hb : b.eval s with
    | false =>
        have ht := h ⟨s, hs, (show (s, Sum.inl s) ∈ (interpret (Atom.branch b)).rel from ⟨hb, rfl⟩)⟩
        simpa [hb] using (tensorOrderIso_inl states states _ s).mp ht
    | true =>
        have ht := h ⟨s, hs, (show (s, Sum.inr s) ∈ (interpret (Atom.branch b)).rel from ⟨hb, rfl⟩)⟩
        simpa [hb] using (tensorOrderIso_inr states states _ s).mp ht
  · rintro h t ⟨s, hs, hst⟩
    cases t with
    | inl t =>
        obtain ⟨hb, rfl⟩ := hst
        exact (tensorOrderIso_inl states states _ _).mpr (by simpa [hb] using h hs)
    | inr t =>
        obtain ⟨hb, rfl⟩ := hst
        exact (tensorOrderIso_inr states states _ _).mpr (by simpa [hb] using h hs)

/-- Diagram obligations coincide with source precondition entailment and verification conditions. -/
theorem vc_annotate_iff (c : ACmd) (P Q : Assertion) :
    (annotate c Q).vc interpret {s | P s} {s | Q s} ↔ P.Entails (c.pre Q) ∧ c.vc Q := by
  induction c generalizing P Q with
  | skip =>
      simpa only [ACmd.strip, compile, annotate, ACmd.pre, ACmd.vc, and_true] using skip_vc P Q
  | assign x a =>
      simpa only [ACmd.strip, compile, annotate, ACmd.pre, ACmd.vc, and_true] using
        assign_vc P Q x a
  | seq c d ihC ihD =>
      simp only [ACmd.strip, compile, annotate, TracedHoare.Annotation.vc.eq_2,
        ihC, ihD, ACmd.pre, ACmd.vc]
      simp [Assertion.entails_refl, and_assoc]
  | ite b c d ihC ihD =>
      simp only [ACmd.strip, compile, annotate, TracedHoare.Annotation.vc.eq_2,
        TracedHoare.Annotation.vc.eq_3, ihC, ihD,
        ACmd.pre, ACmd.vc]
      rw [branch_vc b P (d.pre Q) (c.pre Q),
        delta_sum (d.pre Q) (c.pre Q) (d.pre Q) (c.pre Q), mu_sum Q Q Q Q, join_vc Q Q]
      simp only [Assertion.entails_refl, true_and, and_true]
      exact ⟨fun h => ⟨h.1, h.2.2, h.2.1⟩, fun h => ⟨h.1, h.2.2, h.2.1⟩⟩
  | «while» I b c ih =>
      simp only [ACmd.strip, compile, annotate, TracedHoare.Annotation.vc.eq_2,
        TracedHoare.Annotation.vc.eq_3,
        TracedHoare.Annotation.vc.eq_4, ih, ACmd.pre, ACmd.vc]
      rw [mu_sum P I I I, join_vc I I, branch_vc b I Q (c.pre I),
        delta_sum Q (c.pre I) Q (c.pre I), skip_vc Q Q, mu_sum Q I Q I, delta_sum Q I Q I]
      simp only [Assertion.entails_refl, true_and, and_true]
      constructor
      · rintro ⟨hP, hb, hc⟩
        refine ⟨hP, ?_, ?_, hc⟩
        · intro s hI ht
          simpa [ht] using hb hI
        · intro s hI hf
          simpa [hf] using hb hI
      · rintro ⟨hP, hbody, hexit, hc⟩
        refine ⟨hP, ?_, hc⟩
        intro s hI
        cases hb : b.eval s with
        | false => simpa [hb] using hexit s hI hb
        | true => simpa [hb] using hbody s hI hb

/-- Source obligations construct a derivation of the structurally compiled diagram. -/
theorem annotated_derivable (c : ACmd) (P Q : Assertion)
    (hP : P.Entails (c.pre Q)) (hvc : c.vc Q) :
    TracedHoare.Derivable interpret verification {s | P s} (compile c.strip) {s | Q s} :=
  (annotate c Q).vc_sound ((vc_annotate_iff c P Q).mpr ⟨hP, hvc⟩)

/-- Every derivable source triple has a successful structurally compiled IMP annotation. -/
theorem exists_compiled_annotation {P Q : Assertion} {c : Cmd} (h : IMP.Derivable P c Q) :
    ∃ a : ACmd, a.strip = c ∧ (annotate a Q).vc interpret {s | P s} {s | Q s} := by
  obtain ⟨a, ha, hvc, hP⟩ := ACmd.vc_complete h
  exact ⟨a, ha, (vc_annotate_iff a P Q).mpr ⟨hP, hvc⟩⟩

end Cslib.IMP.DiagramCompiler
