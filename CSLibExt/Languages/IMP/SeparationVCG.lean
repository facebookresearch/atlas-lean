/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.IMP.SeparationRules

/-!
# Verification-condition generation for heap separation logic

`AHeapCmd` annotates heap IMP loops with invariants and supports explicit
frame annotations carrying a frame assertion and a local postcondition.
`strip` erases these annotations. `pre` computes a sufficient backward
precondition; `vc` computes the remaining assertion obligations.

Atomic preconditions use explicit heap lookups, membership, updates and
universal fresh-address quantification. Loop conditions require body
preservation and the desired result at exit. A frame requires its body's
conditions, stability under modifications of the body's store variables,
and entailment from the framed local result to the desired postcondition.
Both conditional branches contribute verification conditions.

`vc_sound` and `vc_valid` establish fault-avoiding partial correctness.
The generator does not infer invariants or frames, decide the generated
propositions, prove termination, or claim completeness.

The invariant-based design extends the existing IMP VCG in
`CSLibExt.Languages.IMP.VCG`; see Nipkow and Klein, *Concrete Semantics*,
Section 12.4 and the accompanying VCG theory:
<https://isabelle.in.tum.de/library/HOL/HOL-IMP/VCG.html>.
The heap assertions and frame rule follow Reynolds, *Separation Logic:
A Logic for Shared Mutable Data Structures*, LICS 2002, Sections 3–4:
<https://www.cs.cmu.edu/~jcr/seplogic.pdf>.
-/

@[expose] public section

namespace Cslib.IMP

/-- Heap commands with supplied loop invariants and explicit frame cuts.
A frame cut records the frame and the body's local postcondition. -/
inductive AHeapCmd where
  | skip
  | assign (name : Nat) (value : AExp)
  | seq (first second : AHeapCmd)
  | ite (guard : BExp) (thenBranch elseBranch : AHeapCmd)
  | while (invariant : HAssertion) (guard : BExp) (body : AHeapCmd)
  | read (name : Nat) (addr : AExp)
  | write (addr value : AExp)
  | alloc (name : Nat) (value : AExp)
  | free (addr : AExp)
  | frame (assertion localPost : HAssertion) (body : AHeapCmd)

namespace AHeapCmd

open HAssertion
open scoped HAssertion

/-- Erase loop invariants and frame annotations, retaining the program. -/
def strip : AHeapCmd → HeapCmd
  | .skip => .skip
  | .assign name value => .assign name value
  | .seq first second => .seq first.strip second.strip
  | .ite guard t e => .ite guard t.strip e.strip
  | .while _ guard body => .while guard body.strip
  | .read name addr => .read name addr
  | .write addr value => .write addr value
  | .alloc name value => .alloc name value
  | .free addr => .free addr
  | .frame _ _ body => body.strip

/-- Compute the backward assertion `C.pre Q` for an annotated command
`C` and heap postcondition `Q`. If `C.vc Q` holds, `C.pre Q` is sufficient
for safe partial correctness. Atomic commands use the
lookup, ownership, update and universal fresh-allocation conditions; sequences
nest these assertions and conditionals select by the guard. Loops return the
supplied invariant. A frame returns `body.pre localPost ⋆ R`; its obligations
connect that local postcondition to the requested result. -/
def pre : AHeapCmd → HAssertion → HAssertion
  | .skip, post => post
  | .assign name value, post => fun s h =>
      post (Function.update s name (value.eval s)) h
  | .seq first second, post => first.pre (second.pre post)
  | .ite guard t e, post => fun s h =>
      if guard.eval s = true then t.pre post s h else e.pre post s h
  | .while invariant _ _, _ => invariant
  | .read name addr, post => fun s h =>
      ∃ v, h.lookup (addr.eval s) = some v ∧
        post (Function.update s name v) h
  | .write addr value, post => fun s h =>
      addr.eval s ∈ h ∧ post s (Finmap.insert (addr.eval s) (value.eval s) h)
  | .alloc name value, post => fun s h =>
      ∀ a, a ∉ h → post (Function.update s name a)
        (Finmap.insert a (value.eval s) h)
  | .free addr, post => fun s h =>
      addr.eval s ∈ h ∧ post s (Finmap.erase (addr.eval s) h)
  | .frame R localPost body, _ => body.pre localPost ⋆ R

/-- Generate the assertion obligations `C.vc Q` for an annotated command
`C` and heap postcondition `Q`. Atomic commands impose no further obligations:
their memory-safety requirements are in `pre`. A sequence checks the first
command against the second command's precondition and checks the second
against `Q`; a conditional checks both branches against `Q`.

A loop requires its invariant and true guard to entail the body precondition
for that invariant, its invariant and false guard to entail `Q`, and the
body's own verification conditions. A frame requires `body.vc localPost`,
stability of `R` under store updates agreeing outside `body.strip.modVars`,
and `(localPost ⋆ R).Entails Q`. -/
def vc : AHeapCmd → HAssertion → Prop
  | .seq first second, post => first.vc (second.pre post) ∧ second.vc post
  | .ite _ t e, post => t.vc post ∧ e.vc post
  | .while invariant guard body, post =>
      HAssertion.Entails (fun s h => invariant s h ∧ guard.eval s = true)
        (body.pre invariant) ∧
      HAssertion.Entails (fun s h => invariant s h ∧ guard.eval s = false)
        post ∧
      body.vc invariant
  | .frame R localPost body, post => body.vc localPost ∧
      (∀ ⦃s h s'⦄, R s h →
        (∀ x, x ∉ body.strip.modVars → s' x = s x) → R s' h) ∧
      (localPost ⋆ R).Entails post
  | _, _ => True

/-- Weakening the desired postcondition weakens the generated precondition.
This does not discharge the separate verification conditions. -/
theorem pre_mono : ∀ (C : AHeapCmd) {Q Q' : HAssertion}, Q.Entails Q' →
    (C.pre Q).Entails (C.pre Q')
  | .skip, _, _, h => h
  | .assign _ _, _, _, h => fun {_ _} hp => h hp
  | .seq c₁ c₂, _, _, h => pre_mono c₁ (pre_mono c₂ h)
  | .ite guard t e, _, _, h => by
      intro s k hp
      by_cases hg : guard.eval s = true
      · simp only [pre, hg, ↓reduceIte] at hp ⊢
        exact pre_mono t h hp
      · simp only [pre, hg] at hp ⊢
        exact pre_mono e h hp
  | .while _ _ _, _, _, _ => entails_refl _
  | .read _ _, _, _, h => by
      rintro s k ⟨v, hv, hp⟩
      exact ⟨v, hv, h hp⟩
  | .write _ _, _, _, h => fun {_ _} hp => ⟨hp.1, h hp.2⟩
  | .alloc _ _, _, _, h => fun {_ _} hp a ha => h (hp a ha)
  | .free _, _, _, h => fun {_ _} hp => ⟨hp.1, h hp.2⟩
  | .frame _ _ _, _, _, _ => entails_refl _

/-- Generated conditions establish safety and the postcondition at every
terminating output of the erased program, from the generated precondition. -/
theorem vc_sound : ∀ (C : AHeapCmd) (Q : HAssertion), C.vc Q →
    SepValid (C.pre Q) C.strip Q
  | .skip, Q, _ => SepValid.skip Q
  | .assign _ _, _, _ => safePre.valid_iff.mpr
      (fun {_ _} hp => safePre.assign_iff.mpr hp)
  | .seq c₁ c₂, Q, ⟨h₁, h₂⟩ =>
      SepValid.seq (vc_sound c₁ _ h₁) (vc_sound c₂ Q h₂)
  | .ite guard t e, Q, ⟨ht, he⟩ => by
      apply SepValid.ite
      · apply SepValid.consequence _ (vc_sound t Q ht) (entails_refl _)
        intro s h hp
        simpa [pre, hp.2] using hp.1
      · apply SepValid.consequence _ (vc_sound e Q he) (entails_refl _)
        intro s h hp
        simpa [pre, hp.2] using hp.1
  | .while I guard body, _, ⟨hbody, hexit, hvc⟩ =>
      SepValid.consequence (entails_refl _)
        (SepValid.whileLoop (SepValid.consequence hbody
          (vc_sound body I hvc) (entails_refl _))) hexit
  | .read _ _, _, _ => safePre.valid_iff.mpr
      (fun {_ _} hp => safePre.read_iff.mpr hp)
  | .write _ _, _, _ => safePre.valid_iff.mpr
      (fun {_ _} hp => safePre.write_iff.mpr hp)
  | .alloc _ _, _, _ => safePre.valid_iff.mpr
      (fun {_ _} hp => safePre.alloc_iff.mpr hp)
  | .free _, _, _ => safePre.valid_iff.mpr
      (fun {_ _} hp => safePre.free_iff.mpr hp)
  | .frame _ localPost body, _, ⟨hvc, hR, hpost⟩ =>
      SepValid.consequence (entails_refl _)
        (SepValid.frame (vc_sound body localPost hvc) hR) hpost

/-- For an annotated command `C` and heap assertions `P`, `Q`, if
`C.vc Q` holds and `P.Entails (C.pre Q)`, then `SepValid P C.strip Q`.
Thus the erased program avoids faults from `P` and satisfies `Q` at every
terminating output; termination itself is not asserted. -/
theorem vc_valid {C : AHeapCmd} {P Q : HAssertion} (hvc : C.vc Q)
    (hpre : P.Entails (C.pre Q)) : SepValid P C.strip Q :=
  SepValid.consequence hpre (vc_sound C Q hvc) (entails_refl _)

end AHeapCmd

end Cslib.IMP
