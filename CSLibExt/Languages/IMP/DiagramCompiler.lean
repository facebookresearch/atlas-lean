/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import CSLibExt.Languages.IMP.CategoricalHoare
public import CSLibExt.Logics.Hoare.Traced

/-!
# Compiling IMP programs and Hoare derivations into traced diagrams

The compiler uses four primitive blocks: skip, assignment, guard branching and
joining. Sequencing becomes diagram composition, conditionals branch into a
tensor and rejoin, and while loops use feedback. False guards take the left
(exit) wire and true guards take the right (body/feedback) wire.

The compiled relation equals the existing terminating big-step semantics.
Partial-correctness derivations are transported by induction on the source
derivation, using the corresponding diagram proof rules. Semantic axioms are
needed only for the four primitive blocks. Reflection uses source completeness;
neither direction asserts termination or decidability of assertion entailment.

Source: Arthan, Martin, Mathiesen and Oliva, *A General Framework for Sound and
Complete Floyd-Hoare Logics*, Section 4.3 and Figure 10,
https://arxiv.org/abs/0807.1016.
-/

@[expose] public section
namespace Cslib.IMP.DiagramCompiler
open CategoryTheory MonoidalCategory CategoricalHoare
open scoped MonoidalCategory

/-- Primitive control-flow blocks; composite commands cannot occur as atoms. -/
inductive Atom : SumRelCat → SumRelCat → Type
  | skip : Atom states states
  | assign (name : Nat) (value : AExp) : Atom states states
  | branch (guard : BExp) : Atom states (states ⊗ states)
  | join : Atom (states ⊗ states) states

/-- Relational meaning of each primitive block. -/
def interpret : ∀ {X Y}, Atom X Y → (X ⟶ Y)
  | _, _, .skip => commandRel .skip
  | _, _, .assign name value => commandRel (.assign name value)
  | _, _, .branch b => .ofRel {p | match p.2 with
      | .inl t => b.eval p.1 = false ∧ t = p.1
      | .inr t => b.eval p.1 = true ∧ t = p.1}
  | _, _, .join => .ofRel {p | p.2 = controlState p.1}

/-- Structural translation into typed diagrams, with finite-path feedback for loops. -/
def compile : Cmd → TracedHoare.Diagram Atom states states
  | .skip => .atom .skip
  | .assign name value => .atom (.assign name value)
  | .seq c d => .seq (compile c) (compile d)
  | .ite b c d => .seq (.atom (.branch b))
      (.seq (.tensor (compile d) (compile c)) (.atom .join))
  | .while b c => .feedback (.seq (.atom .join)
      (.seq (.atom (.branch b)) (.tensor (.atom .skip) (compile c))))

private theorem branch_tensor_rel (b : BExp) (f g : states ⟶ states)
    (s : State) (t : Sum State State) :
    (s, t) ∈ (interpret (.branch b) ≫ (f ⊗ₘ g)).rel ↔ match t with
      | .inl u => b.eval s = false ∧ (s, u) ∈ f.rel
      | .inr u => b.eval s = true ∧ (s, u) ∈ g.rel := by
  rw [SumRelCat.comp_rel]
  cases t <;> simp [Sum.exists, interpret]

private theorem conditional_rel (b : BExp) (c d : Cmd) :
    interpret (.branch b) ≫ ((commandRel d ⊗ₘ commandRel c) ≫ interpret .join) =
      commandRel (.ite b c d) := by
  rw [← Category.assoc]
  apply SumRelCat.Hom.ext
  ext ⟨s, t⟩
  rw [SumRelCat.comp_rel]
  change (∃ u : Sum State State, _ ∧ t = controlState u) ↔ _
  constructor
  · rintro ⟨u, hu, ht⟩
    have hu' := (branch_tensor_rel b (commandRel d) (commandRel c) s u).mp hu
    cases u with
    | inl u => exact .iteFalse hu'.1 (by simpa [controlState] using ht ▸ hu'.2)
    | inr u => exact .iteTrue hu'.1 (by simpa [controlState] using ht ▸ hu'.2)
  · intro h
    rcases BigStep.ite_iff.mp h with h | h
    · exact ⟨.inr t, (branch_tensor_rel b _ _ s (.inr t)).mpr h, rfl⟩
    · exact ⟨.inl t, (branch_tensor_rel b _ _ s (.inl t)).mpr h, rfl⟩

private theorem loop_rel (b : BExp) (c : Cmd) :
    interpret .join ≫ (interpret (.branch b) ≫ (interpret .skip ⊗ₘ commandRel c)) =
      loopBody b c := by
  apply SumRelCat.Hom.ext
  ext ⟨s, t⟩
  rw [SumRelCat.comp_rel]
  change (∃ u : State, u = controlState s ∧ _) ↔ _
  rw [exists_eq_left, branch_tensor_rel b (interpret .skip) (commandRel c)]
  cases t <;> simp [interpret, loopBody, commandRel, BigStep.skip_iff]

/-- The diagram compiled from `c` denotes exactly the terminating execution relation of `c`,
`commandRel c`. -/
theorem denote_compile (c : Cmd) :
    (compile c).denote interpret SumRelCat.symmetricTrace = commandRel c := by
  induction c with
  | skip => rfl
  | assign name value => rfl
  | seq c d ihC ihD =>
      simpa only [compile, TracedHoare.Diagram.denote, ihC, ihD] using
        (commandRel_seq c d).symm
  | ite b c d ihC ihD =>
      simpa only [compile, TracedHoare.Diagram.denote, ihC, ihD] using conditional_rel b c d
  | «while» b c ih =>
      simp only [compile, TracedHoare.Diagram.denote, ih, loop_rel, ← commandRel_while]

/-- A compiled execution is precisely a source big-step execution. -/
theorem execution_iff (c : Cmd) (s t : State) :
    (s, t) ∈ ((compile c).denote interpret SumRelCat.symmetricTrace).rel ↔
      BigStep c s t := by rw [denote_compile]; rfl

open PowersetVerification Functor.LaxMonoidal Functor.OplaxMonoidal

/-- The assertion on two wires with the indicated assertion on each summand. -/
def sumAssertion (P Q : Assertion) : Set (Sum State State) :=
  tensorOrderIso states states ({s | P s}, {s | Q s})

private theorem comparison_in (P Q : Assertion) :
    (({s | P s}, {s | Q s}), sumAssertion P Q) ∈ (μ verification states states).rel := by
  change tensorOrderIso states states ({s | P s}, {s | Q s}) ⊆ sumAssertion P Q
  exact le_rfl

private theorem comparison_out (P Q : Assertion) :
    (sumAssertion P Q, ({s | P s}, {s | Q s})) ∈ (δ verification states states).rel := by
  change (tensorOrderIso states states).symm (sumAssertion P Q) ≤ _
  simp only [sumAssertion, OrderIso.symm_apply_apply]
  exact le_rfl

private theorem parallel {P Q R S : Assertion}
    {d e : TracedHoare.Diagram Atom states states}
    (hd : TracedHoare.Derivable interpret verification {s | P s} d {s | Q s})
    (he : TracedHoare.Derivable interpret verification {s | R s} e {s | S s}) :
    TracedHoare.Derivable interpret verification (sumAssertion P R)
      (.tensor d e) (sumAssertion Q S) :=
  .tensor (comparison_out P R) hd he (comparison_in Q S)

private theorem branch_rule (P : Assertion) (b : BExp) :
    TracedHoare.Derivable interpret verification {s | P s} (.atom (.branch b))
      (sumAssertion (fun s => P s ∧ b.eval s = false)
        (fun s => P s ∧ b.eval s = true)) := by
  apply TracedHoare.Derivable.atom
  change (interpret (.branch b)).rel.image {s | P s} ⊆ _
  rintro t ⟨s, hs, hst⟩
  cases t with
  | inl t =>
      obtain ⟨hb, rfl⟩ := hst
      exact (tensorOrderIso_inl _ _ _ _).mpr ⟨hs, hb⟩
  | inr t =>
      obtain ⟨hb, rfl⟩ := hst
      exact (tensorOrderIso_inr _ _ _ _).mpr ⟨hs, hb⟩

private theorem join_rule (P : Assertion) :
    TracedHoare.Derivable interpret verification (sumAssertion P P) (.atom .join)
      {s | P s} := by
  apply TracedHoare.Derivable.atom
  change (interpret .join).rel.image (sumAssertion P P) ⊆ _
  rintro t ⟨s, hs, hst⟩
  change t = controlState s at hst
  subst t
  cases s with
  | inl s => exact (tensorOrderIso_inl states states ({t | P t}, {t | P t}) s).mp hs
  | inr s => exact (tensorOrderIso_inr states states ({t | P t}, {t | P t}) s).mp hs

/-- Transport source proofs rule by rule, preserving their intermediate assertions
and loop invariants. This construction does not invoke diagram completeness. -/
theorem transport {P Q : Assertion} {c : Cmd} (h : IMP.Derivable P c Q) :
    TracedHoare.Derivable interpret verification {s | P s} (compile c) {s | Q s} := by
  induction h with
  | skip Q => exact .atom Atom.skip ((triple_iff_valid _ _ _).mpr (Valid.skip Q))
  | assign Q name value =>
      exact .atom (Atom.assign name value)
        ((triple_iff_valid _ _ _).mpr (Valid.assign Q name value))
  | seq _ _ ihFirst ihSecond => exact .seq ihFirst ihSecond
  | @ite P Q b c d _ _ ihThen ihElse =>
      exact .seq (branch_rule P b) (.seq (parallel ihElse ihThen) (join_rule Q))
  | @whileLoop I b c _ ih =>
      refine .feedback {s | I s} (comparison_in I I) ?_
        (comparison_out (fun s => I s ∧ b.eval s = false) I)
      refine .seq (join_rule I) (.seq (branch_rule I b) (parallel ?_ ih))
      exact .atom Atom.skip ((triple_iff_valid _ _ _).mpr (Valid.skip _))
  | consequence hP _ hQ ih => exact .consequence ih hP hQ

/-- A diagram proof of a compiled program reflects to the source calculus. -/
theorem reflect {P Q : Assertion} {c : Cmd}
    (h : TracedHoare.Derivable interpret verification {s | P s} (compile c) {s | Q s}) :
    IMP.Derivable P c Q := by
  have hs := h.sound preserves_trace
  rw [denote_compile] at hs
  exact (CategoricalHoare.derivable_iff_triple c P Q).mpr hs

/-- Source and compiled programs have the same partial-correctness derivable triples. -/
theorem derivable_iff (P Q : Assertion) (c : Cmd) :
    IMP.Derivable P c Q ↔
      TracedHoare.Derivable interpret verification {s | P s} (compile c) {s | Q s} :=
  ⟨transport, reflect⟩

end Cslib.IMP.DiagramCompiler
