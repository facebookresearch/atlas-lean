/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `290c48922e071d1e4267dd103a14e73b547adf60`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Computability.Languages.Congruences.Universal
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.GroupTheory.Congruence.Basic

/-!
# Syntactic congruences and syntactic monoids

The Nerode relation compares words by their possible right continuations.  The syntactic
congruence strengthens this test by allowing arbitrary left and right contexts.  It is therefore
a monoid congruence on the free monoid of words.  Its quotient is the syntactic monoid of the
language.

This file develops the context relation, its quotient monoid, the canonical recognizing morphism,
and its connection with deterministic automata.  In particular, the syntactic class of a word is
determined by its action on the states of the residual-language DFA.
-/

@[expose] public section

open scoped Computability

namespace Cslib.Language

universe u v

variable {Symbol : Type u} {State : Type v}

/-- Two words are syntactically equivalent for `L` when no two-sided context distinguishes
them. -/
def syntacticRel (L : Language Symbol) (x y : FreeMonoid Symbol) : Prop :=
  ∀ u v, FreeMonoid.toList (u * x * v) ∈ L ↔ FreeMonoid.toList (u * y * v) ∈ L

@[refl]
theorem syntacticRel_refl (L : Language Symbol) (x : FreeMonoid Symbol) : syntacticRel L x x :=
  fun _ _ ↦ Iff.rfl

@[symm]
theorem syntacticRel_symm (L : Language Symbol) {x y : FreeMonoid Symbol} :
    syntacticRel L x y → syntacticRel L y x :=
  fun h u v ↦ (h u v).symm

@[trans]
theorem syntacticRel_trans (L : Language Symbol) {x y z : FreeMonoid Symbol} :
    syntacticRel L x y → syntacticRel L y z → syntacticRel L x z :=
  fun hxy hyz u v ↦ (hxy u v).trans (hyz u v)

/-- Syntactic equivalence is stable under adding a common left context. -/
theorem syntacticRel_prefix (L : Language Symbol) {x y : FreeMonoid Symbol}
    (h : syntacticRel L x y) (w : FreeMonoid Symbol) : syntacticRel L (w * x) (w * y) := by
  intro u v
  simpa only [mul_assoc] using h (u * w) v

/-- Syntactic equivalence is stable under adding a common right context. -/
theorem syntacticRel_suffix (L : Language Symbol) {x y : FreeMonoid Symbol}
    (h : syntacticRel L x y) (w : FreeMonoid Symbol) : syntacticRel L (x * w) (y * w) := by
  intro u v
  simpa only [mul_assoc] using h u (w * v)

/-- Syntactic equivalence is compatible with concatenation. -/
theorem syntacticRel_append (L : Language Symbol) {w x y z : FreeMonoid Symbol}
    (h₁ : syntacticRel L w x) (h₂ : syntacticRel L y z) :
    syntacticRel L (w * y) (x * z) :=
  syntacticRel_trans L (syntacticRel_suffix L h₁ y) (syntacticRel_prefix L h₂ x)

/-- The syntactic relation as a monoid congruence on words. -/
def syntacticCon (L : Language Symbol) : Con (FreeMonoid Symbol) where
  r := syntacticRel L
  iseqv := ⟨syntacticRel_refl L, syntacticRel_symm L, syntacticRel_trans L⟩
  mul' := syntacticRel_append L

@[simp]
theorem syntacticCon_apply (L : Language Symbol) (x y : FreeMonoid Symbol) :
    syntacticCon L x y ↔ syntacticRel L x y :=
  Iff.rfl

/-- The syntactic monoid of `L` is the free monoid of words modulo indistinguishability in every
two-sided context. -/
abbrev SyntacticMonoid (L : Language Symbol) := (syntacticCon L).Quotient

/-- The canonical morphism from words to their syntactic classes. -/
def syntacticMorphism (L : Language Symbol) : FreeMonoid Symbol →* SyntacticMonoid L :=
  Con.mk' (syntacticCon L)

@[simp]
theorem syntacticMorphism_apply (L : Language Symbol) (x : FreeMonoid Symbol) :
    syntacticMorphism L x = (x : SyntacticMonoid L) :=
  rfl

theorem syntacticMorphism_surjective (L : Language Symbol) :
    Function.Surjective (syntacticMorphism L) :=
  Con.mk'_surjective

theorem syntacticMorphism_eq_iff (L : Language Symbol) (x y : FreeMonoid Symbol) :
    syntacticMorphism L x = syntacticMorphism L y ↔ syntacticRel L x y := by
  exact Quotient.eq''

/-- Membership in `L` depends only on the syntactic class of a word. -/
theorem syntacticRel_mem_iff (L : Language Symbol) {x y : FreeMonoid Symbol}
    (h : syntacticRel L x y) : FreeMonoid.toList x ∈ L ↔ FreeMonoid.toList y ∈ L := by
  simpa using h 1 1

/-- The accepting subset of the syntactic monoid. -/
def syntacticAccept (L : Language Symbol) : Set (SyntacticMonoid L) :=
  {q | Con.liftOn q (fun x ↦ FreeMonoid.toList x ∈ L)
    (fun _ _ h ↦ propext (syntacticRel_mem_iff L h))}

@[simp]
theorem syntacticMorphism_mem_accept (L : Language Symbol) (x : FreeMonoid Symbol) :
    syntacticMorphism L x ∈ syntacticAccept L ↔ FreeMonoid.toList x ∈ L :=
  Iff.rfl

/-- A language is recognized by its canonical syntactic morphism. -/
theorem mem_iff_syntacticMorphism_mem (L : Language Symbol) (x : FreeMonoid Symbol) :
    FreeMonoid.toList x ∈ L ↔ syntacticMorphism L x ∈ syntacticAccept L :=
  (syntacticMorphism_mem_accept L x).symm

/-- Syntactic equivalence refines Nerode equivalence. -/
theorem syntacticRel_nerodeRel (L : Language Symbol) {x y : FreeMonoid Symbol}
    (h : syntacticRel L x y) : nerodeRel L (FreeMonoid.toList x) (FreeMonoid.toList y) := by
  rw [nerodeRel_iff]
  intro z
  simpa using h 1 (FreeMonoid.ofList z)

/-- Equality of syntactic classes implies equality of Nerode classes. -/
theorem nerodeClass_eq_of_syntacticMorphism_eq (L : Language Symbol) {x y : FreeMonoid Symbol}
    (h : syntacticMorphism L x = syntacticMorphism L y) :
    nerodeClass L (FreeMonoid.toList x) = nerodeClass L (FreeMonoid.toList y) := by
  rw [nerodeClass_eq_iff]
  exact syntacticRel_nerodeRel L ((syntacticMorphism_eq_iff L x y).mp h)

/-- The action of a word on a DFA state. -/
def transitionAction (M : DFA Symbol State) (x : FreeMonoid Symbol) : State → State :=
  fun q ↦ M.evalFrom q (FreeMonoid.toList x)

@[simp]
theorem transitionAction_nil (M : DFA Symbol State) : transitionAction M 1 = id := by
  ext q
  rfl

theorem transitionAction_append (M : DFA Symbol State) (x y : FreeMonoid Symbol) :
    transitionAction M (x * y) = transitionAction M y ∘ transitionAction M x := by
  ext q
  exact DFA.evalFrom_of_append M q (FreeMonoid.toList x) (FreeMonoid.toList y)

/-- Two words with the same action on every state of a recognizing DFA are syntactically
equivalent for its accepted language. -/
theorem syntacticRel_of_transitionAction_eq (M : DFA Symbol State) {x y : FreeMonoid Symbol}
    (h : transitionAction M x = transitionAction M y) : syntacticRel M.accepts x y := by
  intro u v
  simp only [FreeMonoid.toList_mul, DFA.mem_accepts, DFA.eval, List.append_assoc,
    DFA.evalFrom_of_append]
  have hxy : M.evalFrom (M.evalFrom M.start (FreeMonoid.toList u)) (FreeMonoid.toList x) =
      M.evalFrom (M.evalFrom M.start (FreeMonoid.toList u)) (FreeMonoid.toList y) := by
    exact congrFun h (M.evalFrom M.start (FreeMonoid.toList u))
  rw [hxy]

/-- On an accessible DFA, syntactic equivalence of words forces them to act identically whenever
the DFA is state-separated. -/
theorem transitionAction_eq_of_syntacticRel (M : DFA Symbol State) (hacc : Accessible M)
    (hsep : StateSeparated M) {x y : FreeMonoid Symbol} (h : syntacticRel M.accepts x y) :
    transitionAction M x = transitionAction M y := by
  funext q
  apply hsep
  obtain ⟨u, rfl⟩ := hacc q
  rw [stateEquivalent_iff]
  intro v
  simpa only [transitionAction, FreeMonoid.toList_mul, FreeMonoid.toList_ofList, DFA.eval,
    DFA.mem_accepts, DFA.evalFrom_of_append, List.append_assoc] using
    h (FreeMonoid.ofList u) (FreeMonoid.ofList v)

/-- For an accessible, state-separated DFA, syntactic classes are exactly transition actions. -/
theorem syntacticRel_iff_transitionAction_eq (M : DFA Symbol State) (hacc : Accessible M)
    (hsep : StateSeparated M) (x y : FreeMonoid Symbol) :
    syntacticRel M.accepts x y ↔ transitionAction M x = transitionAction M y :=
  ⟨transitionAction_eq_of_syntacticRel M hacc hsep,
    syntacticRel_of_transitionAction_eq M⟩

/-! ## Transition monoids -/

/-- State endomorphisms with opposite multiplication, so `f * g` first applies `f`, then `g`. -/
abbrev StateTransformation (State : Type v) := (Function.End State)ᵐᵒᵖ

instance : CoeFun (StateTransformation State) (fun _ ↦ State → State) :=
  ⟨fun f ↦ MulOpposite.unop f⟩

@[ext]
theorem StateTransformation.ext {f g : StateTransformation State}
    (h : ∀ q, f q = g q) : f = g := by
  exact MulOpposite.unop_injective (funext h)

/-- State transformations are just endofunctions, with a multiplication chosen below. -/
def stateTransformationEquiv : StateTransformation State ≃ (State → State) where
  toFun f := MulOpposite.unop f
  invFun f := MulOpposite.op f
  left_inv := MulOpposite.op_unop
  right_inv := MulOpposite.unop_op

@[simp]
theorem StateTransformation.one_apply (q : State) :
    (1 : StateTransformation State) q = q :=
  rfl

@[simp]
theorem StateTransformation.mul_apply (f g : StateTransformation State) (q : State) :
    (f * g) q = g (f q) :=
  rfl

/-- The transformation induced by reading a word in `M`. -/
def transitionTransformation (M : DFA Symbol State) (x : FreeMonoid Symbol) :
    StateTransformation State :=
  MulOpposite.op (transitionAction M x)

@[simp]
theorem transitionTransformation_apply (M : DFA Symbol State) (x : FreeMonoid Symbol)
    (q : State) : transitionTransformation M x q = M.evalFrom q (FreeMonoid.toList x) :=
  rfl

@[simp]
theorem transitionTransformation_one (M : DFA Symbol State) :
    transitionTransformation M 1 = 1 := by
  ext q
  rfl

@[simp]
theorem transitionTransformation_mul (M : DFA Symbol State) (x y : FreeMonoid Symbol) :
    transitionTransformation M (x * y) =
      transitionTransformation M x * transitionTransformation M y := by
  ext q
  exact DFA.evalFrom_of_append M q (FreeMonoid.toList x) (FreeMonoid.toList y)

/-- The transition morphism from the free monoid of words into state transformations. -/
def transitionMorphism (M : DFA Symbol State) :
    FreeMonoid Symbol →* StateTransformation State where
  toFun := transitionTransformation M
  map_one' := transitionTransformation_one M
  map_mul' := transitionTransformation_mul M

@[simp]
theorem transitionMorphism_apply (M : DFA Symbol State) (x : FreeMonoid Symbol) :
    transitionMorphism M x = transitionTransformation M x :=
  rfl

/-- The transition monoid is the image of the word action. -/
def TransitionMonoid (M : DFA Symbol State) := MonoidHom.mrange (transitionMorphism M)

/-- A word determines an element of the transition monoid. -/
def toTransitionMonoid (M : DFA Symbol State) (x : FreeMonoid Symbol) : TransitionMonoid M :=
  ⟨transitionMorphism M x, ⟨x, rfl⟩⟩

@[simp]
theorem toTransitionMonoid_val (M : DFA Symbol State) (x : FreeMonoid Symbol) :
    (toTransitionMonoid M x).val = transitionMorphism M x :=
  rfl

theorem toTransitionMonoid_surjective (M : DFA Symbol State) :
    Function.Surjective (toTransitionMonoid M) := by
  rintro ⟨f, x, rfl⟩
  exact ⟨x, rfl⟩

theorem toTransitionMonoid_eq_iff (M : DFA Symbol State) (x y : FreeMonoid Symbol) :
    toTransitionMonoid M x = toTransitionMonoid M y ↔
      transitionAction M x = transitionAction M y := by
  rw [Subtype.ext_iff]
  constructor
  · intro h
    exact congrArg MulOpposite.unop h
  · intro h
    exact StateTransformation.ext (congrFun h)

theorem transitionMorphism_eq_iff (M : DFA Symbol State) (x y : FreeMonoid Symbol) :
    transitionMorphism M x = transitionMorphism M y ↔
      transitionAction M x = transitionAction M y := by
  constructor
  · intro h
    exact congrArg MulOpposite.unop h
  · intro h
    exact StateTransformation.ext (congrFun h)

/-- For an accessible state-separated automaton, the syntactic congruence is the kernel of its
transition representation. -/
theorem syntacticCon_eq_transitionMorphism_ker (M : DFA Symbol State) (hacc : Accessible M)
    (hsep : StateSeparated M) : syntacticCon M.accepts = Con.ker (transitionMorphism M) := by
  apply Con.ext
  intro x y
  rw [syntacticCon_apply, Con.ker_rel]
  exact (syntacticRel_iff_transitionAction_eq M hacc hsep x y).trans
    (transitionMorphism_eq_iff M x y).symm

/-- The syntactic monoid of a language recognized by an accessible state-separated DFA embeds in
the full state-transformation monoid. -/
def syntacticActionHom (M : DFA Symbol State) (hacc : Accessible M) (hsep : StateSeparated M) :
    SyntacticMonoid M.accepts →* StateTransformation State :=
  (syntacticCon M.accepts).lift (transitionMorphism M) <| by
    intro x y hxy
    exact (transitionMorphism_eq_iff M x y).mpr <|
      (syntacticRel_iff_transitionAction_eq M hacc hsep x y).mp hxy

@[simp]
theorem syntacticActionHom_mk (M : DFA Symbol State) (hacc : Accessible M)
    (hsep : StateSeparated M) (x : FreeMonoid Symbol) :
    syntacticActionHom M hacc hsep (syntacticMorphism M.accepts x) = transitionMorphism M x :=
  Con.lift_mk' _ _

theorem syntacticActionHom_injective (M : DFA Symbol State) (hacc : Accessible M)
    (hsep : StateSeparated M) : Function.Injective (syntacticActionHom M hacc hsep) := by
  intro p q hpq
  induction p using Con.induction_on with
  | _ x =>
    induction q using Con.induction_on with
    | _ y =>
      apply (syntacticMorphism_eq_iff M.accepts x y).mpr
      apply (syntacticRel_iff_transitionAction_eq M hacc hsep x y).mpr
      change syntacticActionHom M hacc hsep (syntacticMorphism M.accepts x) =
        syntacticActionHom M hacc hsep (syntacticMorphism M.accepts y) at hpq
      rw [syntacticActionHom_mk, syntacticActionHom_mk] at hpq
      exact (transitionMorphism_eq_iff M x y).mp hpq

/-- The syntactic action has exactly the transition monoid as its range. -/
theorem syntacticActionHom_range (M : DFA Symbol State) (hacc : Accessible M)
    (hsep : StateSeparated M) :
    MonoidHom.mrange (syntacticActionHom M hacc hsep) = TransitionMonoid M := by
  ext f
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Con.induction_on with
    | _ x => exact ⟨x, syntacticActionHom_mk M hacc hsep x⟩
  · rintro ⟨x, rfl⟩
    exact ⟨syntacticMorphism M.accepts x, (syntacticActionHom_mk M hacc hsep x).symm⟩

end Cslib.Language
