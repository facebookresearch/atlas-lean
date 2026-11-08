/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.PiCalculus.Behavioural
public import CSLibExt.Languages.PiCalculus.Scoping
public import Cslib.Foundations.Syntax.Congruence

/-!
# Structural laws under π-calculus observers

`Context` is a single-hole lexical context using the existing process
constructors, with the canonical CSLib `HasContext` interface.
`Cong.contextualBarbedEquiv` proves that every structural law remains
strong barbed bisimilar under these contexts. This is structural soundness,
not a claim that bare barbed bisimilarity is a parallel/prefix congruence.

Filling is literal de Bruijn syntax filling. It is capture-avoiding for
locally closed holes (`Proc.ClosedAt 0`): `liftProc_eq_of_closedAt` proves that
surrounding input/restriction binders cannot capture their names. For open
holes, references into context binders are intentional lexical binding;
no capture-avoiding theorem for arbitrary open holes is asserted.
-/

@[expose] public section

namespace Cslib.PiCalculus

/-- One-hole lexical contexts, including guards, choice and replication. -/
inductive Context where
  | hole
  | out (a b : Name) (c : Context)
  | inp (a : Name) (c : Context)
  | parL (c : Context) (p : Proc)
  | parR (p : Proc) (c : Context)
  | nu (c : Context)
  | repl (c : Context)
  | sumL (c : Context) (p : Proc)
  | sumR (p : Proc) (c : Context)

/-- Fill the lexical hole. Free constants are never captured; locally
closed hole processes have no references into surrounding binders. -/
def Context.fill : Context → Proc → Proc
  | .hole, p => p
  | .out a b c, p => .out a b (c.fill p)
  | .inp a c, p => .inp a (c.fill p)
  | .parL c q, p => .par (c.fill p) q
  | .parR q c, p => .par q (c.fill p)
  | .nu c, p => .nu (c.fill p)
  | .repl c, p => .repl (c.fill p)
  | .sumL c q, p => .sum (c.fill p) q
  | .sumR q c, p => .sum q (c.fill p)

instance : HasContext Proc where
  Context := Context
  fill := Context.fill

/-- Structural congruence survives every one-hole lexical context. -/
theorem Cong.fill {p q : Proc} (h : Cong p q) (c : Context) :
    Cong (c.fill p) (c.fill q) := by
  induction c with
  | hole => exact h
  | out a b _ ih => exact Cong.out_cong a b ih
  | inp a _ ih => exact Cong.inp_cong a ih
  | parL _ r ih => exact Cong.par_cong ih (.refl r)
  | parR r _ ih => exact Cong.par_cong (.refl r) ih
  | nu _ ih => exact Cong.nu_cong ih
  | repl _ ih => exact Cong.repl_cong ih
  | sumL _ r ih => exact Cong.sum_cong ih (.refl r)
  | sumR r _ ih => exact Cong.sum_cong (.refl r) ih

/-- Substitute a context into the hole of another context. -/
def Context.comp : Context → Context → Context
  | .hole, d => d
  | .out a b c, d => .out a b (c.comp d)
  | .inp a c, d => .inp a (c.comp d)
  | .parL c p, d => .parL (c.comp d) p
  | .parR p c, d => .parR p (c.comp d)
  | .nu c, d => .nu (c.comp d)
  | .repl c, d => .repl (c.comp d)
  | .sumL c p, d => .sumL (c.comp d) p
  | .sumR p c, d => .sumR p (c.comp d)

/-- Context composition agrees with iterated filling. -/
@[simp] theorem Context.fill_comp (c d : Context) (p : Proc) :
    (c.comp d).fill p = c.fill (d.fill p) := by
  induction c <;> simp_all [Context.comp, Context.fill]

/-- Strong barbed equivalence in every lexical process context. For
capture-avoiding use, both hole processes must satisfy `Proc.ClosedAt 0`. -/
def ContextualBarbedEquiv (p q : Proc) : Prop :=
  ∀ c : Context, BarbedBisimilar (c.fill p) (c.fill q)

/-- Structural congruence is sound under every observer context, with
one-for-one reduction matching and immediate input/output barbs. -/
theorem Cong.contextualBarbedEquiv {p q : Proc} (h : Cong p q) :
    ContextualBarbedEquiv p q :=
  fun c => (h.fill c).barbedBisimilar

/-- Contextual barbed equivalence survives filling a context. -/
theorem ContextualBarbedEquiv.fill {p q : Proc}
    (h : ContextualBarbedEquiv p q) (d : Context) :
    ContextualBarbedEquiv (d.fill p) (d.fill q) := by
  intro c
  simpa only [Context.fill_comp] using h (c.comp d)

/-- Contextual barbed equivalence implies standalone barbed bisimilarity. -/
theorem ContextualBarbedEquiv.barbedBisimilar {p q : Proc}
    (h : ContextualBarbedEquiv p q) : BarbedBisimilar p q :=
  h .hole

instance : Congruence ContextualBarbedEquiv := ⟨⟩

/-- Context closure is an equivalence relation and a congruence for the
canonical CSLib context interface. This does not assert the same of bare
`BarbedBisimilar`. -/
instance : LawfulCongruence ContextualBarbedEquiv where
  refl _ _ := LTS.HomBisimilarity.refl _
  symm _ _ h c := LTS.Bisimilarity.symm (h c)
  trans _ _ _ h₁ h₂ c := LTS.Bisimilarity.trans (h₁ c) (h₂ c)
  elim c _ _ h := h.fill c

/-- Capture-avoiding filling: each context binder shifts dangling names
of the hole, while binders internal to the hole remain untouched. -/
def Context.fillAvoiding : Context → Proc → Proc
  | .hole, p => p
  | .out a b c, p => .out a b (c.fillAvoiding p)
  | .inp a c, p => .inp a (c.fillAvoiding (liftProc 0 p))
  | .parL c q, p => .par (c.fillAvoiding p) q
  | .parR q c, p => .par q (c.fillAvoiding p)
  | .nu c, p => .nu (c.fillAvoiding (liftProc 0 p))
  | .repl c, p => .repl (c.fillAvoiding p)
  | .sumL c q, p => .sum (c.fillAvoiding p) q
  | .sumR q c, p => .sum q (c.fillAvoiding p)

/-- Lexical and capture-avoiding filling agree for locally closed holes.
This is the explicit admissibility condition for the contextual theorem. -/
theorem Context.fillAvoiding_eq {p : Proc} (h : Proc.ClosedAt 0 p)
    (c : Context) : c.fillAvoiding p = c.fill p := by
  induction c <;>
    simp_all [Context.fillAvoiding, Context.fill, liftProc_eq_of_closedAt h]

/-- Every structural law is strongly barbed sound under capture-avoiding
contexts, for locally closed hole processes. -/
theorem Cong.fillAvoiding_barbedBisimilar {p q : Proc} (h : Cong p q)
    (hp : Proc.ClosedAt 0 p) (hq : Proc.ClosedAt 0 q) (c : Context) :
    BarbedBisimilar (c.fillAvoiding p) (c.fillAvoiding q) := by
  rw [c.fillAvoiding_eq hp, c.fillAvoiding_eq hq]
  exact h.contextualBarbedEquiv c

end Cslib.PiCalculus
