/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Cslib.Logics.LinearLogic.CLL.Basic
public import CSLibExt.Languages.SessionTypes.Branching

/-!
# Classical processes: session reading of propositions

A partial reading of classical-linear-logic propositions as binary
branching session types. The polarity is Wadler's GV-to-CP translation in
*Propositions as Sessions* (ICFP 2012), Section 3.1, read backwards:
tensor becomes receive, par becomes send of the dual payload proposition,
additive conjunction becomes internal choice, and additive disjunction
becomes external choice. Both multiplicative units become `end`.

This is only a partial, lossy bridge. It is undefined at atoms and
exponentials in positions that must themselves be read. The first
argument of tensor or par is carried as an opaque CLL proposition in the
branching type's payload sort; it is not recursively read and no channel
delegation meaning is claimed for it. The map is not injective, since `1`
and `⊥` both map to `end`. The empty choices for `⊤` and `0` extend the
source's finite labelled-choice clauses to the nullary case.

No GV calculus, translation of processes, or preservation theorem is
formalized here.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.ClassicalProcesses

variable {Atom : Type}

/-- The two positional labels used for binary additive choices. -/
inductive TwoLabel where
  | left : TwoLabel
  | right : TwoLabel
deriving DecidableEq, Repr

/-- Read a CLL proposition as a binary branching type, when every
subproposition that must itself be read lies in the atom- and
exponential-free fragment. Payload propositions of tensor and par are
carried opaquely, as described in the module documentation. -/
def sessionReading :
    Logic.CLL.Proposition Atom →
      Option (SessionTypes.BranchingType
        (Logic.CLL.Proposition Atom) TwoLabel)
  | .atom _ => none
  | .atomDual _ => none
  | .one => some .end
  | .zero => some (.branch .nil)
  | .top => some (.select .nil)
  | .bot => some .end
  | .tensor a b => (sessionReading b).map (.recv a)
  | .parr a b => (sessionReading b).map (.send a.dual)
  | .oplus a b =>
      match sessionReading a, sessionReading b with
      | some x, some y =>
          some (.branch (.cons .left x (.cons .right y .nil)))
      | _, _ => none
  | .with a b =>
      match sessionReading a, sessionReading b with
      | some x, some y =>
          some (.select (.cons .left x (.cons .right y .nil)))
      | _, _ => none
  | .bang _ => none
  | .quest _ => none

/-- The session reading commutes with duality. -/
theorem sessionReading_dual (a : Logic.CLL.Proposition Atom) :
    sessionReading a.dual =
      (sessionReading a).map SessionTypes.BranchingType.dual := by
  induction a with
  | atom _ => rfl
  | atomDual _ => rfl
  | one => rfl
  | zero => rfl
  | top => rfl
  | bot => rfl
  | tensor a b _ ihB =>
      simp only [Logic.CLL.Proposition.dual, sessionReading,
        Logic.CLL.Proposition.dual_involution, ihB, Option.map_map]
      rfl
  | parr a b _ ihB =>
      simp only [Logic.CLL.Proposition.dual, sessionReading,
        ihB, Option.map_map]
      rfl
  | oplus a b ihA ihB =>
      simp only [Logic.CLL.Proposition.dual, sessionReading,
        ihA, ihB]
      cases hA : sessionReading a <;>
        cases hB : sessionReading b <;>
        simp only [Option.map_none, Option.map_some,
          SessionTypes.BranchingType.dual,
          SessionTypes.BranchingType.Branches.dual]
  | «with» a b ihA ihB =>
      simp only [Logic.CLL.Proposition.dual, sessionReading,
        ihA, ihB]
      cases hA : sessionReading a <;>
        cases hB : sessionReading b <;>
        simp only [Option.map_none, Option.map_some,
          SessionTypes.BranchingType.dual,
          SessionTypes.BranchingType.Branches.dual]
  | bang _ _ => rfl
  | quest _ _ => rfl

/-- Every proposition in the image of the session reading is a
well-formed branching type. -/
theorem sessionReading_wellFormed {a : Logic.CLL.Proposition Atom}
    {t : SessionTypes.BranchingType (Logic.CLL.Proposition Atom) TwoLabel}
    (h : sessionReading a = some t) : t.WellFormed := by
  induction a generalizing t with
  | atom _ =>
      simp only [sessionReading] at h
      cases h
  | atomDual _ =>
      simp only [sessionReading] at h
      cases h
  | one =>
      simp only [sessionReading] at h
      cases h
      constructor
  | zero =>
      simp only [sessionReading] at h
      cases h
      constructor
      constructor
  | top =>
      simp only [sessionReading] at h
      cases h
      constructor
      constructor
  | bot =>
      simp only [sessionReading] at h
      cases h
      constructor
  | tensor _ b _ ihB =>
      simp only [sessionReading] at h
      cases hB : sessionReading b with
      | none =>
          simp only [hB] at h
          cases h
      | some _y =>
          simp only [hB] at h
          cases h
          constructor
          exact ihB hB
  | parr _ b _ ihB =>
      simp only [sessionReading] at h
      cases hB : sessionReading b with
      | none =>
          simp only [hB] at h
          cases h
      | some _y =>
          simp only [hB] at h
          cases h
          constructor
          exact ihB hB
  | oplus a b ihA ihB =>
      simp only [sessionReading] at h
      cases hA : sessionReading a with
      | none =>
          simp only [hA] at h
          cases h
      | some _x =>
          cases hB : sessionReading b with
          | none =>
              simp only [hA, hB] at h
              cases h
          | some _y =>
              simp only [hA, hB] at h
              cases h
              constructor
              constructor
              · simp only [SessionTypes.BranchingType.Branches.labels,
                  SessionTypes.BranchingType.Branches.entries, List.map,
                  List.mem_cons, List.not_mem_nil, reduceCtorEq, or_false,
                  not_false_eq_true]
              · exact ihA hA
              · constructor
                · simp only [SessionTypes.BranchingType.Branches.labels,
                    SessionTypes.BranchingType.Branches.entries, List.map,
                    List.not_mem_nil, not_false_eq_true]
                · exact ihB hB
                · constructor
  | «with» a b ihA ihB =>
      simp only [sessionReading] at h
      cases hA : sessionReading a with
      | none =>
          simp only [hA] at h
          cases h
      | some _x =>
          cases hB : sessionReading b with
          | none =>
              simp only [hA, hB] at h
              cases h
          | some _y =>
              simp only [hA, hB] at h
              cases h
              constructor
              constructor
              · simp only [SessionTypes.BranchingType.Branches.labels,
                  SessionTypes.BranchingType.Branches.entries, List.map,
                  List.mem_cons, List.not_mem_nil, reduceCtorEq, or_false,
                  not_false_eq_true]
              · exact ihA hA
              · constructor
                · simp only [SessionTypes.BranchingType.Branches.labels,
                    SessionTypes.BranchingType.Branches.entries, List.map,
                    List.not_mem_nil, not_false_eq_true]
                · exact ihB hB
                · constructor
  | bang _ _ =>
      simp only [sessionReading] at h
      cases h
  | quest _ _ =>
      simp only [sessionReading] at h
      cases h

end Cslib.ClassicalProcesses
