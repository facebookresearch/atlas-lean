/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

-- Runtime fixtures and elaboration-time #eval require both import modes.
public import CSLibExt.Logics.LinearLogic.CLL.CutEliminationBridge
public meta import CSLibExt.Logics.LinearLogic.CLL.CutEliminationBridge
public import Cslib.Logics.LinearLogic.CLL.MLL
public meta import Cslib.Logics.LinearLogic.CLL.Basic

/-! # Consumers of the CLL source compatibility port -/

@[expose] public section

namespace Cslib.Logic.CLL.CutEliminationTests

open Cslib.Logic.InferenceSystem

abbrev F := Proposition Nat

/-- A principal unit cut, with genuinely non-cut-free input. -/
def unitCut : Proof ({(1 : F)} : Sequent Nat) :=
  (Proof.cut (a := 1) (Γ := 0) Proof.one (Proof.bot Proof.one)).rwConclusion
    (by simp)

example : unitCut.cutFree = false := by simp [unitCut, Proof.cutFree]

/-- The executable list entry point returns the existing pinned proof bundle. -/
def unitOutput : CutFreeProof ({(1 : F)} : Sequent Nat) :=
  Proof.cut_elim_list (Γ := [(1 : F)]) unitCut

example : unitOutput.val.cutFree = true := unitOutput.property

/-- info: (false, true) -/
#guard_msgs in
#eval (unitCut.cutFree, unitOutput.val.cutFree)

/-- A tensor/parr principal cut, reducing two proper subformula cuts. -/
def multiplicativeCut : Proof ({(1 : F)} : Sequent Nat) :=
  let p : Proof ((1 ⊗ 1 : F) ::ₘ 0) := Proof.tensor Proof.one Proof.one
  let q : Proof ((1 ⊗ 1 : F)⫠ ::ₘ {(1 : F)}) :=
    Proof.parr (Proof.bot (Proof.bot Proof.one))
  (Proof.cut p q).rwConclusion (by simp)

example : multiplicativeCut.cutFree = false := by
  simp [multiplicativeCut, Proof.cutFree]

/-- The cut-free output interoperates with the pinned MLL fragment. -/
def multiplicativeMLL : MLL.Proof ({(1 : F)} : Sequent Nat) :=
  let q := Proof.cut_elim_list (Γ := [(1 : F)]) multiplicativeCut
  q.val.cutFreeToMLL (by simp [Sequent.IsMLL]) q.property

/-- info: (false, true) -/
#guard_msgs in
#eval (multiplicativeCut.cutFree,
  (Proof.cut_elim_list (Γ := [(1 : F)]) multiplicativeCut).val.cutFree)

/-- Principal additive cuts exercise both selections, with different branches. -/
def additiveCut (right : Bool) : Proof ({(1 : F)} : Sequent Nat) :=
  let p : Proof ((1 ⊕ (1 ⊗ 1) : F) ::ₘ 0) :=
    if right then Proof.oplus₂ (Proof.tensor Proof.one Proof.one)
    else Proof.oplus₁ Proof.one
  let q : Proof ((1 ⊕ (1 ⊗ 1) : F)⫠ ::ₘ {(1 : F)}) :=
    Proof.with (Proof.bot Proof.one)
      (Proof.parr (Proof.bot (Proof.bot Proof.one)))
  (Proof.cut p q).rwConclusion (by simp)

example (right : Bool) : (additiveCut right).cutFree = false := by
  simp [additiveCut, Proof.cutFree]

/-- info: [(false, true), (false, true)] -/
#guard_msgs in
#eval [false, true].map fun right =>
  let p := additiveCut right
  (p.cutFree, (Proof.cut_elim_list (Γ := [(1 : F)]) p).val.cutFree)

/-- Promotion with a nonempty reusable context, not a closed special case. -/
def bangPremise : Proof ((!1 : F) ::ₘ {ʔ(Proposition.atom 0)}) :=
  Proof.bang (by simp [Sequent.allQuest, Multiset.fold])
    ((Proof.weaken (a := Proposition.atom 0) Proof.one).rwConclusion
      (Multiset.pair_comm _ _))

/-- Supply two selected derelictions through tensor, then contract them. -/
def duplicationSupply : Proof ((ʔ⊥ : F) ::ₘ {(1 ⊗ 1 : F)}) :=
  let p : Proof ((1 : F) ::ₘ {(ʔ⊥ : F)}) :=
    (Proof.quest (Proof.bot Proof.one)).rwConclusion (Multiset.pair_comm _ _)
  Proof.contract ((Proof.tensor p p).rwConclusion (by grind only [multiset]))

example : bangPremise.cutFree = true := by
  simp [bangPremise, Proof.cutFree]

example : duplicationSupply.cutFree = true := by
  simp only [duplicationSupply, Proof.cutFree_rwConclusion, Proof.cutFree,
    Bool.and_self]

/-- Exponential cut duplicating and recontracting a nonempty context. -/
def exponentialCut : Proof ([ʔ(Proposition.atom 0), (1 ⊗ 1 : F)] :
    Sequent Nat) := Proof.cut bangPremise duplicationSupply

example : exponentialCut.cutFree = false := rfl

/-- Actual cut-free output in the existing canonical proof bundle. -/
def exponentialOutput : CutFreeProof
    ([ʔ(Proposition.atom 0), (1 ⊗ 1 : F)] : Sequent Nat) :=
  Proof.cut_elim_list (Γ := [ʔ(Proposition.atom 0), (1 ⊗ 1 : F)])
    exponentialCut

example : exponentialOutput.val.cutFree = true := exponentialOutput.property

/-- info: (false, true) -/
#guard_msgs in
#eval (exponentialCut.cutFree, exponentialOutput.val.cutFree)

/-- The quest-first orientation invokes the source exponential reversal. -/
def questOrientationCut : Proof ([(1 ⊗ 1 : F), ʔ(Proposition.atom 0)] :
    Sequent Nat) := Proof.cut' (a := !1) duplicationSupply bangPremise

/-- Selected weakening discards the cut formula, retaining the reusable context. -/
def weakeningCut : Proof ([ʔ(Proposition.atom 0), (1 : F)] : Sequent Nat) :=
  Proof.cut bangPremise (Proof.weaken (a := ⊥) Proof.one)

example : weakeningCut.cutFree = false := rfl

/-- info: [(false, true), (false, true)] -/
#guard_msgs in
#eval [(questOrientationCut.cutFree,
    (Proof.cut_elim_list (Γ := [(1 ⊗ 1 : F), ʔ(Proposition.atom 0)])
      questOrientationCut).val.cutFree),
  (weakeningCut.cutFree,
    (Proof.cut_elim_list (Γ := [ʔ(Proposition.atom 0), (1 : F)])
      weakeningCut).val.cutFree)]

/-- Test-only traversal of actual original proof values, not a new judgement. -/
def proofRules {Atom : Type*} {Γ : Sequent Atom} : Proof Γ → List String
  | .ax => ["ax"]
  | .one => ["one"]
  | .top => ["top"]
  | .cut p q => "cut" :: (proofRules p ++ proofRules q)
  | .tensor p q => "tensor" :: (proofRules p ++ proofRules q)
  | .with p q => "with" :: (proofRules p ++ proofRules q)
  | .bot p => "bot" :: proofRules p
  | .parr p => "parr" :: proofRules p
  | .oplus₁ p => "oplus1" :: proofRules p
  | .oplus₂ p => "oplus2" :: proofRules p
  | .quest p => "quest" :: proofRules p
  | .weaken p => "weaken" :: proofRules p
  | .contract p => "contract" :: proofRules p
  | .bang _ p => "bang" :: proofRules p

/-- Atom equality is enough; this type intentionally has no BEq instance. -/
inductive Token where
  | p | q
  deriving DecidableEq

/-- An atom cut over a carrier lacking Boolean equality. -/
def noBEqCut : Proof
    ([Proposition.atomDual Token.p, Proposition.atom Token.p] : Sequent Token) :=
  Proof.cut (Proof.ax (a := Proposition.atom Token.p))
    (Proof.ax (a := Proposition.atomDual Token.p))

/-- info: (false, true) -/
#guard_msgs in
#eval (noBEqCut.cutFree,
  (Proof.cut_elim_list
    (Γ := [Proposition.atomDual Token.p, Proposition.atom Token.p])
    noBEqCut).val.cutFree)

-- Universality: no decidable equality or list presentation is assumed here.
example {Atom : Type*} {Γ : Sequent Atom} (p : Proof Γ) :
    ∃ q : Proof Γ, q.cutFree := ⟨p.cut_elim.val, p.cut_elim.property⟩

/-- Reverse multiplicative orientation exercises parr/tensor principal reduction. -/
def multiplicativeReverseCut : Proof ({(1 : F)} : Sequent Nat) :=
  let p : Proof ((1 ⊗ 1 : F) ::ₘ 0) := Proof.tensor Proof.one Proof.one
  let q : Proof ((1 ⊗ 1 : F)⫠ ::ₘ {(1 : F)}) :=
    Proof.parr (Proof.bot (Proof.bot Proof.one))
  (Proof.cut' (a := 1 ⊗ 1) q p).rwConclusion (by simp)

/-- info: (false, true) -/
#guard_msgs in
#eval (multiplicativeReverseCut.cutFree,
  (Proof.cut_elim_list (Γ := [(1 : F)]) multiplicativeReverseCut).val.cutFree)

/-- Reverse additive cuts exercise with/oplus principal reductions. -/
def additiveReverseCut (right : Bool) : Proof ({(1 : F)} : Sequent Nat) :=
  let p : Proof ((1 ⊕ (1 ⊗ 1) : F) ::ₘ 0) :=
    if right then Proof.oplus₂ (Proof.tensor Proof.one Proof.one)
    else Proof.oplus₁ Proof.one
  let q : Proof ((1 ⊕ (1 ⊗ 1) : F)⫠ ::ₘ {(1 : F)}) :=
    Proof.with (Proof.bot Proof.one)
      (Proof.parr (Proof.bot (Proof.bot Proof.one)))
  (Proof.cut' (a := 1 ⊕ (1 ⊗ 1)) q p).rwConclusion (by simp)

/-- info: [(false, true), (false, true)] -/
#guard_msgs in
#eval [false, true].map fun right =>
  let p := additiveReverseCut right
  (p.cutFree, (Proof.cut_elim_list (Γ := [(1 : F)]) p).val.cutFree)

/-- Real cuts below every recursive proof constructor. -/
def structuralCases : List (String × (Σ Γ : List F, Proof (Γ : Sequent Nat))) :=
  [("bot", ⟨[⊥, 1], Proof.bot unitCut⟩),
   ("parr", ⟨[⊥ ⅋ 1], Proof.parr (Proof.bot unitCut)⟩),
   ("tensor", ⟨[1 ⊗ 1], Proof.tensor unitCut unitCut⟩),
   ("oplus1", ⟨[1 ⊕ 0], Proof.oplus₁ unitCut⟩),
   ("oplus2", ⟨[0 ⊕ 1], Proof.oplus₂ unitCut⟩),
   ("with", ⟨[1 & 1], Proof.with unitCut unitCut⟩),
   ("quest", ⟨[ʔ1], Proof.quest unitCut⟩),
   ("weaken", ⟨[ʔ0, 1], Proof.weaken unitCut⟩),
   ("contract", ⟨[ʔ0, 1], Proof.contract (Proof.weaken (Proof.weaken unitCut))⟩),
   ("bang", ⟨[!1], Proof.bang rfl unitCut⟩)]

/-- info: (10, true) -/
#guard_msgs in
#eval (structuralCases.length, structuralCases.all fun (_, ⟨Γ, p⟩) =>
  !p.cutFree && (Proof.cut_elim_list (Γ := Γ) p).val.cutFree)

/-- A selected unit is behind a nonprincipal bot rule and an exchange. -/
def commutingCut : Proof ([⊥, (1 : F)] : Sequent Nat) :=
  Proof.cut (a := 1)
    ((Proof.bot Proof.one).rwConclusion (Multiset.pair_comm _ _))
    (Proof.bot Proof.one)

/-- info: (false, true) -/
#guard_msgs in
#eval (commutingCut.cutFree,
  (Proof.cut_elim_list (Γ := [⊥, (1 : F)]) commutingCut).val.cutFree)

/-- info: (true, true, true) -/
#guard_msgs in
#eval ((Proof.cut_elim_list (Γ := [(1 : F)]) Proof.one).val.cutFree,
  (Proof.cut_elim_list (Γ := [(⊤ : F), 0])
    (Proof.top (Γ := {(0 : F)}))).val.cutFree,
  (Proof.cut_elim_list (Γ := [Proposition.atom 0, Proposition.atomDual 0])
    Proof.ax).val.cutFree)

end Cslib.Logic.CLL.CutEliminationTests
