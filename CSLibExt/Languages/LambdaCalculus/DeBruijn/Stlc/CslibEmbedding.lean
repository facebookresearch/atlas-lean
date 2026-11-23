/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Embedding intrinsic de Bruijn STLC into upstream locally nameless STLC
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.CslibBridge
public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.ElaborationSubstitution

/-!
# Embedding intrinsic STLC into upstream locally nameless STLC

This module erases an intrinsically typed term to the existing annotated de Bruijn syntax and
then translates that syntax to upstream locally nameless terms.  Bound indices remain bound
indices.  The variables supplied by the intrinsic typing context become distinct free natural
numbers, so the translation also supports open terms.

The main result, `Tm.toLocallyNameless_typing`, transports intrinsic typing to upstream
`LocallyNameless.Stlc.Typing`.  In particular, every translated term is locally closed.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open Cslib.LambdaCalculus.LocallyNameless.Untyped
open scoped CslibStlc

universe u

variable {Base : Type u}
variable {A B C : Ty Base}
variable {Γ Δ : List (Ty Base)}

/-- Upstream locally nameless untyped terms with natural-number free variables. -/
abbrev LocallyNamelessTerm :=
  Cslib.LambdaCalculus.LocallyNameless.Untyped.Term Nat

/-- Upstream locally nameless typing contexts with natural-number free variables. -/
abbrev LocallyNamelessContext (Base : Type u) :=
  Cslib.LambdaCalculus.LocallyNameless.Context Nat (LocallyNamelessTy Base)

namespace RawTm

/-- Translate annotated de Bruijn syntax to upstream locally nameless syntax.

Indices below `depth` are bound by surrounding lambdas.  The remaining indices refer to the
source typing context and are translated through `names`.  The default branch is unreachable on
erasures of well-typed intrinsic terms when `names` has the context's length. -/
def toLocallyNamelessAux (depth : Nat) (names : List Nat) :
    RawTm Base → LocallyNamelessTerm
  | .var n =>
      if n < depth then .bvar n else .fvar (names.getD (n - depth) 0)
  | .app f a => .app (toLocallyNamelessAux depth names f)
      (toLocallyNamelessAux depth names a)
  | .lam _ body => .abs (toLocallyNamelessAux (depth + 1) names body)

@[simp]
theorem toLocallyNamelessAux_app (depth : Nat) (names : List Nat)
    (f a : RawTm Base) :
    toLocallyNamelessAux depth names (.app f a) =
      .app (toLocallyNamelessAux depth names f)
        (toLocallyNamelessAux depth names a) := rfl

@[simp]
theorem toLocallyNamelessAux_lam (depth : Nat) (names : List Nat)
    (A : Ty Base) (body : RawTm Base) :
    toLocallyNamelessAux depth names (.lam A body) =
      .abs (toLocallyNamelessAux (depth + 1) names body) := rfl

/-- Opening the next translated binder extends the list of free-variable names. -/
theorem open_toLocallyNamelessAux (raw : RawTm Base) (depth : Nat)
    (names : List Nat) (x : Nat) :
    Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.openRec depth (.fvar x)
        (toLocallyNamelessAux (depth + 1) names raw) =
      toLocallyNamelessAux depth (x :: names) raw := by
  induction raw generalizing depth with
  | var n =>
      by_cases hlt : n < depth
      · have hlt' : n < depth + 1 := by omega
        simp [toLocallyNamelessAux, hlt, hlt', Term.openRec_bvar,
          show depth ≠ n by omega]
      · by_cases heq : n = depth
        · subst n
          simp [toLocallyNamelessAux, Term.openRec_bvar]
        · have hge : depth + 1 ≤ n := by omega
          have hsub : n - depth = (n - (depth + 1)) + 1 := by omega
          simp [toLocallyNamelessAux, hlt, Nat.not_lt.mpr hge, hsub,
            Term.openRec_fvar]
  | app f a ihf iha =>
      rw [toLocallyNamelessAux_app, Term.openRec_app, ihf, iha]
      rfl
  | lam A body ih =>
      rw [toLocallyNamelessAux_lam, Term.openRec_abs,
        toLocallyNamelessAux_lam]
      simpa [Nat.add_assoc] using ih (depth + 1)

/-- Shifted erasures cancel the additional target binder depth. -/
theorem toLocallyNamelessAux_shift (raw : RawTm Base) (amount cutoff : Nat)
    (names : List Nat) :
    toLocallyNamelessAux (amount + cutoff) names (raw.shift amount cutoff) =
      toLocallyNamelessAux cutoff names raw := by
  induction raw generalizing cutoff with
  | var n =>
      by_cases hlt : n < cutoff
      · have hlt' : n < amount + cutoff := by omega
        have hnle : ¬cutoff ≤ n := by omega
        simp [RawTm.shift, toLocallyNamelessAux, hlt, hlt', hnle]
      · have hge : cutoff ≤ n := by omega
        have hge' : amount + cutoff ≤ n + amount := by omega
        have hsub : n + amount - (amount + cutoff) = n - cutoff := by omega
        simp [RawTm.shift, toLocallyNamelessAux, hge, Nat.not_lt.mpr hge', hsub]
  | app f a ihf iha =>
      simp [RawTm.shift, toLocallyNamelessAux, ihf, iha]
  | lam A body ih =>
      simp only [RawTm.shift, toLocallyNamelessAux_lam]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (cutoff + 1)

private def bumpIndex (cutoff n : Nat) : Nat :=
  if cutoff ≤ n then n + 1 else n

private theorem liftRen_bumpIndex (cutoff : Nat) :
    RawTm.liftRen (bumpIndex cutoff) = bumpIndex (cutoff + 1) := by
  funext n
  cases n with
  | zero => simp [RawTm.liftRen, bumpIndex]
  | succ n =>
      by_cases h : cutoff ≤ n
      · have h' : cutoff + 1 ≤ n + 1 := by omega
        simp [RawTm.liftRen, bumpIndex, h, h']
      · have h' : ¬cutoff + 1 ≤ n + 1 := by omega
        simp [RawTm.liftRen, bumpIndex, h, h']

private theorem rename_bumpIndex (raw : RawTm Base) (cutoff : Nat) :
    RawTm.rename (bumpIndex cutoff) raw = raw.shift 1 cutoff := by
  induction raw generalizing cutoff with
  | var n => simp [RawTm.rename, RawTm.shift, bumpIndex]
  | app f a ihf iha => simp [RawTm.rename, RawTm.shift, ihf, iha]
  | lam A body ih =>
      simp only [RawTm.rename, RawTm.shift]
      rw [liftRen_bumpIndex, ih]

private theorem shift_add (raw : RawTm Base) (m n cutoff : Nat) :
    (raw.shift m cutoff).shift n cutoff = raw.shift (m + n) cutoff := by
  induction raw generalizing cutoff with
  | var i =>
      by_cases h : cutoff ≤ i
      · have h' : cutoff ≤ i + m := by omega
        simp [RawTm.shift, h, h']
        omega
      · simp [RawTm.shift, h]
  | app f a ihf iha => simp [RawTm.shift, ihf, iha]
  | lam A body ih =>
      simp only [RawTm.shift]
      rw [ih]

private theorem rename_succ_shift (raw : RawTm Base) (depth : Nat) :
    RawTm.rename Nat.succ (raw.shift depth) = raw.shift (depth + 1) := by
  have hbump : bumpIndex 0 = Nat.succ := by
    funext n
    simp [bumpIndex, Nat.succ_eq_add_one]
  rw [← hbump, rename_bumpIndex, shift_add]

/-- One-variable de Bruijn substitution at an arbitrary surrounding binder depth. -/
def betaSub (depth : Nat) (arg : RawTm Base) : RawTm.RawSub Base := fun n ↦
  if n < depth then .var n
  else if n = depth then arg.shift depth
  else .var (n - 1)

/-- Lifting a beta substitution increments its binder depth. -/
theorem liftSub_betaSub (depth : Nat) (arg : RawTm Base) :
    RawTm.liftSub (betaSub depth arg) = betaSub (depth + 1) arg := by
  funext n
  cases n with
  | zero => simp [RawTm.liftSub, betaSub]
  | succ n =>
      by_cases hlt : n < depth
      · have hlt' : n + 1 < depth + 1 := by omega
        simp [RawTm.liftSub, betaSub, hlt, hlt']
      · by_cases heq : n = depth
        · subst n
          simp only [RawTm.liftSub, betaSub, lt_self_iff_false, ↓reduceIte]
          exact rename_succ_shift arg depth
        · have hgt : depth < n := by omega
          have hgt' : depth + 1 < n + 1 := by omega
          have hnot : ¬n + 1 < depth + 1 := by omega
          simp [RawTm.liftSub, betaSub, hlt, heq, hnot]
          omega

/-- Translating one-variable raw substitution is upstream opening. -/
theorem toLocallyNamelessAux_betaSub (raw arg : RawTm Base) (depth : Nat)
    (names : List Nat) :
    toLocallyNamelessAux depth names
        (RawTm.substAll (betaSub depth arg) raw) =
      Term.openRec depth (toLocallyNamelessAux 0 names arg)
        (toLocallyNamelessAux (depth + 1) names raw) := by
  induction raw generalizing depth with
  | var n =>
      by_cases hlt : n < depth
      · have hlt' : n < depth + 1 := by omega
        simp [RawTm.substAll, betaSub, toLocallyNamelessAux, hlt, hlt',
          Term.openRec_bvar, show depth ≠ n by omega]
      · by_cases heq : n = depth
        · subst n
          simp only [RawTm.substAll_var]
          rw [show betaSub depth arg depth = arg.shift depth by simp [betaSub]]
          have hshift := toLocallyNamelessAux_shift arg depth 0 names
          simp only [Nat.add_zero] at hshift
          rw [hshift]
          simp [toLocallyNamelessAux, Term.openRec_bvar]
        · have hgt : depth < n := by omega
          have hge : depth + 1 ≤ n := by omega
          have hp : depth ≤ n - 1 := by omega
          have hpred : n - 1 - depth = n - (depth + 1) := by omega
          simp [RawTm.substAll, betaSub, toLocallyNamelessAux, hlt, heq,
            Nat.not_lt.mpr hge, Nat.not_lt.mpr hp, hpred, Term.openRec_fvar]
  | app f a ihf iha =>
      simp [RawTm.substAll, toLocallyNamelessAux, Term.openRec_app, ihf, iha]
  | lam A body ih =>
      rw [RawTm.substAll_lam, liftSub_betaSub, toLocallyNamelessAux_lam,
        toLocallyNamelessAux_lam, Term.openRec_abs, ih]

/-- At depth zero, `betaSub` is the existing single raw substitution. -/
theorem betaSub_zero (arg : RawTm Base) :
    betaSub 0 arg = RawTm.singleSub arg := by
  funext n
  cases n <;> simp [betaSub, RawTm.singleSub]

end RawTm

/-- Pair source-context types with a list of free-variable names. -/
def locallyNamelessContextWith :
    List Nat → List (Ty Base) → LocallyNamelessContext Base
  | x :: names, A :: Γ =>
      ⟨x, Ty.toLocallyNameless A⟩ :: locallyNamelessContextWith names Γ
  | _, _ => []

/-- With equally long inputs, the keys of the translated context are exactly its names. -/
@[simp]
theorem locallyNamelessContextWith_keys {names : List Nat}
    (hlen : names.length = Γ.length) :
    (locallyNamelessContextWith (Base := Base) names Γ).keys = names := by
  induction names generalizing Γ with
  | nil =>
      cases Γ <;> simp [locallyNamelessContextWith]
  | cons x names ih =>
      cases Γ with
      | nil => simp at hlen
      | cons A Γ =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp [locallyNamelessContextWith, ih hlen]

/-- Distinct context names give a well-formed upstream context. -/
theorem locallyNamelessContextWith_wellFormed {names : List Nat}
    (hlen : names.length = Γ.length) (hnames : names.Nodup) :
    (locallyNamelessContextWith (Base := Base) names Γ)✓ := by
  change (locallyNamelessContextWith (Base := Base) names Γ).NodupKeys
  change (locallyNamelessContextWith (Base := Base) names Γ).keys.Nodup
  rw [locallyNamelessContextWith_keys hlen]
  exact hnames

namespace Var

/-- The erased de Bruijn index of a typed variable is in range of its context. -/
@[simp]
theorem toNat_lt_length (x : Var Γ A) : x.toNat < Γ.length := by
  induction x with
  | zero => simp [toNat]
  | succ x ih => simp [toNat, ih]

/-- A typed source variable becomes a member of the translated upstream context. -/
theorem mem_locallyNamelessContextWith {names : List Nat}
    (x : Var Γ A) (hlen : names.length = Γ.length) :
    Sigma.mk (names.getD x.toNat 0) (Ty.toLocallyNameless A) ∈
      locallyNamelessContextWith (Base := Base) names Γ := by
  induction x generalizing names with
  | zero =>
      cases names with
      | nil => simp at hlen
      | cons name names => simp [toNat, locallyNamelessContextWith]
  | succ x ih =>
      cases names with
      | nil => simp at hlen
      | cons name names =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          apply List.mem_cons_of_mem
          simpa [toNat] using ih (names := names) hlen

end Var

namespace Tm

/-- Translate an intrinsic term, assigning the source context the supplied free names. -/
def toLocallyNamelessWith (names : List Nat) (t : Tm Γ A) :
    LocallyNamelessTerm :=
  RawTm.toLocallyNamelessAux 0 names t.erase

@[simp]
theorem toLocallyNamelessWith_var (names : List Nat) (x : Var Γ A) :
    toLocallyNamelessWith names (.var x) = .fvar (names.getD x.toNat 0) := by
  simp [toLocallyNamelessWith, RawTm.toLocallyNamelessAux]

@[simp]
theorem toLocallyNamelessWith_app (names : List Nat)
    (f : Tm Γ (A ⇒ B)) (a : Tm Γ A) :
    toLocallyNamelessWith names (.app f a) =
      .app (toLocallyNamelessWith names f) (toLocallyNamelessWith names a) := rfl

@[simp]
theorem toLocallyNamelessWith_lam (names : List Nat)
    (body : Tm (A :: Γ) B) :
    toLocallyNamelessWith names (.lam body) =
      .abs (RawTm.toLocallyNamelessAux 1 names body.erase) := rfl

/-- Opening a translated lambda body gives the translation with the fresh name prepended. -/
@[simp]
theorem open_toLocallyNamelessWith_lam (names : List Nat)
    (body : Tm (A :: Γ) B) (x : Nat) :
    Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open'
        (RawTm.toLocallyNamelessAux 1 names body.erase) (.fvar x) =
      toLocallyNamelessWith (x :: names) body := by
  simpa [toLocallyNamelessWith,
    Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open'] using
    RawTm.open_toLocallyNamelessAux body.erase 0 names x

/-- Intrinsic capture-avoiding instantiation becomes upstream locally nameless opening. -/
@[simp]
theorem toLocallyNamelessWith_instantiate (names : List Nat)
    (body : Tm (A :: Γ) B) (a : Tm Γ A) :
    toLocallyNamelessWith names (Tm.instantiate body a) =
      Term.open'
        (RawTm.toLocallyNamelessAux 1 names body.erase)
        (toLocallyNamelessWith names a) := by
  change RawTm.toLocallyNamelessAux 0 names (Tm.instantiate body a).erase = _
  rw [Tm.erase_instantiate, ← RawTm.betaSub_zero]
  simpa [Term.open', toLocallyNamelessWith] using
    RawTm.toLocallyNamelessAux_betaSub body.erase a.erase 0 names

/-- Typing transport for the names-parameterized embedding. -/
theorem toLocallyNamelessWith_typing (t : Tm Γ A) {names : List Nat}
    (hlen : names.length = Γ.length) (hnames : names.Nodup) :
    Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing
      (locallyNamelessContextWith names Γ)
      (toLocallyNamelessWith names t) (Ty.toLocallyNameless A) := by
  induction t generalizing names with
  | var x =>
      exact .var (locallyNamelessContextWith_wellFormed hlen hnames)
        (x.mem_locallyNamelessContextWith hlen)
  | app f a ihf iha =>
      exact .app (ihf hlen hnames) (iha hlen hnames)
  | @lam A B Γ body ih =>
      apply Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing.abs names.toFinset
      intro x hx
      rw [open_toLocallyNamelessWith_lam]
      have hbody := ih (names := x :: names) (by simp [hlen])
        (List.nodup_cons.mpr ⟨by simpa using hx, hnames⟩)
      simpa [locallyNamelessContextWith] using hbody

/-- The canonical upstream context uses the free names `0, …, Γ.length - 1`. -/
def locallyNamelessContext (Γ : List (Ty Base)) : LocallyNamelessContext Base :=
  locallyNamelessContextWith (List.range Γ.length) Γ

/-- Canonical locally nameless embedding of an intrinsic term. -/
def toLocallyNameless (t : Tm Γ A) : LocallyNamelessTerm :=
  toLocallyNamelessWith (List.range Γ.length) t

/-- Canonical-context form of `toLocallyNamelessWith_instantiate`. -/
@[simp]
theorem toLocallyNameless_instantiate (body : Tm (A :: Γ) B) (a : Tm Γ A) :
    (Tm.instantiate body a).toLocallyNameless =
      Term.open'
        (RawTm.toLocallyNamelessAux 1 (List.range Γ.length) body.erase)
        a.toLocallyNameless :=
  toLocallyNamelessWith_instantiate (List.range Γ.length) body a

/-- Every intrinsic term is well typed after canonical locally nameless embedding. -/
theorem toLocallyNameless_typing (t : Tm Γ A) :
    Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing
      (locallyNamelessContext Γ) t.toLocallyNameless (Ty.toLocallyNameless A) := by
  apply toLocallyNamelessWith_typing
  · simp
  · exact List.nodup_range

/-- Every canonical embedding is locally closed, including embeddings of open intrinsic terms. -/
theorem toLocallyNameless_lc (t : Tm Γ A) : t.toLocallyNameless.LC :=
  t.toLocallyNameless_typing.lc

end Tm

end Cslib.Languages.LambdaCalculus.Stlc
