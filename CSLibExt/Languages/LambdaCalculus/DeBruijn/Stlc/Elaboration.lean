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

/-
# Certified elaboration for raw STLC terms
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.NbeCanonical

/-!
# Certified elaboration for raw simply typed lambda terms

This module connects an ordinary, extrinsic de Bruijn surface language to the
intrinsically typed STLC developed in this directory.  Lambda binders carry
the one annotation needed for syntax-directed checking.  The elaborator
returns an intrinsic term together with its inferred type, so successful
elaboration is a typing certificate by construction.

The construction follows the bidirectional, syntax-directed presentation of
simply typed lambda calculus in Pierce, *Types and Programming Languages*,
Chapter 9, adapted to de Bruijn indices and this repository's intrinsic core.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

variable {Base : Type u}
variable {A B C : Ty Base}
variable {Γ Δ Ξ : List (Ty Base)}

/-- Extrinsic de Bruijn syntax.  A lambda records its parameter type, while
variables and applications carry no type information. -/
inductive RawTm (Base : Type u) where
  | var : Nat → RawTm Base
  | app : RawTm Base → RawTm Base → RawTm Base
  | lam : Ty Base → RawTm Base → RawTm Base
  deriving DecidableEq, Repr

namespace RawTm

/-- Number of syntax nodes in a raw term. -/
def size : RawTm Base → Nat
  | .var _ => 1
  | .app f a => f.size + a.size + 1
  | .lam _ body => body.size + 1

/-- Shift variables at or above a cutoff. -/
def shift (amount : Nat) (cutoff : Nat := 0) : RawTm Base → RawTm Base
  | .var n => .var (if cutoff ≤ n then n + amount else n)
  | .app f a => .app (f.shift amount cutoff) (a.shift amount cutoff)
  | .lam A body => .lam A (body.shift amount (cutoff + 1))

@[simp] theorem size_pos (t : RawTm Base) : 0 < t.size := by
  cases t <;> simp [size]

@[simp] theorem shift_zero (t : RawTm Base) (cutoff : Nat) :
    t.shift 0 cutoff = t := by
  induction t generalizing cutoff with
  | var n => simp [shift]
  | app f a ihf iha => simp [shift, ihf, iha]
  | lam A body ih => simp [shift, ih]

end RawTm

/-- Recover an intrinsically typed variable from a raw de Bruijn index. -/
def lookupVar : (Γ : List (Ty Base)) → Nat →
    Option (Sigma fun A => Var Γ A)
  | [], _ => none
  | A :: _, 0 => some ⟨A, .zero⟩
  | _ :: Γ, n + 1 => do
      let ⟨A, x⟩ ← lookupVar Γ n
      pure ⟨A, .succ x⟩

@[simp] theorem lookupVar_zero (A : Ty Base) (Γ : List (Ty Base)) :
    lookupVar (A :: Γ) 0 = some ⟨A, .zero⟩ := rfl

/-- Forget the type index of an intrinsic variable. -/
def Var.toNat {Base : Type u} {Γ : List (Ty Base)} {A : Ty Base} : Var Γ A → Nat
  | .zero => 0
  | .succ x => x.toNat + 1

/-- Looking up the erased index of an intrinsic variable recovers it exactly. -/
@[simp] theorem lookupVar_toNat {Base : Type u} {Γ : List (Ty Base)} {A : Ty Base}
    (x : Var Γ A) :
    lookupVar Γ x.toNat = some ⟨A, x⟩ := by
  induction x with
  | zero => rfl
  | succ x ih => simp [Var.toNat, lookupVar, ih]

/-- A successful lookup returns a variable whose erased index is precisely the
queried index. -/
theorem lookupVar_result_toNat {Base : Type u} {Γ : List (Ty Base)}
    {n : Nat} {result : Sigma fun A => Var Γ A}
    (h : lookupVar Γ n = some result) : result.2.toNat = n := by
  induction Γ generalizing n with
  | nil => simp [lookupVar] at h
  | cons B Γ ih =>
      cases n with
      | zero =>
          simp [lookupVar] at h
          cases h
          rfl
      | succ n =>
          cases hv : lookupVar Γ n with
          | none => simp [lookupVar, hv] at h
          | some previous =>
              simp [lookupVar, hv] at h
              cases h
              simpa [Var.toNat] using congrArg Nat.succ (ih hv)

theorem lookupVar_some_toNat {Base : Type u} {Γ : List (Ty Base)}
    {n : Nat} {A : Ty Base} {x : Var Γ A}
    (h : lookupVar Γ n = some ⟨A, x⟩) : x.toNat = n :=
  lookupVar_result_toNat h

/-- Erase intrinsic typing information while retaining binder annotations. -/
def Tm.erase {Base : Type u} {Γ : List (Ty Base)} {A : Ty Base} :
    Tm Γ A → RawTm Base
  | .var x => .var x.toNat
  | .app f a => .app f.erase a.erase
  | .lam (A := A) body => .lam A body.erase

@[simp] theorem Tm.erase_var (x : Var Γ A) :
    (Tm.var x).erase = (RawTm.var x.toNat : RawTm Base) := rfl

@[simp] theorem Tm.erase_app (f : Tm Γ (A ⇒ B)) (a : Tm Γ A) :
    (Tm.app f a).erase = (RawTm.app f.erase a.erase : RawTm Base) := rfl

@[simp] theorem Tm.erase_lam (body : Tm (A :: Γ) B) :
    (Tm.lam body).erase = (RawTm.lam A body.erase : RawTm Base) := rfl

/-- A successful elaboration result packages the inferred type with an
intrinsic term at that type. -/
abbrev Checked (Base : Type u) (Γ : List (Ty Base)) :=
  Sigma fun A => Tm Γ A

/-- Syntax-directed elaboration from raw terms to intrinsically typed terms. -/
def elaborate [DecidableEq Base] (Γ : List (Ty Base)) :
    RawTm Base → Option (Checked Base Γ)
  | .var n => lookupVar Γ n
      |>.map fun ⟨A, x⟩ => ⟨A, .var x⟩
  | .lam A body => do
      let ⟨B, body'⟩ ← elaborate (A :: Γ) body
      pure ⟨A ⇒ B, .lam body'⟩
  | .app f a => do
      let ⟨F, f'⟩ ← elaborate Γ f
      match F, f' with
      | .base _, _ => none
      | A ⇒ B, f' =>
        let ⟨A', a'⟩ ← elaborate Γ a
        if h : A' = A then
          pure ⟨B, .app f' (h ▸ a')⟩
        else none

/-- Erasure is a section of elaboration: every intrinsic term elaborates back
to the same type and term. -/
@[simp] theorem elaborate_erase [DecidableEq Base] (t : Tm Γ A) :
    elaborate (Base := Base) Γ t.erase = some ⟨A, t⟩ := by
  induction t with
  | var x => simp [Tm.erase, elaborate, lookupVar_toNat]
  | app f a ihf iha => simp [Tm.erase, elaborate, ihf, iha]
  | @lam A B Γ body ih => simp [Tm.erase, elaborate, ih]

/-- Successful elaboration preserves the complete input syntax: erasing the
returned intrinsic certificate recovers the raw term exactly. -/
theorem elaborate_faithful [DecidableEq Base] {raw : RawTm Base}
    {t : Tm Γ A} (h : elaborate Γ raw = some ⟨A, t⟩) :
    t.erase = raw := by
  induction raw generalizing Γ A with
  | var n =>
      cases hv : lookupVar Γ n with
      | none => simp [elaborate, hv] at h
      | some result =>
          obtain ⟨B, x⟩ := result
          have hs : (some ⟨B, Tm.var x⟩ : Option (Checked Base Γ)) =
              some ⟨A, t⟩ := by simpa [elaborate, hv] using h
          cases Option.some.inj hs
          simp [Tm.erase, lookupVar_some_toNat hv]
  | lam B body ih =>
      cases hb : elaborate (B :: Γ) body with
      | none => simp [elaborate, hb] at h
      | some result =>
          obtain ⟨C, body'⟩ := result
          have hs : (some ⟨B ⇒ C, Tm.lam body'⟩ : Option (Checked Base Γ)) =
              some ⟨A, t⟩ := by simpa [elaborate, hb] using h
          cases Option.some.inj hs
          simp [Tm.erase, ih hb]
  | app f a ihf iha =>
      cases hf : elaborate Γ f with
      | none => simp [elaborate, hf] at h
      | some result =>
          obtain ⟨F, f'⟩ := result
          cases F with
          | base b => simp [elaborate, hf] at h
          | arr B C =>
              cases ha : elaborate Γ a with
              | none => simp [elaborate, hf, ha] at h
              | some result =>
                  obtain ⟨B', a'⟩ := result
                  by_cases heq : B' = B
                  · subst B'
                    have hs :
                        (some ⟨C, Tm.app f' a'⟩ : Option (Checked Base Γ)) =
                          some ⟨A, t⟩ := by
                      simpa [elaborate, hf, ha] using h
                    cases Option.some.inj hs
                    simp [Tm.erase, ihf hf, iha ha]
                  · simp [elaborate, hf, ha, heq] at h

/-- Erasure is injective on intrinsic terms of a fixed type and context. -/
theorem Tm.erase_injective :
    Function.Injective (@Tm.erase Base Γ A) := by
  classical
  intro t u h
  have h' :
      (some ⟨A, t⟩ : Option (Checked Base Γ)) = some ⟨A, u⟩ := by
    simpa only [elaborate_erase] using
      congrArg (elaborate (Base := Base) Γ) h
  cases Option.some.inj h'
  rfl

/-- A declarative typing judgment for raw terms. -/
inductive HasType : (Γ : List (Ty Base)) → RawTm Base → Ty Base → Prop where
  | var {Γ : List (Ty Base)} {A : Ty Base} {n : Nat} {x : Var Γ A}
      (h : lookupVar Γ n = some ⟨A, x⟩) : HasType Γ (.var n) A
  | app {Γ : List (Ty Base)} {A B : Ty Base} {f a : RawTm Base} :
      HasType Γ f (A ⇒ B) → HasType Γ a A → HasType Γ (.app f a) B
  | lam {Γ : List (Ty Base)} {A B : Ty Base} {body : RawTm Base} :
      HasType (A :: Γ) body B → HasType Γ (.lam A body) (A ⇒ B)

namespace HasType

/-- Every intrinsic term erases to a well-typed raw term. -/
theorem erase (t : Tm Γ A) : HasType Γ t.erase A := by
  induction t with
  | var x => exact .var (lookupVar_toNat x)
  | app f a ihf iha => exact .app ihf iha
  | lam body ih => exact .lam ih

/-- Typing is deterministic. -/
theorem unique {raw : RawTm Base} (hA : HasType Γ raw A)
    (hB : HasType Γ raw B) : A = B := by
  induction hA generalizing B with
  | @var Γ A n x hx =>
      cases hB with
      | @var _ B _ y hy =>
        rw [hx] at hy
        cases hy
        rfl
  | app hf ha ihf iha =>
      cases hB with
      | app hg hb =>
        have hfun := ihf hg
        cases hfun
        rfl
  | lam h ih =>
      cases hB with
      | lam h' =>
        exact congrArg (Ty.arr _) (ih h')

/-- Every declarative typing derivation is accepted by the elaborator. -/
theorem elaborate_complete [DecidableEq Base] {raw : RawTm Base}
    (h : HasType Γ raw A) :
    ∃ t : Tm Γ A, elaborate Γ raw = some ⟨A, t⟩ := by
  induction h with
  | @var Γ A n x hx =>
      refine ⟨.var x, ?_⟩
      simp [elaborate, hx]
  | @app Γ A B f a hf ha ihf iha =>
      obtain ⟨f', hf'⟩ := ihf
      obtain ⟨a', ha'⟩ := iha
      refine ⟨.app f' a', ?_⟩
      simp [elaborate, hf', ha']
  | @lam Γ A B body hbody ih =>
      obtain ⟨body', hb⟩ := ih
      refine ⟨.lam body', ?_⟩
      simp [elaborate, hb]

/-- Successful elaboration implies the declarative typing judgment. -/
theorem elaborate_sound [DecidableEq Base] {raw : RawTm Base} {t : Tm Γ A}
    (h : elaborate Γ raw = some ⟨A, t⟩) : HasType Γ raw A := by
  induction raw generalizing Γ A with
  | var n =>
      simp only [elaborate] at h
      cases hv : lookupVar Γ n with
      | none => simp [hv] at h
      | some result =>
          obtain ⟨B, x⟩ := result
          have hs : (some ⟨B, Tm.var x⟩ : Option (Checked Base Γ)) =
              some ⟨A, t⟩ := by simpa [hv] using h
          have hBA := congrArg Sigma.fst (Option.some.inj hs)
          change B = A at hBA
          subst A
          exact .var hv
  | lam B body ih =>
      simp only [elaborate] at h
      cases hb : elaborate (B :: Γ) body with
      | none => simp [hb] at h
      | some result =>
          obtain ⟨C, body'⟩ := result
          have hs : (some ⟨B ⇒ C, Tm.lam body'⟩ : Option (Checked Base Γ)) =
              some ⟨A, t⟩ := by simpa [hb] using h
          have hty := congrArg Sigma.fst (Option.some.inj hs)
          change (B ⇒ C) = A at hty
          subst A
          exact .lam (ih hb)
  | app f a ihf iha =>
      simp only [elaborate] at h
      cases hf : elaborate Γ f with
      | none => simp [hf] at h
      | some result =>
          obtain ⟨F, f'⟩ := result
          cases F with
          | base b => simp [hf] at h
          | arr B C =>
              cases ha : elaborate Γ a with
              | none => simp [hf, ha] at h
              | some result =>
                  obtain ⟨B', a'⟩ := result
                  by_cases heq : B' = B
                  · subst B'
                    have hs : (some ⟨C, Tm.app f' a'⟩ : Option (Checked Base Γ)) =
                        some ⟨A, t⟩ := by simpa [hf, ha] using h
                    have hty := congrArg Sigma.fst (Option.some.inj hs)
                    change C = A at hty
                    subst A
                    exact .app (ihf hf) (iha ha)
                  · simp [hf, ha, heq] at h

/-- The algorithmic and declarative presentations of typing coincide. -/
theorem iff_elaborates [DecidableEq Base] {raw : RawTm Base} :
    HasType Γ raw A ↔ ∃ t : Tm Γ A, elaborate Γ raw = some ⟨A, t⟩ := by
  constructor
  · exact elaborate_complete
  · rintro ⟨t, ht⟩
    exact elaborate_sound ht

end HasType

/-- Infer only the type of a raw term. -/
def infer [DecidableEq Base] (Γ : List (Ty Base)) (raw : RawTm Base) :
    Option (Ty Base) :=
  (elaborate Γ raw).map Sigma.fst

@[simp] theorem infer_erase [DecidableEq Base] (t : Tm Γ A) :
    infer (Base := Base) Γ t.erase = some A := by
  simp [infer]

/-- Type inference succeeds exactly at declaratively typable terms. -/
theorem infer_eq_some_iff [DecidableEq Base] {raw : RawTm Base} :
    infer Γ raw = some A ↔ HasType Γ raw A := by
  constructor
  · intro h
    unfold infer at h
    cases he : elaborate Γ raw with
    | none => simp [he] at h
    | some result =>
        obtain ⟨B, t⟩ := result
        simp [he] at h
        subst B
        exact HasType.elaborate_sound he
  · intro h
    obtain ⟨t, ht⟩ := HasType.elaborate_complete h
    simp [infer, ht]

/-- Decidable type checking, derived from certified inference. -/
def check [DecidableEq Base] (Γ : List (Ty Base))
    (raw : RawTm Base) (A : Ty Base) : Bool :=
  infer Γ raw == some A

@[simp] theorem check_eq_true_iff [DecidableEq Base] {raw : RawTm Base} :
    check Γ raw A = true ↔ HasType Γ raw A := by
  simp [check, infer_eq_some_iff]

@[simp] theorem check_erase [DecidableEq Base] (t : Tm Γ A) :
    check (Base := Base) Γ t.erase A = true := by
  exact check_eq_true_iff.mpr (HasType.erase t)

/-- Elaborate and normalize a raw term, retaining its inferred type. -/
def normalizeRaw [DecidableEq Base] (Γ : List (Ty Base))
    (raw : RawTm Base) : Option (Sigma fun _ : Ty Base => RawTm Base) := do
  let ⟨A, t⟩ ← elaborate Γ raw
  pure ⟨A, (normalizeTm t).erase⟩

/-- On intrinsic inputs, raw normalization agrees with normalization by
evaluation followed by erasure. -/
@[simp] theorem normalizeRaw_erase [DecidableEq Base] (t : Tm Γ A) :
    normalizeRaw (Base := Base) Γ t.erase = some ⟨A, (normalizeTm t).erase⟩ := by
  simp [normalizeRaw]

/-- Normalizing a raw term does not change its inferred type. -/
theorem normalizeRaw_type [DecidableEq Base] {raw normalized : RawTm Base}
    (h : normalizeRaw Γ raw = some ⟨A, normalized⟩) :
    infer Γ raw = some A := by
  unfold normalizeRaw at h
  cases he : elaborate Γ raw with
  | none => simp [he] at h
  | some result =>
      obtain ⟨B, t⟩ := result
      simp [he] at h
      rcases h with ⟨rfl, rfl⟩
      simp [infer, he]

/-- The output of raw normalization remains well typed. -/
theorem normalizeRaw_hasType [DecidableEq Base] {raw normalized : RawTm Base}
    (h : normalizeRaw Γ raw = some ⟨A, normalized⟩) :
    HasType Γ normalized A := by
  unfold normalizeRaw at h
  cases he : elaborate Γ raw with
  | none => simp [he] at h
  | some result =>
      obtain ⟨B, t⟩ := result
      simp [he] at h
      rcases h with ⟨rfl, rfl⟩
      exact HasType.erase (normalizeTm t)

/-- Raw normalization is idempotent on successful results. -/
theorem normalizeRaw_idempotent [DecidableEq Base]
    {raw normalized : RawTm Base}
    (h : normalizeRaw Γ raw = some ⟨A, normalized⟩) :
    normalizeRaw Γ normalized = some ⟨A, normalized⟩ := by
  unfold normalizeRaw at h
  cases he : elaborate Γ raw with
  | none => simp [he] at h
  | some result =>
      obtain ⟨B, t⟩ := result
      simp [he] at h
      rcases h with ⟨rfl, rfl⟩
      simp [normalizeRaw]

end Cslib.Languages.LambdaCalculus.Stlc
