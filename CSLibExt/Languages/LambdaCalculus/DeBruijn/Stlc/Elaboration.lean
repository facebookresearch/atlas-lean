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

/-- **Raw lambda terms.** Raw terms are extrinsic de Bruijn syntax over a given type of base
types: a raw term is either a variable given by a natural-number index $n$, an application
$f\,a$ of two raw terms $f$ and $a$, or a lambda abstraction $\lambda A.\,t$ consisting of a
simple type $A$ over the base types (the parameter type) and a raw term $t$ (the body).
Variables and applications carry no type information. -/
inductive RawTm (Base : Type u) where
  | var : Nat → RawTm Base
  | app : RawTm Base → RawTm Base → RawTm Base
  | lam : Ty Base → RawTm Base → RawTm Base
  deriving DecidableEq, Repr

namespace RawTm

/-- **Size of a raw term.** Writing $|t|$ for the size of a raw term $t$, the size counts the
syntax nodes of $t$: a variable has size $1$, an application $f\,a$ has size $|f| + |a| + 1$,
and a lambda abstraction $\lambda A.\,t$ has size $|t| + 1$, so the type annotation $A$ is
not counted. -/
def size : RawTm Base → Nat
  | .var _ => 1
  | .app f a => f.size + a.size + 1
  | .lam _ body => body.size + 1

/-- **Shifting raw terms.** For natural numbers $k$ (the amount) and $c$ (the cutoff, $0$ by
default), shifting a raw term by $k$ at cutoff $c$ replaces a variable index $n$ by $n + k$ if
$c \le n$ and leaves it unchanged otherwise, shifts both sides of an application by $k$ at
cutoff $c$, and sends $\lambda A.\,t$ to $\lambda A.\,t'$, where $t'$ is $t$ shifted by $k$ at
cutoff $c + 1$. -/
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

/-- **Variable lookup.** Given a context $\Gamma$, a list of types, and a natural number $n$,
looking up the de Bruijn index $n$ in $\Gamma$ either fails or returns a type $A$ together with
an intrinsic variable of type $A$ in $\Gamma$. It is defined by recursion: lookup fails in the
empty context; index $0$ in the context $A :: \Gamma$, obtained by adding $A$ at the front of
$\Gamma$, returns $A$ with the zero variable; and index $n + 1$ in $B :: \Gamma$ looks up $n$ in
$\Gamma$, fails if that fails, and otherwise returns the same type with the successor of the
variable found. -/
def lookupVar : (Γ : List (Ty Base)) → Nat →
    Option (Sigma fun A => Var Γ A)
  | [], _ => none
  | A :: _, 0 => some ⟨A, .zero⟩
  | _ :: Γ, n + 1 => do
      let ⟨A, x⟩ ← lookupVar Γ n
      pure ⟨A, .succ x⟩

@[simp] theorem lookupVar_zero (A : Ty Base) (Γ : List (Ty Base)) :
    lookupVar (A :: Γ) 0 = some ⟨A, .zero⟩ := rfl

/-- **Index of a typed variable.** For a context $\Gamma$ and a type $A$, a well-typed de Bruijn
variable of type $A$ in $\Gamma$ is sent to its natural-number index, forgetting its type: the
variable for the first entry of the context has index $0$, and the successor of a variable $x$
has the index of $x$ plus $1$. -/
def Var.toNat {Base : Type u} {Γ : List (Ty Base)} {A : Ty Base} : Var Γ A → Nat
  | .zero => 0
  | .succ x => x.toNat + 1

/-- **Lookup recovers an intrinsic variable from its index.** For every context $\Gamma$, type
$A$ and intrinsic variable $x$ of type $A$ in $\Gamma$, looking up the de Bruijn index of $x$ in
$\Gamma$ succeeds and returns the type $A$ together with $x$. -/
@[simp] theorem lookupVar_toNat {Base : Type u} {Γ : List (Ty Base)} {A : Ty Base}
    (x : Var Γ A) :
    lookupVar Γ x.toNat = some ⟨A, x⟩ := by
  induction x with
  | zero => rfl
  | succ x ih => simp [Var.toNat, lookupVar, ih]

/-- **Lookup returns a variable with the queried index.** For every context $\Gamma$ and
natural number $n$, if looking up the de Bruijn index $n$ in $\Gamma$ succeeds with a type $A$
and an intrinsic variable $x$ of type $A$ in $\Gamma$, then the de Bruijn index of $x$ is $n$. -/
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

/-- **Erasure of intrinsically typed terms.** The erasure of an intrinsically typed term in a
context $\Gamma$ is the raw term defined by recursion: a variable becomes the raw variable whose
index is its position in $\Gamma$ (counting from $0$ at the front); an application of $f$ to $a$
becomes the raw application of the erasure of $f$ to the erasure of $a$; and a lambda with
parameter type $B$ becomes the raw lambda annotated with $B$ whose body is the erasure of its
body. Erasure thus forgets all typing information except the binder annotations. -/
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

/-- **Checked terms.** For a context $\Gamma$ of simple types, a checked term in $\Gamma$ is a pair
$(A, t)$ of a simple type $A$ and an intrinsically typed term $t$ of type $A$ in $\Gamma$.

A successful elaboration returns such a pair: the inferred type together with an intrinsic
term at that type. -/
abbrev Checked (Base : Type u) (Γ : List (Ty Base)) :=
  Sigma fun A => Tm Γ A

/-- **Elaboration of raw STLC terms.** Assume equality of base types is decidable. Elaboration in
a context $\Gamma$ of simple types sends a raw term either to failure or to a checked term in
$\Gamma$ (a simple type together with an intrinsically typed term of that type in $\Gamma$), by
recursion on the raw term. A variable with de Bruijn index $n$ elaborates to the variable at
position $n$ of $\Gamma$ (counting from $0$ at the front), with the type stored there, and fails
if $\Gamma$ has at most $n$ entries. A lambda with parameter type $A$ and body $b$ elaborates $b$
in $\Gamma$ extended by $A$ at the front; if that gives type $B$, it returns the lambda at type
$A \to B$, and otherwise it fails. An application of $f$ to $a$ elaborates $f$ and $a$ in
$\Gamma$, and succeeds, returning the application at type $B$, exactly when $f$ gets a function
type $A \to B$ and $a$ gets type $A$; otherwise it fails. -/
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

/-- **Elaboration inverts erasure.** Assume equality of base types is decidable. For every
intrinsically typed term $t$ of type $A$ in context $\Gamma$, elaborating the erasure of $t$ in
$\Gamma$ succeeds and returns exactly the pair $(A, t)$. In other words, erasure is a section of
elaboration. -/
@[simp] theorem elaborate_erase [DecidableEq Base] (t : Tm Γ A) :
    elaborate (Base := Base) Γ t.erase = some ⟨A, t⟩ := by
  induction t with
  | var x => simp [Tm.erase, elaborate, lookupVar_toNat]
  | app f a ihf iha => simp [Tm.erase, elaborate, ihf, iha]
  | @lam A B Γ body ih => simp [Tm.erase, elaborate, ih]

/-- **Elaboration preserves the input syntax.** Assume equality of base types is decidable. If
elaborating a raw term $r$ in context $\Gamma$ succeeds with type $A$ and intrinsically typed
term $t$, then the erasure of $t$ is exactly $r$. -/
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

/-- **Erasure is injective.** For a fixed context $\Gamma$ and type $A$, erasure is injective on
intrinsically typed terms of type $A$ in $\Gamma$: two such terms with the same erasure are
equal. -/
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

/-- **Declarative typing of raw terms.** For a context $\Gamma$ (a list of simple types), a
raw term $t$ and a type $A$, the judgment $\Gamma \vdash t : A$ is the least relation closed
under three rules. A variable with de Bruijn index $n$ has type $A$ in $\Gamma$ whenever looking
up $n$ in $\Gamma$ succeeds with the type $A$ and some intrinsic variable of type $A$. If
$\Gamma \vdash f : A \Rightarrow B$ and $\Gamma \vdash a : A$, then the application $f\,a$ has
type $B$ in $\Gamma$. If $A :: \Gamma \vdash b : B$, where $A :: \Gamma$ is $\Gamma$ with $A$
added at the front, then the abstraction $\lambda{:}A.\,b$ with parameter type $A$ has type
$A \Rightarrow B$ in $\Gamma$. -/
inductive HasType : (Γ : List (Ty Base)) → RawTm Base → Ty Base → Prop where
  | var {Γ : List (Ty Base)} {A : Ty Base} {n : Nat} {x : Var Γ A}
      (h : lookupVar Γ n = some ⟨A, x⟩) : HasType Γ (.var n) A
  | app {Γ : List (Ty Base)} {A B : Ty Base} {f a : RawTm Base} :
      HasType Γ f (A ⇒ B) → HasType Γ a A → HasType Γ (.app f a) B
  | lam {Γ : List (Ty Base)} {A B : Ty Base} {body : RawTm Base} :
      HasType (A :: Γ) body B → HasType Γ (.lam A body) (A ⇒ B)

namespace HasType

/-- **Erasure preserves typing.** For every intrinsically typed term $t$ of type $A$ in context
$\Gamma$, the erasure of $t$ has type $A$ in $\Gamma$ under the declarative typing judgment for
raw terms. -/
theorem erase (t : Tm Γ A) : HasType Γ t.erase A := by
  induction t with
  | var x => exact .var (lookupVar_toNat x)
  | app f a ihf iha => exact .app ihf iha
  | lam body ih => exact .lam ih

/-- **Uniqueness of types for raw terms.** Let $\Gamma$ be a context of simple types and $r$ a
raw term. If $r$ has type $A$ in $\Gamma$ and $r$ has type $B$ in $\Gamma$ under the declarative
typing judgment for raw terms, then $A = B$. -/
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

/-- **Completeness of elaboration.** Assume equality of base types is decidable. If a raw term $r$
has type $A$ in context $\Gamma$ under the declarative typing judgment, then elaborating $r$ in
$\Gamma$ succeeds and returns the type $A$ together with some intrinsically typed term of type
$A$ in $\Gamma$. -/
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

/-- **Soundness of elaboration.** Assume equality of base types is decidable. If elaborating a raw
term $r$ in context $\Gamma$ succeeds with type $A$ (and some intrinsically typed term of type $A$
in $\Gamma$), then $r$ has type $A$ in $\Gamma$ under the declarative typing judgment. -/
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

/-- **Declarative typing agrees with elaboration.** Assume equality of base types is decidable.
For every context $\Gamma$, raw term $t$ and type $A$, the declarative typing judgment
$\Gamma \vdash t : A$ holds if and only if there is an intrinsically typed term $u$ of type $A$
in context $\Gamma$ such that elaborating $t$ in $\Gamma$ succeeds and returns the type $A$
together with $u$. -/
theorem iff_elaborates [DecidableEq Base] {raw : RawTm Base} :
    HasType Γ raw A ↔ ∃ t : Tm Γ A, elaborate Γ raw = some ⟨A, t⟩ := by
  constructor
  · exact elaborate_complete
  · rintro ⟨t, ht⟩
    exact elaborate_sound ht

end HasType

/-- **Type inference for raw terms.** Assume equality of base types is decidable. Given a
context $\Gamma$ and a raw term $t$, type inference elaborates $t$ in $\Gamma$; if elaboration
succeeds, it returns the type component of the result and forgets the intrinsically typed term,
and if elaboration fails, inference fails. -/
def infer [DecidableEq Base] (Γ : List (Ty Base)) (raw : RawTm Base) :
    Option (Ty Base) :=
  (elaborate Γ raw).map Sigma.fst

@[simp] theorem infer_erase [DecidableEq Base] (t : Tm Γ A) :
    infer (Base := Base) Γ t.erase = some A := by
  simp [infer]

/-- **Type inference is sound and complete.** Assume equality of base types is decidable. For
every context $\Gamma$, raw term $t$ and type $A$, type inference for $t$ in $\Gamma$ returns
$A$ if and only if the declarative typing judgment $\Gamma \vdash t : A$ holds. -/
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

/-- **Type checking for raw STLC terms.** Assume equality of base types is decidable. Given a
context $\Gamma$ (a list of simple types), a raw term $r$ and a simple type $A$, the type checker
returns true exactly when type inference for $r$ in $\Gamma$ returns the type $A$, and false
otherwise. -/
def check [DecidableEq Base] (Γ : List (Ty Base))
    (raw : RawTm Base) (A : Ty Base) : Bool :=
  infer Γ raw == some A

@[simp] theorem check_eq_true_iff [DecidableEq Base] {raw : RawTm Base} :
    check Γ raw A = true ↔ HasType Γ raw A := by
  simp [check, infer_eq_some_iff]

@[simp] theorem check_erase [DecidableEq Base] (t : Tm Γ A) :
    check (Base := Base) Γ t.erase A = true := by
  exact check_eq_true_iff.mpr (HasType.erase t)

/-- **Normalization of raw terms.** Let the base types have decidable equality. Given a context
$\Gamma$ of simple types and a raw term $r$, raw normalization elaborates $r$ in $\Gamma$. If
elaboration fails, raw normalization fails. If elaboration returns a type $A$ and an
intrinsically typed term $t$ of type $A$, raw normalization returns $A$ together with the
erasure to a raw term of the normal form of $t$ computed by normalization by evaluation. -/
def normalizeRaw [DecidableEq Base] (Γ : List (Ty Base))
    (raw : RawTm Base) : Option (Sigma fun _ : Ty Base => RawTm Base) := do
  let ⟨A, t⟩ ← elaborate Γ raw
  pure ⟨A, (normalizeTm t).erase⟩

/-- **Raw normalization of an erased term.** Assume equality of base types is decidable. For
every intrinsically typed term $t$ of type $A$ in context $\Gamma$, raw normalization of the
erasure of $t$ in $\Gamma$ succeeds and returns the type $A$ together with the erasure of the
normal form of $t$ computed by normalization by evaluation. -/
@[simp] theorem normalizeRaw_erase [DecidableEq Base] (t : Tm Γ A) :
    normalizeRaw (Base := Base) Γ t.erase = some ⟨A, (normalizeTm t).erase⟩ := by
  simp [normalizeRaw]

/-- **Raw normalization reports the inferred type.** Let the base types have decidable
equality, let $\Gamma$ be a context of simple types and let $r$ be a raw term. If normalizing
$r$ in $\Gamma$ succeeds and returns a type $A$ together with a raw term, then type inference
for $r$ in $\Gamma$ returns $A$. -/
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

/-- **Raw normalization produces well-typed terms.** Assume equality of base types is
decidable. For every context $\Gamma$ and raw term $t$, if raw normalization of $t$ in $\Gamma$
succeeds with a type $A$ and a raw term $t'$, then the declarative typing judgment
$\Gamma \vdash t' : A$ holds. -/
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

/-- **Raw normalization is idempotent.** Assume equality of base types is decidable. For every
context $\Gamma$ and raw term $t$, if raw normalization of $t$ in $\Gamma$ succeeds with a type
$A$ and a raw term $t'$, then raw normalization of $t'$ in $\Gamma$ succeeds with the same type
$A$ and the same term $t'$. -/
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
