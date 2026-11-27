/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.CEK
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt

/-!
# Untyped de Bruijn terms as locally nameless terms

Untyped λ-terms with de Bruijn indices (`Cslib.Languages.LambdaCalculus.CEK.Tm`) and locally
nameless terms (`Cslib.LambdaCalculus.LocallyNameless.Untyped.Term`) over a type `Var` of names
with decidable equality: translations both ways in a naming context, the bijection between
well-scoped terms and locally closed terms whose free names lie in the context, and the
correspondence of β-substitution with opening (A. Charguéraud, *The locally nameless
representation*, Journal of Automated Reasoning 49(3), 2012, Sections 2.3, 2.4, 3.3 and 3.6).

A naming context is a list `names` whose head is the innermost free name: under `depth`
enclosing abstractions, the index `depth + j` denotes `names[j]`.

* `toLocallyNamelessAux depth names` sends an index below `depth` to a bound variable, the index
  `depth + j` with `j < names.length` to the free variable `names[j]`, and every larger index `i`
  to the dangling bound variable `bvar i`; `ofLocallyNamelessAux depth names` goes back, sending
  a free name `x` to the index `depth + names.idxOf x`.
* `scopedAt n t` says that every free index of `t` is below `n`. The translation of a term scoped
  at `names.length` is locally closed (`toLocallyNameless_lc`).
* `equivLocallyNameless`: for a context without repetitions, the two translations are inverse
  bijections between the terms scoped at `names.length` and the locally closed terms whose free
  names lie in `names`. `equivLocallyNamelessClosed` is the case of closed terms.
* `toLocallyNameless_instantiate`: β-substitution of de Bruijn terms (`instantiate`, with
  `shift`) becomes opening of locally nameless terms. `open_toLocallyNameless_lam`: opening with
  a free name extends the context by that name.

The statements about locally closed terms assume that every finite set of names misses some name
(`[HasFresh Var]`): over a finite type of names the cofinite rule of `LC` holds vacuously. The
translation generalizes the embedding of simply typed de Bruijn terms in
`CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.CslibEmbedding` to untyped terms over an
arbitrary type of names.
-/

public section

namespace Cslib.LambdaCalculus.DeBruijn.Untyped.LocallyNamelessBridge

open Cslib.Languages.LambdaCalculus.CEK (Tm)
open Cslib.LambdaCalculus.LocallyNameless.Untyped (Term)
open scoped Cslib.LambdaCalculus.LocallyNameless.Untyped.Term

universe u

/-! ### Scoping, shifting and β-substitution of de Bruijn terms -/

/-- **Well-scoped de Bruijn terms.** `scopedAt n t` holds when every free index of `t` is below
`n`: an index `i` under `k` abstractions of `t` is free when `k ≤ i`, and it must then satisfy
`i - k < n`. -/
@[expose] def scopedAt (n : ℕ) : Tm → Bool
  | .var i => i < n
  | .lam t => scopedAt (n + 1) t
  | .app t u => scopedAt n t && scopedAt n u

/-- **Shifting free indices.** `shift amount cutoff t` adds `amount` to every index of `t` that
is at least `cutoff` plus the number of abstractions of `t` around it. -/
@[expose] def shift (amount cutoff : ℕ) : Tm → Tm
  | .var i => if cutoff ≤ i then .var (i + amount) else .var i
  | .lam t => .lam (shift amount (cutoff + 1) t)
  | .app t u => .app (shift amount cutoff t) (shift amount cutoff u)

/-- **Substitution for one index.** `instantiateAt depth arg t` replaces the index `depth` of `t`,
counted from outside the abstractions of `t` around it, by `arg` shifted by `depth` and by those
abstractions, and lowers every larger index by one. -/
@[expose] def instantiateAt (depth : ℕ) (arg : Tm) : Tm → Tm
  | .var i => if i < depth then .var i else if i = depth then shift depth 0 arg else .var (i - 1)
  | .lam t => .lam (instantiateAt (depth + 1) arg t)
  | .app t u => .app (instantiateAt depth arg t) (instantiateAt depth arg u)

/-- **β-substitution.** `instantiate body arg` is the contractum of the redex `app (lam body) arg`:
the index `0` of `body` becomes `arg`, and every larger free index of `body` is lowered by one. -/
@[expose] def instantiate (body arg : Tm) : Tm := instantiateAt 0 arg body

/-! ### The two translations -/

/-- **De Bruijn terms as locally nameless terms, under binders.** `toLocallyNamelessAux depth
names t` translates `t` as if it stood under `depth` abstractions in the naming context `names`,
whose head is the innermost free name. An index `i < depth` becomes the bound variable `bvar i`,
an index `depth + j` with `j < names.length` becomes the free variable `fvar names[j]`, and every
larger index `i` becomes the dangling bound variable `bvar i`. Applications are translated
componentwise, and the body of an abstraction one binder deeper. -/
@[expose] def toLocallyNamelessAux {Var : Type u} [DecidableEq Var] (depth : ℕ)
    (names : List Var) : Tm → Term Var
  | .var i =>
    if i < depth then .bvar i
    else if h : i - depth < names.length then .fvar names[i - depth]
    else .bvar i
  | .lam t => .abs (toLocallyNamelessAux (depth + 1) names t)
  | .app t u => .app (toLocallyNamelessAux depth names t) (toLocallyNamelessAux depth names u)

/-- **De Bruijn terms as locally nameless terms.** `toLocallyNameless names t` translates `t` in
the naming context `names`, whose head is the innermost free name: the index `j` becomes
`fvar names[j]` when `j < names.length`. -/
@[expose] def toLocallyNameless {Var : Type u} [DecidableEq Var] (names : List Var) :
    Tm → Term Var :=
  toLocallyNamelessAux 0 names

/-- **Locally nameless terms as de Bruijn terms, under binders.** `ofLocallyNamelessAux depth
names M` translates `M` as if it stood under `depth` abstractions in the naming context `names`.
A bound variable `bvar i` becomes the index `i`, and a free name `x` becomes the index
`depth + names.idxOf x`, which is `depth + names.length` when `x` is not in `names`. Applications
are translated componentwise, and the body of an abstraction one binder deeper. -/
@[expose] def ofLocallyNamelessAux {Var : Type u} [DecidableEq Var] (depth : ℕ)
    (names : List Var) : Term Var → Tm
  | .bvar i => .var i
  | .fvar x => .var (depth + names.idxOf x)
  | .abs t => .lam (ofLocallyNamelessAux (depth + 1) names t)
  | .app t u => .app (ofLocallyNamelessAux depth names t) (ofLocallyNamelessAux depth names u)

/-- **Locally nameless terms as de Bruijn terms.** `ofLocallyNameless names M` translates `M` in
the naming context `names`: the free name `x` becomes the index `names.idxOf x`. -/
@[expose] def ofLocallyNameless {Var : Type u} [DecidableEq Var] (names : List Var) :
    Term Var → Tm :=
  ofLocallyNamelessAux 0 names

/-! ### The bijection -/

/-- **Free names of a translation.** Every free name of `toLocallyNamelessAux depth names t` lies
in `names`. -/
theorem mem_of_mem_fv_toLocallyNamelessAux {Var : Type u} [DecidableEq Var] {depth : ℕ}
    {names : List Var} {t : Tm} {x : Var} (hx : x ∈ (toLocallyNamelessAux depth names t).fv) :
    x ∈ names := by
  induction t generalizing depth with
  | var i =>
    simp only [toLocallyNamelessAux] at hx
    split_ifs at hx with h₁ h₂
    · simp at hx
    · simp only [Term.fv, Finset.mem_singleton] at hx
      subst hx
      exact List.getElem_mem h₂
    · simp at hx
  | lam t ih =>
    simp only [toLocallyNamelessAux, Term.fv] at hx
    exact ih hx
  | app t u iht ihu =>
    simp only [toLocallyNamelessAux, Term.fv, Finset.mem_union] at hx
    exact hx.elim iht ihu

/-- **Local closure of a translation.** The translation `toLocallyNamelessAux depth names t` is
locally closed at level `depth` exactly when `t` is scoped at `depth + names.length`. -/
theorem lcAt_toLocallyNamelessAux {Var : Type u} [DecidableEq Var] (depth : ℕ)
    (names : List Var) (t : Tm) :
    (toLocallyNamelessAux depth names t).LcAt depth = scopedAt (depth + names.length) t := by
  induction t generalizing depth with
  | var i =>
    simp only [toLocallyNamelessAux, scopedAt]
    split_ifs with h₁ h₂
    · simp only [Term.LcAt, decide_eq_decide]
      omega
    · simp only [Term.LcAt, Bool.true_eq, decide_eq_true_eq]
      omega
    · simp only [Term.LcAt, decide_eq_decide]
      omega
  | lam t ih =>
    simp only [toLocallyNamelessAux, scopedAt, Term.LcAt]
    rw [ih, Nat.add_right_comm]
  | app t u iht ihu =>
    simp only [toLocallyNamelessAux, scopedAt, Term.LcAt, iht, ihu]

/-- **Translating back gives a scoped term.** If `M` is locally closed at level `depth` and every
free name of `M` lies in `names`, then `ofLocallyNamelessAux depth names M` is scoped at
`depth + names.length`. -/
theorem scopedAt_ofLocallyNamelessAux {Var : Type u} [DecidableEq Var] {depth : ℕ}
    {names : List Var} {M : Term Var} (hM : M.LcAt depth) (hfv : ∀ x ∈ M.fv, x ∈ names) :
    scopedAt (depth + names.length) (ofLocallyNamelessAux depth names M) := by
  induction M generalizing depth with
  | bvar i =>
    simp only [Term.LcAt, decide_eq_true_eq] at hM
    simp only [ofLocallyNamelessAux, scopedAt, decide_eq_true_eq]
    omega
  | fvar x =>
    have hx : names.idxOf x < names.length :=
      List.idxOf_lt_length_iff.mpr (hfv x (by simp))
    simp only [ofLocallyNamelessAux, scopedAt, decide_eq_true_eq]
    omega
  | abs t ih =>
    simp only [Term.LcAt] at hM
    simp only [Term.fv] at hfv
    simp only [ofLocallyNamelessAux, scopedAt]
    rw [Nat.add_right_comm]
    exact ih hM hfv
  | app t u iht ihu =>
    simp only [Term.LcAt, Bool.and_eq_true] at hM
    simp only [Term.fv, Finset.mem_union] at hfv
    simp only [ofLocallyNamelessAux, scopedAt, Bool.and_eq_true]
    exact ⟨iht hM.1 fun x hx => hfv x (.inl hx), ihu hM.2 fun x hx => hfv x (.inr hx)⟩

/-- **The de Bruijn round trip, under binders.** If `names` has no repetition and `t` is scoped at
`depth + names.length`, then translating `t` to a locally nameless term and back gives `t`. -/
theorem ofLocallyNamelessAux_toLocallyNamelessAux {Var : Type u} [DecidableEq Var] {depth : ℕ}
    {names : List Var} {t : Tm} (hnodup : names.Nodup)
    (ht : scopedAt (depth + names.length) t) :
    ofLocallyNamelessAux depth names (toLocallyNamelessAux depth names t) = t := by
  induction t generalizing depth with
  | var i =>
    simp only [scopedAt, decide_eq_true_eq] at ht
    simp only [toLocallyNamelessAux]
    split_ifs with h₁ h₂
    · rfl
    · simp only [ofLocallyNamelessAux, hnodup.idxOf_getElem, Tm.var.injEq]
      omega
    · exact absurd ht (by omega)
  | lam t ih =>
    simp only [scopedAt] at ht
    simp only [toLocallyNamelessAux, ofLocallyNamelessAux]
    rw [ih (by rwa [Nat.add_right_comm])]
  | app t u iht ihu =>
    simp only [scopedAt, Bool.and_eq_true] at ht
    simp only [toLocallyNamelessAux, ofLocallyNamelessAux, iht ht.1, ihu ht.2]

/-- **The locally nameless round trip, under binders.** If `M` is locally closed at level `depth`
and every free name of `M` lies in `names`, then translating `M` to a de Bruijn term and back
gives `M`. -/
theorem toLocallyNamelessAux_ofLocallyNamelessAux {Var : Type u} [DecidableEq Var] {depth : ℕ}
    {names : List Var} {M : Term Var} (hM : M.LcAt depth) (hfv : ∀ x ∈ M.fv, x ∈ names) :
    toLocallyNamelessAux depth names (ofLocallyNamelessAux depth names M) = M := by
  induction M generalizing depth with
  | bvar i =>
    simp only [Term.LcAt, decide_eq_true_eq] at hM
    simp [ofLocallyNamelessAux, toLocallyNamelessAux, hM]
  | fvar x =>
    have hx : names.idxOf x < names.length :=
      List.idxOf_lt_length_iff.mpr (hfv x (by simp))
    simp [ofLocallyNamelessAux, toLocallyNamelessAux, hx]
  | abs t ih =>
    simp only [Term.LcAt] at hM
    simp only [Term.fv] at hfv
    simp only [ofLocallyNamelessAux, toLocallyNamelessAux, ih hM hfv]
  | app t u iht ihu =>
    simp only [Term.LcAt, Bool.and_eq_true] at hM
    simp only [Term.fv, Finset.mem_union] at hfv
    simp only [ofLocallyNamelessAux, toLocallyNamelessAux,
      iht hM.1 fun x hx => hfv x (.inl hx), ihu hM.2 fun x hx => hfv x (.inr hx)]

/-- **Local closure from the level check.** A term that is locally closed at level `0` is locally
closed. This direction needs no fresh name: the body of each abstraction is opened with every
name. -/
private theorem lc_of_lcAt_zero {Var : Type u} {M : Term Var} (h : M.LcAt 0) : M.LC := by
  induction M using Term.ind_on_depth with
  | bvar i => simp [Term.LcAt] at h
  | fvar x => exact .fvar x
  | app M N ihM ihN =>
    simp only [Term.LcAt, Bool.and_eq_true] at h
    exact .app (ihM h.1) (ihN h.2)
  | abs M _ ih =>
    refine .abs ∅ M fun x _ => ih (M ^ Term.fvar x) (Term.depth_open_fvar_eq_depth M x).le ?_
    rw [Term.lcAt_open_fvar_iff_lcAt]
    simpa [Term.LcAt] using h

/-- **Translations are locally closed.** If `t` is scoped at the length of `names`, the
translation `toLocallyNameless names t` is locally closed. No fresh name is needed. -/
theorem toLocallyNameless_lc {Var : Type u} [DecidableEq Var] {names : List Var} {t : Tm}
    (ht : scopedAt names.length t) : (toLocallyNameless names t).LC := by
  apply lc_of_lcAt_zero
  rw [toLocallyNameless, lcAt_toLocallyNamelessAux, Nat.zero_add]
  exact ht

/-- **The de Bruijn round trip.** If `names` has no repetition and `t` is scoped at the length of
`names`, then `ofLocallyNameless names (toLocallyNameless names t) = t`. -/
theorem ofLocallyNameless_toLocallyNameless {Var : Type u} [DecidableEq Var] {names : List Var}
    {t : Tm} (hnodup : names.Nodup) (ht : scopedAt names.length t) :
    ofLocallyNameless names (toLocallyNameless names t) = t := by
  apply ofLocallyNamelessAux_toLocallyNamelessAux hnodup
  rw [Nat.zero_add]
  exact ht

/-- **The locally nameless round trip.** Suppose every finite set of names misses some name
(`[HasFresh Var]`). If `M` is locally closed and every free name of `M` lies in `names`, then
`toLocallyNameless names (ofLocallyNameless names M) = M`. -/
theorem toLocallyNameless_ofLocallyNameless {Var : Type u} [DecidableEq Var] [HasFresh Var]
    {names : List Var} {M : Term Var} (hM : M.LC) (hfv : ∀ x ∈ M.fv, x ∈ names) :
    toLocallyNameless names (ofLocallyNameless names M) = M := by
  exact toLocallyNamelessAux_ofLocallyNamelessAux ((Term.lcAt_iff_LC M).mpr hM) hfv

/-- **The bijection.** Suppose every finite set of names misses some name (`[HasFresh Var]`) and
`names` has no repetition. Then `toLocallyNameless names` and `ofLocallyNameless names` are
inverse bijections between the de Bruijn terms scoped at the length of `names` and the locally
closed terms whose free names lie in `names`. -/
@[expose] def equivLocallyNameless {Var : Type u} [DecidableEq Var] [HasFresh Var]
    (names : List Var) (h : names.Nodup) :
    {t : Tm // scopedAt names.length t} ≃ {M : Term Var // M.LC ∧ ∀ x ∈ M.fv, x ∈ names} where
  toFun t := ⟨toLocallyNameless names t.1, toLocallyNameless_lc t.2,
    fun _ hx => mem_of_mem_fv_toLocallyNamelessAux hx⟩
  invFun M := ⟨ofLocallyNameless names M.1, by
    have := scopedAt_ofLocallyNamelessAux ((Term.lcAt_iff_LC M.1).mpr M.2.1) M.2.2
    rwa [Nat.zero_add] at this⟩
  left_inv t := Subtype.ext (ofLocallyNameless_toLocallyNameless h t.2)
  right_inv M := Subtype.ext (toLocallyNameless_ofLocallyNameless M.2.1 M.2.2)

/-- **The bijection for closed terms.** Suppose every finite set of names misses some name
(`[HasFresh Var]`). Then the translations in the empty context are inverse bijections between the
closed de Bruijn terms, those scoped at `0`, and the locally closed terms without free names. -/
@[expose] def equivLocallyNamelessClosed {Var : Type u} [DecidableEq Var] [HasFresh Var] :
    {t : Tm // scopedAt 0 t} ≃ {M : Term Var // M.LC ∧ M.fv = ∅} :=
  (equivLocallyNameless [] List.nodup_nil).trans
    (Equiv.subtypeEquivRight fun M => by simp [Finset.eq_empty_iff_forall_notMem])

/-! ### β-substitution and opening -/

/-- **Opening with a name extends the context.** Opening the translation of `t` one binder deeper
at index `depth` with the free name `x` is translating `t` with `x` added at the head of the
context. -/
theorem openRec_toLocallyNamelessAux {Var : Type u} [DecidableEq Var] (depth : ℕ) (x : Var)
    (names : List Var) (t : Tm) :
    Term.openRec depth (.fvar x) (toLocallyNamelessAux (depth + 1) names t) =
      toLocallyNamelessAux depth (x :: names) t := by
  induction t generalizing depth with
  | var i =>
    rcases Nat.lt_trichotomy i depth with h | rfl | h
    · simp [toLocallyNamelessAux, Term.openRec, h, show i < depth + 1 by omega,
        show depth ≠ i by omega]
    · simp [toLocallyNamelessAux, Term.openRec]
    · have e : i - depth = i - (depth + 1) + 1 := by omega
      by_cases h₁ : i - (depth + 1) < names.length
      · simp [toLocallyNamelessAux, Term.openRec, show ¬ i < depth by omega,
          show ¬ i < depth + 1 by omega, h₁, e]
      · simp [toLocallyNamelessAux, Term.openRec, show ¬ i < depth by omega,
          show ¬ i < depth + 1 by omega, h₁, e, show depth ≠ i by omega]
  | lam t ih => simp only [toLocallyNamelessAux, Term.openRec, ih]
  | app t u iht ihu => simp only [toLocallyNamelessAux, Term.openRec, iht, ihu]

/-- **Opening the body of an abstraction with a name.** Opening the translation of the body `b`
of an abstraction with the free name `x` is translating `b` with `x` added at the head of the
context. -/
theorem open_toLocallyNameless_lam {Var : Type u} [DecidableEq Var] (x : Var)
    (names : List Var) (b : Tm) :
    toLocallyNamelessAux 1 names b ^ Term.fvar x = toLocallyNameless (x :: names) b := by
  exact openRec_toLocallyNamelessAux 0 x names b

/-- **Shifting below the cutoff is invisible.** If `t` is scoped at `cutoff + names.length`, then
translating `shift amount cutoff t` under `amount + cutoff` binders gives the translation of `t`
under `cutoff` binders. -/
theorem toLocallyNamelessAux_shift {Var : Type u} [DecidableEq Var] (amount : ℕ) {cutoff : ℕ}
    {names : List Var} {t : Tm} (ht : scopedAt (cutoff + names.length) t) :
    toLocallyNamelessAux (amount + cutoff) names (shift amount cutoff t) =
      toLocallyNamelessAux cutoff names t := by
  induction t generalizing cutoff with
  | var i =>
    simp only [scopedAt, decide_eq_true_eq] at ht
    by_cases h₁ : cutoff ≤ i
    · have e : i + amount - (amount + cutoff) = i - cutoff := by omega
      simp [shift, toLocallyNamelessAux, h₁, e, show ¬ i + amount < amount + cutoff by omega,
        show ¬ i < cutoff by omega, show i - cutoff < names.length by omega]
    · simp [shift, toLocallyNamelessAux, h₁, show i < cutoff by omega,
        show i < amount + cutoff by omega]
  | lam t ih =>
    simp only [scopedAt] at ht
    simp only [shift, toLocallyNamelessAux]
    exact congrArg Term.abs (ih (by rwa [Nat.add_right_comm]))
  | app t u iht ihu =>
    simp only [scopedAt, Bool.and_eq_true] at ht
    simp only [shift, toLocallyNamelessAux, iht ht.1, ihu ht.2]

/-- **β-substitution at a depth is opening.** If `a` is scoped at the length of `names` and `b` is
scoped at `depth + 1 + names.length`, then translating `instantiateAt depth a b` under `depth`
binders is opening, at index `depth`, the translation of `b` one binder deeper with the
translation of `a`. -/
theorem toLocallyNamelessAux_instantiateAt {Var : Type u} [DecidableEq Var] {depth : ℕ}
    {names : List Var} {a b : Tm} (ha : scopedAt names.length a)
    (hb : scopedAt (depth + 1 + names.length) b) :
    toLocallyNamelessAux depth names (instantiateAt depth a b) =
      Term.openRec depth (toLocallyNameless names a)
        (toLocallyNamelessAux (depth + 1) names b) := by
  induction b generalizing depth with
  | var i =>
    simp only [scopedAt, decide_eq_true_eq] at hb
    rcases Nat.lt_trichotomy i depth with h | rfl | h
    · simp [instantiateAt, toLocallyNamelessAux, Term.openRec, h,
        show i < depth + 1 by omega, show depth ≠ i by omega]
    · have hs := toLocallyNamelessAux_shift (names := names) i (cutoff := 0) (t := a)
        (by rwa [Nat.zero_add])
      simp only [Nat.add_zero] at hs
      simp [instantiateAt, toLocallyNamelessAux, Term.openRec, hs, toLocallyNameless]
    · have e : i - 1 - depth = i - (depth + 1) := by omega
      simp [instantiateAt, toLocallyNamelessAux, Term.openRec, show ¬ i < depth by omega,
        show i ≠ depth by omega, show ¬ i - 1 < depth by omega, show ¬ i < depth + 1 by omega,
        show i - (depth + 1) < names.length by omega, e]
  | lam t ih =>
    simp only [scopedAt] at hb
    simp only [instantiateAt, toLocallyNamelessAux, Term.openRec]
    exact congrArg Term.abs (ih (by rwa [Nat.add_right_comm]))
  | app t u iht ihu =>
    simp only [scopedAt, Bool.and_eq_true] at hb
    simp only [instantiateAt, toLocallyNamelessAux, Term.openRec, iht hb.1, ihu hb.2]

/-- **β-substitution is opening.** If the body `b` is scoped at `names.length + 1` and the
argument `a` is scoped at the length of `names`, then translating the contractum
`instantiate b a` is opening the translation of `b`, one binder deep, with the translation of
`a`. -/
theorem toLocallyNameless_instantiate {Var : Type u} [DecidableEq Var] {names : List Var}
    {a b : Tm} (hb : scopedAt (names.length + 1) b) (ha : scopedAt names.length a) :
    toLocallyNameless names (instantiate b a) =
      toLocallyNamelessAux 1 names b ^ toLocallyNameless names a := by
  rw [Nat.add_comm] at hb
  exact toLocallyNamelessAux_instantiateAt ha (by rw [Nat.zero_add]; exact hb)

end Cslib.LambdaCalculus.DeBruijn.Untyped.LocallyNamelessBridge
