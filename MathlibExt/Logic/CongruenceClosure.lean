/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.Basic

@[expose] public section


/-- Ground terms of an uninterpreted-function signature with one
binary function symbol and constants indexed by naturals. -/
inductive GTerm
  | const (c : ℕ) : GTerm
  | app (t s : GTerm) : GTerm

/-- Congruence closure of a set of ground equalities `E`: the
least congruence containing `E` (reflexive, symmetric,
transitive, and congruent for `app`). -/
inductive CongClosure (E : GTerm → GTerm → Prop) :
    GTerm → GTerm → Prop
  | hyp {t s : GTerm} (h : E t s) : CongClosure E t s
  | refl (t : GTerm) : CongClosure E t t
  | symm {t s : GTerm} (h : CongClosure E t s) : CongClosure E s t
  | trans {t s u : GTerm} (h₁ : CongClosure E t s)
      (h₂ : CongClosure E s u) : CongClosure E t u
  | congr {t₁ t₂ s₁ s₂ : GTerm} (h₁ : CongClosure E t₁ t₂)
      (h₂ : CongClosure E s₁ s₂) :
      CongClosure E (GTerm.app t₁ s₁) (GTerm.app t₂ s₂)

/-- Evaluation of a ground term in an interpretation: constants
interpreted by `f`, the function symbol by `op`. -/
def GTerm.eval {D : Type*} (f : ℕ → D) (op : D → D → D) : GTerm → D
  | .const c => f c
  | .app t s => op (t.eval f op) (s.eval f op)

/-- Soundness of congruence closure for EUF: if two terms are
related by the congruence closure of `E`, then they have the
same value in every interpretation that satisfies all the
equalities of `E`. Hence a disequality `t ≠ s` in the input is
decided correctly: `t` and `s` are equal in all models of `E`
iff they are in the closure (the `if` direction is this theorem;
completeness is `CongClosure` being by definition the least such
relation, cf. `CongClosure.least` below). -/
theorem congClosure_sound {E : GTerm → GTerm → Prop} {D : Type*}
    {f : ℕ → D} {op : D → D → D}
    (hE : ∀ t s, E t s → GTerm.eval f op t = GTerm.eval f op s)
    {t s : GTerm} (h : CongClosure E t s) :
    GTerm.eval f op t = GTerm.eval f op s := by
  induction h with
  | hyp h => exact hE _ _ h
  | refl _ => rfl
  | symm _ ih => exact Eq.symm ih
  | trans _ _ ih₁ ih₂ => exact Eq.trans ih₁ ih₂
  | congr _ _ ih₁ ih₂ => simp only [GTerm.eval, ih₁, ih₂]

/-- Leastness: every congruence relation (equivalence closed
under `app`-congruence) containing `E` contains the closure. -/
theorem congClosure_least {E : GTerm → GTerm → Prop}
    {R : GTerm → GTerm → Prop}
    (hhyp : ∀ t s, E t s → R t s)
    (hrefl : ∀ t, R t t)
    (hsymm : ∀ {t s}, R t s → R s t)
    (htrans : ∀ {t s u}, R t s → R s u → R t u)
    (hcongr : ∀ {t₁ t₂ s₁ s₂}, R t₁ t₂ → R s₁ s₂ →
      R (GTerm.app t₁ s₁) (GTerm.app t₂ s₂))
    {t s : GTerm} (h : CongClosure E t s) : R t s := by
  induction h with
  | hyp h => exact hhyp _ _ h
  | refl t => exact hrefl t
  | symm _ ih => exact hsymm ih
  | trans _ _ ih₁ ih₂ => exact htrans ih₁ ih₂
  | congr _ _ ih₁ ih₂ => exact hcongr ih₁ ih₂
