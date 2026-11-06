/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.SystemF.Model
public import CSLibExt.Languages.LambdaCalculus.SystemF.Syntax

/-!
# System F erasure and closing environments

Erase types into CSLib's existing locally nameless untyped calculus. The bound
index shift only adapts scoped simultaneous environments to that existing
syntax; no new untyped term, beta relation, or local-closure predicate is used.
Type lambdas and type applications erase completely.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.SystemF

open Cslib.LambdaCalculus.LocallyNameless.Untyped

/-- **Shift of untyped bound indices above a cutoff.**
Shift free bound indices in CSLib syntax, preserving indices below `c`. -/
def shiftAt (c : Nat) : Term Nat → Term Nat
  | .bvar i => .bvar (if i < c then i else i + 1)
  | .fvar x => .fvar x
  | .app f a => .app (shiftAt c f) (shiftAt c a)
  | .abs b => .abs (shiftAt (c + 1) b)

/-- **Lifting a raw erasure environment under a binder.**
Lift a raw erasure environment beneath one scoped term binder. -/
def liftRaw {m : Nat} (σ : Fin m → Term Nat) :
    Fin (m + 1) → Term Nat :=
  Fin.cases (.bvar 0) (fun i => shiftAt 0 (σ i))

private theorem shiftAt_lcAt {c k : Nat} (t : Term Nat) (h : t.LcAt k) :
    (shiftAt c t).LcAt (k + 1) := by
  induction t generalizing c k with
  | bvar i =>
    simp only [Term.LcAt, decide_eq_true_eq] at h
    simp only [shiftAt, Term.LcAt, decide_eq_true_eq]
    split_ifs
    · exact Nat.lt_succ_of_lt h
    · exact Nat.succ_lt_succ h
  | fvar => rfl
  | app f a ihf iha =>
    simp only [shiftAt, Term.LcAt, Bool.and_eq_true] at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | abs b ih => exact ih h

private theorem shiftAt_eq_self {c : Nat} (t : Term Nat) (h : t.LcAt c) :
    shiftAt c t = t := by
  induction t generalizing c with
  | bvar i =>
    have hi : i < c := by simpa only [Term.LcAt, decide_eq_true_eq] using h
    simp only [shiftAt, ite_eq_left hi]
  | fvar => rfl
  | app f a ihf iha =>
    simp only [Term.LcAt, Bool.and_eq_true] at h
    simp only [shiftAt, ihf h.1, iha h.2]
  | abs b ih => exact congrArg Term.abs (ih h)

/-- **Shifting leaves locally closed terms unchanged.**
Introducing a binder does not shift an already locally closed term. -/
theorem shiftAt_closed (c : Nat) (t : Term Nat) (h : t.LcAt 0) :
    shiftAt c t = t :=
  shiftAt_eq_self t (t.lcAt_le 0 c (Nat.zero_le c) h)

private theorem openRec_shiftAt (u : Term Nat) (hu : u.LcAt 0)
    {c k : Nat} (hck : c ≤ k) (t : Term Nat) :
    Term.openRec (k + 1) u (shiftAt c t) =
      shiftAt c (Term.openRec k u t) := by
  induction t generalizing c k with
  | bvar i =>
    by_cases hi : i < c
    · have hik : i < k := Nat.lt_of_lt_of_le hi hck
      simp [shiftAt, Term.openRec, hi, Nat.ne_of_gt hik,
        Nat.ne_of_gt (Nat.lt_succ_of_lt hik)]
    · by_cases heq : i = k
      · subst i
        simp [shiftAt, Term.openRec, hi, shiftAt_closed c u hu]
      · simp [shiftAt, Term.openRec, hi, Ne.symm heq]
  | fvar => rfl
  | app f a ihf iha => simp only [shiftAt, Term.openRec, ihf hck, iha hck]
  | abs b ih => exact congrArg Term.abs (ih (Nat.succ_le_succ hck))

private theorem shiftAt_comm {c d : Nat} (hcd : c ≤ d) (t : Term Nat) :
    shiftAt c (shiftAt d t) = shiftAt (d + 1) (shiftAt c t) := by
  induction t generalizing c d with
  | bvar i =>
    by_cases hi : i < c
    · have hd : i < d := Nat.lt_of_lt_of_le hi hcd
      simp [shiftAt, hi, hd, Nat.lt_succ_of_lt hd]
    · by_cases hd : i < d
      · simp [shiftAt, hi, hd]
      · have hc : ¬i + 1 < c := Nat.not_lt_of_ge
          (Nat.le_trans (Nat.le_of_not_gt hi) (Nat.le_succ i))
        simp [shiftAt, hi, hd, hc]
  | fvar => rfl
  | app f a ihf iha => simp only [shiftAt, ihf hcd, iha hcd]
  | abs b ih => exact congrArg Term.abs (ih (Nat.succ_le_succ hcd))

namespace Tm

/-- **Type erasure under an untyped environment.**
Erase a scoped term under an arbitrary simultaneous untyped environment. -/
@[simp] def eraseWith {n m : Nat} (σ : Fin m → Term Nat) :
    Tm n m → Term Nat
  | .var i => σ i
  | .lam _ b => .abs (eraseWith (liftRaw σ) b)
  | .app f a => .app (eraseWith σ f) (eraseWith σ a)
  | .tabs b => eraseWith σ b
  | .tapp f _ => eraseWith σ f

/-- **Type erasure of System F terms to untyped terms.**
Type erasure into the existing untyped de Bruijn syntax. -/
def erase {n m : Nat} (t : Tm n m) : Term Nat :=
  eraseWith (fun i => .bvar i.val) t

/-- **Erasure with locally closed images is locally closed.**
Erasure preserves the closure invariant of its environment images. -/
theorem eraseWith_lcAt {n m k : Nat} (σ : Fin m → Term Nat) (t : Tm n m)
    (hσ : ∀ i, (σ i).LcAt k) : (eraseWith σ t).LcAt k := by
  induction t generalizing k with
  | var i => exact hσ i
  | lam A b ih =>
    apply ih
    intro i
    induction i using Fin.cases with
    | zero => simp only [liftRaw, Fin.cases_zero, Term.LcAt,
        decide_eq_true_eq, Nat.zero_lt_succ]
    | succ i => exact shiftAt_lcAt (σ i) (hσ i)
  | app f a ihf iha =>
    simp only [eraseWith, Term.LcAt, Bool.and_eq_true]
    exact ⟨ihf σ hσ, iha σ hσ⟩
  | tabs b ih => exact ih σ hσ
  | tapp f A ih => exact ih σ hσ

/-- **Closing System F terms in the term model.**
Close every scoped term variable with a locally closed model term. -/
def close {n m : Nat} (σ : Fin m → Model) (t : Tm n m) : Model :=
  ⟨eraseWith (fun i => (σ i).val) t,
    eraseWith_lcAt _ t (fun i => (σ i).property)⟩

/-- **Erasure of closed System F terms to the term model.**
Erase a term with no free term variables into the existing term model. -/
def eraseModel {n : Nat} (t : Tm n 0) : Model := close Fin.elim0 t

/-- **Opening commutes with erasure under an environment.**
Opening an erased instance opens exactly its raw environment images. -/
theorem eraseWith_openRec {n m : Nat} (u : Term Nat) (hu : u.LcAt 0)
    (k : Nat) (σ : Fin m → Term Nat) (t : Tm n m) :
    Term.openRec k u (eraseWith σ t) =
      eraseWith (fun i => Term.openRec k u (σ i)) t := by
  induction t generalizing k with
  | var => rfl
  | lam A b ih =>
    simp only [eraseWith, Term.openRec, ih]
    congr 2
    funext i
    induction i using Fin.cases with
    | zero => simp [liftRaw, Term.openRec]
    | succ i => exact openRec_shiftAt u hu (Nat.zero_le k) (σ i)
  | app f a ihf iha => simp only [eraseWith, Term.openRec, ihf, iha]
  | tabs b ih => exact ih (k := k) (σ := σ)
  | tapp f A ih => exact ih (k := k) (σ := σ)

/-- **Untyped erasure is invariant under type substitution.**
Type substitution changes no part of the erased untyped term. -/
theorem eraseWith_tySubst {n k m : Nat} (σ : Fin n → Ty k)
    (η : Fin m → Term Nat) (t : Tm n m) :
    eraseWith η (tySubst σ t) = eraseWith η t := by
  induction t generalizing k with
  | var => rfl
  | lam A b ih => simp only [tySubst, eraseWith, ih]
  | app f a ihf iha => simp only [tySubst, eraseWith, ihf, iha]
  | tabs b ih => simp only [tySubst, eraseWith, ih]
  | tapp f A ih => simp only [tySubst, eraseWith, ih]

/-- **Closing a System F variable.** Closing a variable returns exactly its environment image. -/
@[simp] theorem close_var {n m : Nat} (σ : Fin m → Model) (i : Fin m) :
    close σ (.var i : Tm n m) = σ i := rfl

/-- **Closing a System F application.** Closing commutes with the upstream model's application. -/
@[simp] theorem close_app {n m : Nat} (σ : Fin m → Model) (f a : Tm n m) :
    close σ (.app f a) = Model.app (close σ f) (close σ a) := rfl

/-- **Closing erases System F type abstraction.** A type lambda contributes no untyped binder. -/
@[simp] theorem close_tabs {n m : Nat} (σ : Fin m → Model)
    (b : Tm (n + 1) m) : close σ (.tabs b) = close σ b := rfl

/-- **Closing erases System F type application.**
A type argument contributes no untyped application. -/
@[simp] theorem close_tapp {n m : Nat} (σ : Fin m → Model)
    (f : Tm n m) (A : Ty n) : close σ (.tapp f A) = close σ f := rfl

/-- **System F closing is invariant under type substitution.**
Closing is independent of every type substitution. -/
@[simp] theorem close_tySubst {n k m : Nat} (σ : Fin n → Ty k)
    (η : Fin m → Model) (t : Tm n m) :
    close η (tySubst σ t) = close η t := by
  apply Subtype.ext
  exact eraseWith_tySubst σ (fun i => (η i).val) t

private theorem open_lift {n m : Nat} (σ : Fin m → Model)
    (b : Tm n (m + 1)) (a : Model) :
    Term.openRec 0 a.val (eraseWith (liftRaw (fun i => (σ i).val)) b) =
      (close (Fin.cases a σ) b).val := by
  rw [eraseWith_openRec a.val a.property]
  congr 1
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [liftRaw, Fin.cases_succ,
      shiftAt_closed 0 (σ i).val (σ i).property]
    exact Term.lcAt_openRec_above_lcAt (σ i).val a.val 0 0
      (Nat.le_refl 0) (σ i).property

/-- **Beta conversion of a closed System F lambda application.**
An erased lambda application beta-converts to its extended body instance. -/
theorem close_beta {n m : Nat} (σ : Fin m → Model) (A : Ty n)
    (b : Tm n (m + 1)) (a : Model) :
    BetaEq (Model.app (close σ (.lam A b)) a) (close (Fin.cases a σ) b) := by
  have hs : Term.FullBeta (Model.app (close σ (.lam A b)) a).val
      (Term.openRec 0 a.val (eraseWith (liftRaw (fun i => (σ i).val)) b)) :=
    Term.Xi.base (Term.Beta.beta (close σ (.lam A b)).lc a.lc)
  rw [open_lift] at hs
  exact Relation.EqvGen.rel _ _ hs

/-- **Shifting commutes with erasure under an environment.**
Shifting an erased instance shifts exactly its raw environment images. -/
theorem eraseWith_shift {n m : Nat} (c : Nat) (σ : Fin m → Term Nat)
    (t : Tm n m) : shiftAt c (eraseWith σ t) =
      eraseWith (fun i => shiftAt c (σ i)) t := by
  induction t generalizing c with
  | var => rfl
  | lam A b ih =>
    simp only [eraseWith, shiftAt, ih]
    congr 2
    funext i
    induction i using Fin.cases with
    | zero => simp [liftRaw, shiftAt]
    | succ i => exact (shiftAt_comm (Nat.zero_le c) (σ i)).symm
  | app f a ihf iha => simp only [eraseWith, shiftAt, ihf, iha]
  | tabs b ih => exact ih (c := c) (σ := σ)
  | tapp f A ih => exact ih (c := c) (σ := σ)

/-- **Erasure of a term-variable renaming.**
Erasing a term-variable renaming precomposes the raw environment. -/
theorem eraseWith_rename {n m k : Nat} (η : Fin m → Fin k)
    (σ : Fin k → Term Nat) (t : Tm n m) :
    eraseWith σ (rename η t) = eraseWith (σ ∘ η) t := by
  induction t generalizing k with
  | var => rfl
  | lam A b ih =>
    simp only [rename, eraseWith, ih]
    congr 2
    funext i
    induction i using Fin.cases <;> rfl
  | app f a ihf iha => simp only [rename, eraseWith, ihf, iha]
  | tabs b ih => simp only [rename, eraseWith, ih]
  | tapp f A ih => simp only [rename, eraseWith, ih]

/-- **Erasure of a term substitution.**
Actual term substitution erases by composing raw environments. -/
theorem eraseWith_subst {n m k : Nat} (σ : Fin m → Tm n k)
    (η : Fin k → Term Nat) (t : Tm n m) :
    eraseWith η (subst σ t) =
      eraseWith (fun i => eraseWith η (σ i)) t := by
  induction t generalizing k with
  | var => rfl
  | lam A b ih =>
    simp only [subst, eraseWith, ih]
    congr 2
    funext i
    induction i using Fin.cases with
    | zero => rfl
    | succ i =>
      change eraseWith (liftRaw η) (rename Fin.succ (σ i)) =
        shiftAt 0 (eraseWith η (σ i))
      rw [eraseWith_rename]
      exact (eraseWith_shift 0 η (σ i)).symm
  | app f a ihf iha => simp only [subst, eraseWith, ihf, iha]
  | tabs b ih => simp only [subst, eraseWith, ih, tyRename, eraseWith_tySubst]
  | tapp f A ih => simp only [subst, eraseWith, ih]

/-- **Closing commutes with System F term substitution.**
Closing an actual substitution composes its model-valued environments. -/
theorem close_subst {n m k : Nat} (σ : Fin m → Tm n k)
    (η : Fin k → Model) (t : Tm n m) :
    close η (subst σ t) = close (fun i => close η (σ i)) t := by
  apply Subtype.ext
  exact eraseWith_subst σ (fun i => (η i).val) t

/-- **Closing an instantiated System F term binder.**
Actual binder discharge agrees with extending the closing environment. -/
theorem close_instantiate {n m : Nat} (η : Fin m → Model)
    (b : Tm n (m + 1)) (a : Tm n m) :
    close η (instantiate b a) = close (Fin.cases (close η a) η) b := by
  rw [instantiate, close_subst]
  congr 1
  funext i
  induction i using Fin.cases <;> rfl

end Tm

end Cslib.Languages.LambdaCalculus.SystemF
