/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.FOmega.Safety
public import CSLibExt.Languages.LambdaCalculus.SystemF.Semantics

/-! # The star/forall System F fragment inside pure Fω

The translation is generalized over images of the free System F type
variables. Its canonical specialization maps each variable to the
corresponding star-kinded variable. No source type constructor is erased.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.FOmega

/-- Extend images of System F type variables under a star-kinded binder. -/
def liftTypes {n : Nat} {Δ : List Kind} (φ : Fin n → Ty Δ .star) :
    Fin (n + 1) → Ty (.star :: Δ) .star :=
  Fin.cases (.var .zero) (fun i => (φ i).rename KVar.succ)

/-- Translate System F types with arbitrary kind-`star` variable images. -/
def Ty.fromSystemF : {n : Nat} → {Δ : List Kind} →
    (Fin n → Ty Δ .star) → SystemF.Ty n → Ty Δ .star
  | _, _, φ, .var i => φ i
  | _, _, φ, .arr A B => .arr (fromSystemF φ A) (fromSystemF φ B)
  | _, _, φ, .all B => .all (fromSystemF (liftTypes φ) B)

namespace Ty

variable {n k : Nat} {Δ Ε : List Kind}

/-- The translation depends only on the images of free type variables. -/
theorem fromSystemF_congr {φ ψ : Fin n → Ty Δ .star}
    (h : ∀ i, φ i = ψ i) (t : SystemF.Ty n) :
    fromSystemF φ t = fromSystemF ψ t := by
  have e : φ = ψ := funext h
  rw [e]

/-- Target kind-preserving renaming commutes with the System F translation. -/
theorem fromSystemF_target_rename (φ : Fin n → Ty Δ .star)
    (ρ : KRen Δ Ε) (t : SystemF.Ty n) :
    (fromSystemF φ t).rename ρ =
      fromSystemF (fun i => (φ i).rename ρ) t := by
  induction t generalizing Δ Ε with
  | var => rfl
  | arr A B ihA ihB => simp [fromSystemF, rename, ihA, ihB]
  | all B ih =>
    simp only [fromSystemF, rename]
    congr 1
    rw [ih]
    apply fromSystemF_congr
    intro i
    induction i using Fin.cases with
    | zero => rfl
    | succ i =>
      simp only [liftTypes, Fin.cases_succ, rename_rename]
      apply rename_congr
      intro ν x
      rfl

/-- Target type substitution commutes with the System F translation. -/
theorem fromSystemF_target_subst (φ : Fin n → Ty Δ .star)
    (σ : Sub Δ Ε) (t : SystemF.Ty n) :
    (fromSystemF φ t).subst σ =
      fromSystemF (fun i => (φ i).subst σ) t := by
  induction t generalizing Δ Ε with
  | var => rfl
  | arr A B ihA ihB => simp [fromSystemF, subst, ihA, ihB]
  | all B ih =>
    simp only [fromSystemF, subst]
    congr 1
    rw [ih]
    apply fromSystemF_congr
    intro i
    induction i using Fin.cases with
    | zero => rfl
    | succ i => exact subst_lift_rename σ (φ i)

/-- Source type renaming is precomposition of the translated variable images. -/
theorem fromSystemF_source_rename (φ : Fin k → Ty Δ .star)
    (ρ : Fin n → Fin k) (t : SystemF.Ty n) :
    fromSystemF φ (t.rename ρ) = fromSystemF (fun i => φ (ρ i)) t := by
  induction t generalizing k Δ with
  | var => rfl
  | arr A B ihA ihB => simp [fromSystemF, ihA, ihB]
  | all B ih =>
    simp only [fromSystemF, SystemF.Ty.rename]
    congr 1
    rw [ih]
    apply fromSystemF_congr
    intro i
    induction i using Fin.cases <;> rfl

/-- Source type substitution translates to simultaneous operator images. -/
theorem fromSystemF_source_subst (φ : Fin k → Ty Δ .star)
    (σ : Fin n → SystemF.Ty k) (t : SystemF.Ty n) :
    fromSystemF φ (t.subst σ) =
      fromSystemF (fun i => fromSystemF φ (σ i)) t := by
  induction t generalizing k Δ with
  | var => rfl
  | arr A B ihA ihB => simp [fromSystemF, ihA, ihB]
  | all B ih =>
    simp only [fromSystemF, SystemF.Ty.subst]
    congr 1
    rw [ih]
    apply fromSystemF_congr
    intro i
    induction i using Fin.cases with
    | zero => rfl
    | succ i =>
      simpa only [SystemF.Ty.liftSub, liftTypes, Fin.cases_succ,
        fromSystemF_source_rename] using
        (fromSystemF_target_rename φ KVar.succ (σ i)).symm

/-- The System F translation commutes with type-binder instantiation. -/
theorem fromSystemF_instantiate (φ : Fin n → Ty Δ .star)
    (B : SystemF.Ty (n + 1)) (A : SystemF.Ty n) :
    fromSystemF φ (B.instantiate A) =
      (fromSystemF (liftTypes φ) B).instantiate (fromSystemF φ A) := by
  simp only [SystemF.Ty.instantiate, fromSystemF_source_subst,
    instantiate, fromSystemF_target_subst]
  apply fromSystemF_congr
  intro i
  induction i using Fin.cases with
  | zero => rfl
  | succ i => exact (instantiate_rename_succ (φ i) (fromSystemF φ A)).symm

end Ty

/-- Translate all five System F term constructors, retaining type binders. -/
def Tm.fromSystemF : {n m : Nat} → {Δ : List Kind} →
    (Fin n → Ty Δ .star) → SystemF.Tm n m → Tm Δ m
  | _, _, _, _, .var i => .var i
  | _, _, _, φ, .lam A b => .lam (Ty.fromSystemF φ A) (fromSystemF φ b)
  | _, _, _, φ, .app f a => .app (fromSystemF φ f) (fromSystemF φ a)
  | _, _, _, φ, .tabs b => .tabs (fromSystemF (liftTypes φ) b)
  | _, _, _, φ, .tapp f A => .tapp (fromSystemF φ f) (Ty.fromSystemF φ A)

/-- Every System F typing derivation is preserved by the star translation. -/
theorem Tm.fromSystemF_typing {n m : Nat} {Δ : List Kind}
    {Γ : SystemF.Ctx n m} {t : SystemF.Tm n m} {A : SystemF.Ty n}
    (h : SystemF.Typing Γ t A) (φ : Fin n → Ty Δ .star) :
    Typing (fun i => Ty.fromSystemF φ (Γ i)) (fromSystemF φ t)
      (Ty.fromSystemF φ A) := by
  induction h generalizing Δ with
  | var i => exact .var i
  | lam hb ih =>
    apply Typing.lam
    convert ih φ using 1
    funext i
    induction i using Fin.cases <;> rfl
  | app hf ha ihf iha => exact .app (ihf φ) (iha φ)
  | tabs hb ih =>
    apply Typing.tabs
    simpa only [Ty.fromSystemF_source_rename, liftTypes, Fin.cases_succ,
      Ty.fromSystemF_target_rename] using ih (liftTypes φ)
  | tapp hf ih =>
    rw [Tm.fromSystemF, Ty.fromSystemF_instantiate]
    exact .tapp (ih φ)

/-- The corresponding star-kinded variable in an `n`-star telescope. -/
def KVar.ofFin : {n : Nat} → Fin n → KVar (List.replicate n .star) .star
  | 0, i => nomatch i
  | _n + 1, i => Fin.cases .zero (fun j => .succ (ofFin j)) i

/-- The canonical variable-for-variable embedding of System F types. -/
def Ty.embed {n : Nat} (t : SystemF.Ty n) : Ty (List.replicate n .star) .star :=
  fromSystemF (fun i => .var (KVar.ofFin i)) t

/-- The canonical scoped embedding of System F terms into pure Fω. -/
def Tm.embed {n m : Nat} (t : SystemF.Tm n m) : Tm (List.replicate n .star) m :=
  fromSystemF (fun i => .var (KVar.ofFin i)) t

/-- Canonical embedding preserves every System F typing derivation. -/
theorem Tm.embed_typing {n m : Nat} {Γ : SystemF.Ctx n m}
    {t : SystemF.Tm n m} {A : SystemF.Ty n} (h : SystemF.Typing Γ t A) :
    Typing (fun i => Ty.embed (Γ i)) (Tm.embed t) (Ty.embed A) :=
  fromSystemF_typing h (fun i => .var (KVar.ofFin i))

/-- Term translation depends only on the images of its free type variables. -/
theorem Tm.fromSystemF_congr {n m : Nat} {Δ : List Kind}
    {φ ψ : Fin n → Ty Δ .star} (h : ∀ i, φ i = ψ i) (t : SystemF.Tm n m) :
    fromSystemF φ t = fromSystemF ψ t := by
  have e : φ = ψ := funext h
  rw [e]

/-- Operator substitution commutes with translating System F terms. -/
theorem Tm.fromSystemF_target_tySubst {n m : Nat} {Δ Ε : List Kind}
    (φ : Fin n → Ty Δ .star) (σ : Ty.Sub Δ Ε) (t : SystemF.Tm n m) :
    (fromSystemF φ t).tySubst σ =
      fromSystemF (fun i => (φ i).subst σ) t := by
  induction t generalizing Δ Ε with
  | var => rfl
  | lam A b ih =>
    simp [fromSystemF, Ty.fromSystemF_target_subst, ih]
  | app f a ihf iha => simp [fromSystemF, ihf, iha]
  | tapp f A ih => simp [fromSystemF, Ty.fromSystemF_target_subst, ih]
  | tabs b ih =>
    simp only [fromSystemF, tySubst]
    congr 1
    rw [ih]
    apply fromSystemF_congr
    intro i
    induction i using Fin.cases with
    | zero => rfl
    | succ i => exact Ty.subst_lift_rename σ (φ i)

/-- Source type substitution commutes with the pure-term translation. -/
theorem Tm.fromSystemF_source_tySubst {n k m : Nat} {Δ : List Kind}
    (φ : Fin k → Ty Δ .star) (σ : Fin n → SystemF.Ty k)
    (t : SystemF.Tm n m) :
    fromSystemF φ (t.tySubst σ) =
      fromSystemF (fun i => Ty.fromSystemF φ (σ i)) t := by
  induction t generalizing k Δ with
  | var => rfl
  | lam A b ih => simp [fromSystemF, Ty.fromSystemF_source_subst, ih]
  | app f a ihf iha => simp [fromSystemF, ihf, iha]
  | tapp f A ih => simp [fromSystemF, Ty.fromSystemF_source_subst, ih]
  | tabs b ih =>
    simp only [fromSystemF, SystemF.Tm.tySubst]
    congr 1
    rw [ih]
    apply fromSystemF_congr
    intro i
    induction i using Fin.cases with
    | zero => rfl
    | succ i =>
      simpa only [SystemF.Ty.liftSub, liftTypes, Fin.cases_succ,
        Ty.fromSystemF_source_rename] using
        (Ty.fromSystemF_target_rename φ KVar.succ (σ i)).symm

/-- Weakening beneath a type binder agrees in both calculus presentations. -/
theorem Tm.fromSystemF_tyRename_succ {n m : Nat} {Δ : List Kind}
    (φ : Fin n → Ty Δ .star) (t : SystemF.Tm n m) :
    fromSystemF (liftTypes φ) (t.tyRename Fin.succ) =
      (fromSystemF φ t).tyRename KVar.succ := by
  simp only [SystemF.Tm.tyRename, Tm.tyRename,
    fromSystemF_source_tySubst, fromSystemF_target_tySubst,
    Ty.fromSystemF, liftTypes, Fin.cases_succ, Ty.subst_var_rename]

/-- Term-variable renaming commutes with the System F translation. -/
theorem Tm.fromSystemF_rename {n m k : Nat} {Δ : List Kind}
    (φ : Fin n → Ty Δ .star) (ρ : Fin m → Fin k) (t : SystemF.Tm n m) :
    fromSystemF φ (t.rename ρ) = (fromSystemF φ t).rename ρ := by
  induction t generalizing k Δ with
  | var => rfl
  | lam A b ih => simp [fromSystemF, ih]
  | app f a ihf iha => simp [fromSystemF, ihf, iha]
  | tabs b ih => simp [fromSystemF, ih]
  | tapp f A ih => simp [fromSystemF, ih]

private theorem fromSystemF_liftSub {n m k : Nat} {Δ : List Kind}
    (φ : Fin n → Ty Δ .star) (σ : Fin m → SystemF.Tm n k)
    (i : Fin (m + 1)) :
    Tm.fromSystemF φ (SystemF.Tm.liftSub σ i) =
      Tm.liftSub (fun j => Tm.fromSystemF φ (σ j)) i := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i =>
    simpa only [SystemF.Tm.liftSub, Tm.liftSub, Fin.cases_succ] using
      Tm.fromSystemF_rename φ Fin.succ (σ i)

/-- Simultaneous term substitution commutes with the System F translation. -/
theorem Tm.fromSystemF_subst {n m k : Nat} {Δ : List Kind}
    (φ : Fin n → Ty Δ .star) (σ : Fin m → SystemF.Tm n k)
    (t : SystemF.Tm n m) :
    fromSystemF φ (t.subst σ) =
      (fromSystemF φ t).subst (fun i => fromSystemF φ (σ i)) := by
  induction t generalizing k Δ with
  | var => rfl
  | app f a ihf iha => simp [fromSystemF, ihf, iha]
  | tapp f A ih => simp [fromSystemF, ih]
  | tabs b ih => simp [fromSystemF, ih, fromSystemF_tyRename_succ]
  | lam A b ih =>
    simp only [SystemF.Tm.subst, fromSystemF, Tm.subst, ih]
    congr 1
    congr 1
    funext i
    exact fromSystemF_liftSub φ σ i

/-- Term-binder instantiation commutes with the System F translation. -/
theorem Tm.fromSystemF_instantiate {n m : Nat} {Δ : List Kind}
    (φ : Fin n → Ty Δ .star) (b : SystemF.Tm n (m + 1))
    (a : SystemF.Tm n m) :
    fromSystemF φ (b.instantiate a) =
      (fromSystemF φ b).instantiate (fromSystemF φ a) := by
  simp only [SystemF.Tm.instantiate, fromSystemF_subst, Tm.instantiate]
  congr 1
  funext i
  induction i using Fin.cases <;> rfl

/-- Type-binder discharge agrees for translated System F terms. -/
theorem Tm.fromSystemF_tyInstantiate {n m : Nat} {Δ : List Kind}
    (φ : Fin n → Ty Δ .star) (b : SystemF.Tm (n + 1) m)
    (A : SystemF.Ty n) :
    fromSystemF φ (b.tySubst (Fin.cases A SystemF.Ty.var)) =
      (fromSystemF (liftTypes φ) b).tySubst (Ty.single (Ty.fromSystemF φ A)) := by
  simp only [fromSystemF_source_tySubst, fromSystemF_target_tySubst]
  apply fromSystemF_congr
  intro i
  induction i using Fin.cases with
  | zero => rfl
  | succ i =>
    exact (Ty.instantiate_rename_succ (φ i) (Ty.fromSystemF φ A)).symm

/-- The System F translation preserves both weak-CBV value forms. -/
theorem Tm.fromSystemF_value {n m : Nat} {Δ : List Kind}
    (φ : Fin n → Ty Δ .star) {t : SystemF.Tm n m} (h : SystemF.Value t) :
    Value (fromSystemF φ t) := by
  cases h with
  | lam => exact .lam _ _
  | tabs => exact .tabs _

/-- Every System F weak-CBV step is simulated by one Fω weak-CBV step. -/
theorem Tm.fromSystemF_step {n m : Nat} {Δ : List Kind}
    (φ : Fin n → Ty Δ .star) {t t' : SystemF.Tm n m}
    (h : SystemF.Step t t') : Step (fromSystemF φ t) (fromSystemF φ t') := by
  induction h generalizing Δ with
  | appFun h ih => exact .appFun (ih φ)
  | appArg hv h ih => exact .appArg (fromSystemF_value φ hv) (ih φ)
  | tappFun h ih => exact .tapp (ih φ)
  | beta hv =>
    rw [fromSystemF_instantiate]
    exact .beta (fromSystemF_value φ hv)
  | tyBeta =>
    rw [fromSystemF_tyInstantiate]
    exact .tybeta _ _

/-- The canonical embedding preserves individual System F evaluation steps. -/
theorem Tm.embed_step {n m : Nat} {t t' : SystemF.Tm n m}
    (h : SystemF.Step t t') : Step (Tm.embed t) (Tm.embed t') :=
  fromSystemF_step (fun i => .var (KVar.ofFin i)) h

/-- The canonical embedding preserves finite System F evaluation sequences. -/
theorem Tm.embed_steps {n m : Nat} {t t' : SystemF.Tm n m}
    (h : SystemF.Steps t t') :
    Relation.ReflTransGen Step (Tm.embed t) (Tm.embed t') :=
  h.lift Tm.embed (fun _ _ => embed_step)

end Cslib.Languages.LambdaCalculus.FOmega
