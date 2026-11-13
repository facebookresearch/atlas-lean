/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.FOmega.Typing
public import CSLibExt.Languages.LambdaCalculus.FOmega.Confluence

/-! # Conversion-aware weak call-by-value safety for pure Fω

Canonical forms use proved type-beta confluence/inversion, including the
kind of a universal binder. They are not assumptions of the typing judgment.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.FOmega

/-- Weak-CBV values: neither form of lambda evaluates beneath its binder. -/
inductive Value : {Δ : List Kind} → {m : Nat} → Tm Δ m → Prop where
  | lam {Δ : List Kind} {m : Nat} (A : Ty Δ .star) (b : Tm Δ (m + 1)) :
      Value (.lam A b)
  | tabs {Δ : List Kind} {m : Nat} {κ : Kind} (b : Tm (κ :: Δ) m) :
      Value (.tabs b)

/-- Ordinary left-to-right weak call-by-value reduction. -/
inductive Step : {Δ : List Kind} → {m : Nat} → Tm Δ m → Tm Δ m → Prop where
  | beta {Δ : List Kind} {m : Nat} {A : Ty Δ .star}
      {b : Tm Δ (m + 1)} {a : Tm Δ m} :
      Value a → Step (.app (.lam A b) a) (b.instantiate a)
  | tybeta {Δ : List Kind} {m : Nat} {κ : Kind}
      (b : Tm (κ :: Δ) m) (a : Ty Δ κ) :
      Step (.tapp (.tabs b) a) (b.tySubst (Ty.single a))
  | appFun {Δ : List Kind} {m : Nat} {f f' a : Tm Δ m} :
      Step f f' → Step (.app f a) (.app f' a)
  | appArg {Δ : List Kind} {m : Nat} {f a a' : Tm Δ m} :
      Value f → Step a a' → Step (.app f a) (.app f a')
  | tapp {Δ : List Kind} {m : Nat} {κ : Kind}
      {f f' : Tm Δ m} {a : Ty Δ κ} :
      Step f f' → Step (.tapp f a) (.tapp f' a)

variable {Δ : List Kind} {m : Nat} {Γ : Ctx Δ m}

/-- Lambda typing inversion retains the annotation and a proved conversion. -/
theorem Typing.lam_inv {A T : Ty Δ .star} {b : Tm Δ (m + 1)}
    (h : Typing Γ (.lam A b) T) :
    ∃ B, Typing (Fin.cases A Γ) b B ∧ Ty.Conv (.arr A B) T := by
  generalize e : Tm.lam A b = u at h
  induction h with
  | lam hb ih => cases e; exact ⟨_, hb, .refl _⟩
  | conv ht hc ih =>
    obtain ⟨B, hb, he⟩ := ih e
    exact ⟨B, hb, .trans he hc⟩
  | var i => cases e
  | app hf ha ihf iha => cases e
  | tabs hb ih => cases e
  | tapp hf ih => cases e

/-- Type-lambda inversion retains its binder kind and body conversion. -/
theorem Typing.tabs_inv {κ : Kind} {T : Ty Δ .star}
    {b : Tm (κ :: Δ) m} (h : Typing Γ (.tabs b) T) :
    ∃ B : Ty (κ :: Δ) .star,
      Typing (fun i => (Γ i).rename KVar.succ) b B ∧
        Ty.Conv (.all B) T := by
  generalize e : Tm.tabs b = u at h
  induction h with
  | tabs hb ih => cases e; exact ⟨_, hb, .refl _⟩
  | conv ht hc ih =>
    obtain ⟨B, hb, he⟩ := ih e
    exact ⟨B, hb, .trans he hc⟩
  | var i => cases e
  | lam hb ih => cases e
  | app hf ha ihf iha => cases e
  | tapp hf ih => cases e

/-- Weak-CBV reduction preserves typing in unrestricted open contexts. -/
theorem Typing.preservation {A : Ty Δ .star} {t t' : Tm Δ m}
    (h : Typing Γ t A) (hs : Step t t') : Typing Γ t' A := by
  induction h with
  | var i => cases hs
  | lam hb ih => cases hs
  | tabs hb ih => cases hs
  | conv ht hc ih => exact .conv (ih hs) hc
  | app hf ha ihf iha =>
    cases hs with
    | appFun hs => exact .app (ihf hs) ha
    | appArg hv hs => exact .app hf (iha hs)
    | beta hv =>
      obtain ⟨B, hb, hc⟩ := hf.lam_inv
      obtain ⟨hA, hB⟩ := hc.arr_inj
      exact .conv (hb.instantiate (.conv ha hA.symm)) hB
  | @tapp Δ m κ Γ f A C hf ih =>
    cases hs with
    | tapp hs => exact .tapp (ih hs)
    | tybeta =>
      obtain ⟨B, hb, hc⟩ := hf.tabs_inv
      exact .conv (hb.tyInstantiate A) (hc.all_inj.subst (Ty.single A))

/-- A value typed at an arrow, despite conversion, is a term lambda. -/
theorem Value.arrow {A B : Ty Δ .star} {t : Tm Δ m}
    (hv : Value t) (h : Typing Γ t (.arr A B)) :
    ∃ C b, t = .lam C b := by
  cases hv with
  | lam C b => exact ⟨C, b, rfl⟩
  | tabs b =>
    obtain ⟨C, hb, hc⟩ := h.tabs_inv
    exact False.elim (Ty.not_conv_arr_all hc.symm)

/-- A value at a quantified type is a type lambda of the same binder kind. -/
theorem Value.all {κ : Kind} {C : Ty (κ :: Δ) .star} {t : Tm Δ m}
    (hv : Value t) (h : Typing Γ t (.all C)) :
    ∃ b : Tm (κ :: Δ) m, t = .tabs b := by
  cases hv with
  | lam A b =>
    obtain ⟨B, hb, hc⟩ := h.lam_inv
    exact False.elim (Ty.not_conv_arr_all hc)
  | @tabs μ b =>
    obtain ⟨B, hb, hc⟩ := h.tabs_inv
    have e : μ = κ := hc.all_kind
    subst μ
    exact ⟨b, rfl⟩

private theorem app_progress {A B : Ty Δ .star} {f a : Tm Δ m}
    (hf : Typing Γ f (.arr A B))
    (pf : Value f ∨ ∃ f', Step f f')
    (pa : Value a ∨ ∃ a', Step a a') :
    ∃ t', Step (.app f a) t' := by
  rcases pf with hvf | ⟨f', hs⟩
  · rcases pa with hva | ⟨a', hs⟩
    · obtain ⟨C, b, rfl⟩ := hvf.arrow hf
      exact ⟨_, .beta hva⟩
    · exact ⟨_, .appArg hvf hs⟩
  · exact ⟨_, .appFun hs⟩

private theorem progress_of_empty {A : Ty Δ .star} {t : Tm Δ m}
    (h : Typing Γ t A) (empty : ∀ _ : Fin m, False) :
    Value t ∨ ∃ t', Step t t' := by
  induction h with
  | var i => exact False.elim (empty i)
  | lam hb ih => exact .inl (.lam _ _)
  | tabs hb ih => exact .inl (.tabs _)
  | conv ht hc ih => exact ih empty
  | app hf ha ihf iha => exact .inr (app_progress hf (ihf empty) (iha empty))
  | @tapp Δ m κ Γ f A C hf ih =>
    rcases ih empty with hv | ⟨f', hs⟩
    · obtain ⟨b, rfl⟩ := hv.all hf
      exact .inr ⟨_, .tybeta b A⟩
    · exact .inr ⟨_, .tapp hs⟩

/-- Closed-term progress, allowing an arbitrary open kinded-type telescope. -/
theorem Typing.progress {Γ : Ctx Δ 0} {A : Ty Δ .star} {t : Tm Δ 0}
    (h : Typing Γ t A) : Value t ∨ ∃ t', Step t t' :=
  progress_of_empty h Fin.elim0

/-- Every finite weak-CBV reduction sequence preserves typing. -/
theorem Typing.preservation_steps {A : Ty Δ .star} {t t' : Tm Δ m}
    (h : Typing Γ t A) (hs : Relation.ReflTransGen Step t t') :
    Typing Γ t' A := by
  induction hs with
  | refl => exact h
  | tail hs p ih => exact ih.preservation p

/-- No reachable closed well-typed term is stuck, with type variables allowed. -/
theorem Typing.safety {Γ : Ctx Δ 0} {A : Ty Δ .star} {t t' : Tm Δ 0}
    (h : Typing Γ t A) (hs : Relation.ReflTransGen Step t t') :
    Value t' ∨ ∃ u, Step t' u := (h.preservation_steps hs).progress

end Cslib.Languages.LambdaCalculus.FOmega
