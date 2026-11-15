/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic

@[expose] public section

/-- System F types with de Bruijn indices. -/
inductive Ty : Type
  | var : ℕ → Ty
  | arr : Ty → Ty → Ty
  | all : Ty → Ty
deriving DecidableEq

/-- Shift free type variables at or above cutoff `c` up by `d`. -/
def tyShift (d : ℕ) (c : ℕ) : Ty → Ty
  | .var k => if k < c then .var k else .var (k + d)
  | .arr A B => .arr (tyShift d c A) (tyShift d c B)
  | .all A => .all (tyShift d (c + 1) A)

/-- Substitute `S` for type variable `j` (decrementing higher
variables). -/
def tySubst (j : ℕ) (S : Ty) : Ty → Ty
  | .var k =>
      if k < j then .var k
      else if k = j then S
      else .var (k - 1)
  | .arr A B => .arr (tySubst j S A) (tySubst j S B)
  | .all A => .all (tySubst (j + 1) (tyShift 1 0 S) A)

/-- Type well-formedness under `Δ` type variables. -/
def TyWf (Δ : ℕ) : Ty → Prop
  | .var k => k < Δ
  | .arr A B => TyWf Δ A ∧ TyWf Δ B
  | .all A => TyWf (Δ + 1) A

/-- System F terms with de Bruijn indices (term and type
binders). -/
inductive Tm : Type
  | var : ℕ → Tm
  | lam : Ty → Tm → Tm
  | app : Tm → Tm → Tm
  | tlam : Tm → Tm
  | tapp : Tm → Ty → Tm
deriving DecidableEq

/-- Shift type variables inside a term. -/
def tmTyShift (d : ℕ) (c : ℕ) : Tm → Tm
  | .var k => .var k
  | .lam A t => .lam (tyShift d c A) (tmTyShift d c t)
  | .app t u => .app (tmTyShift d c t) (tmTyShift d c u)
  | .tlam t => .tlam (tmTyShift d (c + 1) t)
  | .tapp t A => .tapp (tmTyShift d c t) (tyShift d c A)

/-- Shift free term variables at or above cutoff `c` up by `d`. -/
def tmShift (d : ℕ) (c : ℕ) : Tm → Tm
  | .var k => if k < c then .var k else .var (k + d)
  | .lam A t => .lam A (tmShift d (c + 1) t)
  | .app t u => .app (tmShift d c t) (tmShift d c u)
  | .tlam t => .tlam (tmShift d c t)
  | .tapp t A => .tapp (tmShift d c t) A

/-- Substitute term `s` for term variable `j`. -/
def tmSubst (j : ℕ) (s : Tm) : Tm → Tm
  | .var k =>
      if k < j then .var k
      else if k = j then s
      else .var (k - 1)
  | .lam A t => .lam A (tmSubst (j + 1) (tmShift 1 0 s) t)
  | .app t u => .app (tmSubst j s t) (tmSubst j s u)
  | .tlam t => .tlam (tmSubst j (tmTyShift 1 0 s) t)
  | .tapp t A => .tapp (tmSubst j s t) A

/-- Substitute type `S` for type variable `j` inside a term. -/
def tmTySubst (j : ℕ) (S : Ty) : Tm → Tm
  | .var k => .var k
  | .lam A t => .lam (tySubst j S A) (tmTySubst j S t)
  | .app t u => .app (tmTySubst j S t) (tmTySubst j S u)
  | .tlam t => .tlam (tmTySubst (j + 1) (tyShift 1 0 S) t)
  | .tapp t A => .tapp (tmTySubst j S t) (tySubst j S A)

/-- Typing: `HasType Δ Γ t T` with `Δ` the number of type
variables in scope and `Γ` a de Bruijn context (head is
variable 0). -/
inductive HasType : ℕ → List Ty → Tm → Ty → Prop
  | var {Δ : ℕ} {Γ : List Ty} {k : ℕ} {T : Ty} (h : Γ[k]? = some T)
      (hwf : TyWf Δ T) : HasType Δ Γ (.var k) T
  | lam {Δ : ℕ} {Γ : List Ty} {A B : Ty} {t : Tm} (hA : TyWf Δ A)
      (h : HasType Δ (A :: Γ) t B) :
      HasType Δ Γ (.lam A t) (.arr A B)
  | app {Δ : ℕ} {Γ : List Ty} {A B : Ty} {t u : Tm}
      (h₁ : HasType Δ Γ t (.arr A B)) (h₂ : HasType Δ Γ u A) :
      HasType Δ Γ (.app t u) B
  | tlam {Δ : ℕ} {Γ : List Ty} {T : Ty} {t : Tm}
      (h : HasType (Δ + 1) (Γ.map (tyShift 1 0)) t T) :
      HasType Δ Γ (.tlam t) (.all T)
  | tapp {Δ : ℕ} {Γ : List Ty} {T : Ty} {t : Tm} {S : Ty}
      (h : HasType Δ Γ t (.all T)) (hS : TyWf Δ S) :
      HasType Δ Γ (.tapp t S) (tySubst 0 S T)

/-- Full beta reduction (term beta and type beta, with
congruence in every subterm position). -/
inductive Step : Tm → Tm → Prop
  | beta {A : Ty} {t u : Tm} : Step (.app (.lam A t) u) (tmSubst 0 u t)
  | tbeta {t : Tm} {S : Ty} : Step (.tapp (.tlam t) S) (tmTySubst 0 S t)
  | appL {t t' u : Tm} (h : Step t t') : Step (.app t u) (.app t' u)
  | appR {t u u' : Tm} (h : Step u u') : Step (.app t u) (.app t u')
  | lam {A : Ty} {t t' : Tm} (h : Step t t') :
      Step (.lam A t) (.lam A t')
  | tlam {t t' : Tm} (h : Step t t') : Step (.tlam t) (.tlam t')
  | tapp {t t' : Tm} {S : Ty} (h : Step t t') :
      Step (.tapp t S) (.tapp t' S)

private theorem tyShift_zero {c : ℕ} {A : Ty} : tyShift 0 c A = A := by
  induction A generalizing c with
  | var k =>
      simp only [tyShift, tySubst]
      split_ifs
      all_goals (first | rfl | (congr 1; omega) | omega)
  | arr A B ihA ihB => simp only [tyShift, ihA, ihB]
  | all A ih => simp only [tyShift, ih]

private theorem tyShift_add {d₁ d₂ c : ℕ} {A : Ty} :
    tyShift d₁ c (tyShift d₂ c A) = tyShift (d₁ + d₂) c A := by
  induction A generalizing c with
  | var k =>
      simp only [tyShift, tySubst]
      split_ifs
      all_goals (try simp only [tyShift, tySubst])
      all_goals (try split_ifs)
      all_goals (first | rfl | (congr 1; omega) | omega)
  | arr A B ihA ihB => simp only [tyShift, ihA, ihB]
  | all A ih => simp only [tyShift, ih]

private theorem tyShift_comm {d d' c c' : ℕ} {A : Ty} (h : c' ≤ c) :
    tyShift d (c + d') (tyShift d' c' A) = tyShift d' c' (tyShift d c A) := by
  induction A generalizing c c' with
  | var k =>
      simp only [tyShift, tySubst]
      split_ifs
      all_goals (try simp only [tyShift, tySubst])
      all_goals (try split_ifs)
      all_goals (first | rfl | (congr 1; omega) | omega)
  | arr A B ihA ihB => simp only [tyShift, ihA h, ihB h]
  | all A ih =>
      simp only [tyShift]
      have h1 : c + d' + 1 = c + 1 + d' := by omega
      rw [h1, ih (show c' + 1 ≤ c + 1 by omega)]

private theorem tySubst_tyShift_cancel {c : ℕ} {S A : Ty} :
    tySubst c S (tyShift 1 c A) = A := by
  induction A generalizing c S with
  | var k =>
      simp only [tyShift, tySubst]
      split_ifs
      all_goals (try simp only [tyShift, tySubst])
      all_goals (try split_ifs)
      all_goals (first | rfl | (congr 1; omega) | omega)
  | arr A B ihA ihB => simp only [tyShift, tySubst, ihA, ihB]
  | all A ih => simp only [tyShift, tySubst, ih]

private theorem tySubst_tyShift_add {j' c : ℕ} {Y S₀ : Ty} :
    tySubst (j' + c) Y (tyShift (j' + 1) c S₀) = tyShift j' c S₀ := by
  induction S₀ generalizing j' c Y with
  | var k =>
      simp only [tyShift, tySubst]
      split_ifs
      all_goals (try simp only [tyShift, tySubst])
      all_goals (try split_ifs)
      all_goals (first | rfl | (congr 1; omega) | omega)
  | arr A B ihA ihB => simp only [tyShift, tySubst, ihA, ihB]
  | all A ih =>
      simp only [tyShift, tySubst]
      have h1 : j' + c + 1 = j' + (c + 1) := by omega
      rw [h1, ih]

private theorem tyShift_tySubst {d c j : ℕ} {S A : Ty} (h : c ≤ j) :
    tyShift d c (tySubst j S A) = tySubst (j + d) (tyShift d c S) (tyShift d c A) := by
  induction A generalizing c j d S with
  | var k =>
      simp only [tyShift, tySubst]
      split_ifs
      all_goals (try simp only [tyShift, tySubst])
      all_goals (try split_ifs)
      all_goals (first | rfl | (congr 1; omega) | omega)
  | arr A B ihA ihB => simp only [tyShift, tySubst, ihA h, ihB h]
  | all A ih =>
      simp only [tyShift, tySubst]
      rw [ih (show c + 1 ≤ j + 1 by omega)]
      have hS : tyShift d (c + 1) (tyShift 1 0 S) = tyShift 1 0 (tyShift d c S) :=
        tyShift_comm (d := d) (d' := 1) (c := c) (c' := 0) (A := S) (Nat.zero_le c)
      have hidx : j + 1 + d = j + d + 1 := by omega
      rw [hS, hidx]

private theorem tyShift_tySubst_le {c j : ℕ} {S T : Ty} (h : j ≤ c) :
    tyShift 1 c (tySubst j S T)
      = tySubst j (tyShift 1 c S) (tyShift 1 (c + 1) T) := by
  induction T generalizing c j S with
  | var k =>
      simp only [tyShift, tySubst]
      split_ifs
      all_goals (try simp only [tyShift, tySubst])
      all_goals (try split_ifs)
      all_goals (first | rfl | (congr 1; omega) | omega)
  | arr A B ihA ihB => simp only [tyShift, tySubst, ihA h, ihB h]
  | all A ih =>
      simp only [tyShift, tySubst]
      rw [ih (show j + 1 ≤ c + 1 by omega)]
      have hS : tyShift 1 (c + 1) (tyShift 1 0 S)
          = tyShift 1 0 (tyShift 1 c S) :=
        tyShift_comm (d := 1) (d' := 1) (c := c) (c' := 0) (A := S) (Nat.zero_le c)
      rw [hS]

private theorem tySubst_tyShift_add_zero {j' : ℕ} {Y S₀ : Ty} :
    tySubst j' Y (tyShift (j' + 1) 0 S₀) = tyShift j' 0 S₀ := by
  have h := tySubst_tyShift_add (j' := j') (c := 0) (Y := Y) (S₀ := S₀)
  simpa using h

private theorem tySubst_tySubst {j' j : ℕ} {S S' T : Ty} (h : j' ≤ j) :
    tySubst j (tyShift j' 0 S) (tySubst j' S' T)
      = tySubst j' (tySubst j (tyShift j' 0 S) S')
          (tySubst (j + 1) (tyShift (j' + 1) 0 S) T) := by
  induction T generalizing j' j S S' with
  | var k =>
      simp only [tyShift, tySubst]
      split_ifs
      all_goals (try simp only [tyShift, tySubst])
      all_goals (try split_ifs)
      all_goals (try simp only [tyShift, tySubst])
      all_goals (try split_ifs)
      all_goals (try simp only [tySubst_tyShift_add_zero])
      all_goals (first | rfl | (congr 1; omega) | omega)
  | arr A B ihA ihB => simp only [tyShift, tySubst, ihA h, ihB h]
  | all T₀ ih =>
      have hadd1 : tyShift 1 0 (tyShift j' 0 S) = tyShift (j' + 1) 0 S := by
        have h0 := tyShift_add (d₁ := 1) (d₂ := j') (c := 0) (A := S)
        have e : 1 + j' = j' + 1 := by omega
        rwa [e] at h0
      have hadd2 : tyShift 1 0 (tyShift (j' + 1) 0 S) = tyShift (j' + 2) 0 S := by
        have h0 := tyShift_add (d₁ := 1) (d₂ := j' + 1) (c := 0) (A := S)
        have e : 1 + (j' + 1) = j' + 2 := by omega
        rwa [e] at h0
      have hM : tyShift 1 0 (tySubst j (tyShift j' 0 S) S')
          = tySubst (j + 1) (tyShift (j' + 1) 0 S) (tyShift 1 0 S') := by
        have h0 := tyShift_tySubst (d := 1) (c := 0) (j := j)
          (S := tyShift j' 0 S) (A := S') (Nat.zero_le j)
        rwa [hadd1] at h0
      simp only [tyShift, tySubst]
      rw [hadd1, hadd2, hM]
      rw [ih (j' := j' + 1) (j := j + 1) (S := S) (S' := tyShift 1 0 S')
        (show j' + 1 ≤ j + 1 by omega)]

private theorem TyWf_tyShift {Δ c d : ℕ} {A : Ty} (h : TyWf Δ A) (hc : c ≤ Δ) :
    TyWf (Δ + d) (tyShift d c A) := by
  induction A generalizing Δ c d with
  | var k =>
      simp only [tyShift]
      split_ifs
      all_goals (simp only [TyWf] at h ⊢)
      all_goals omega
  | arr A B ihA ihB =>
      simp only [tyShift, TyWf] at h ⊢
      exact ⟨ihA h.1 hc, ihB h.2 hc⟩
  | all A ih =>
      simp only [tyShift, TyWf] at h ⊢
      have h1 : Δ + d + 1 = Δ + 1 + d := by omega
      rw [h1]
      exact ih h (show c + 1 ≤ Δ + 1 by omega)

private theorem TyWf_tySubst {Δ j : ℕ} {T S : Ty} (hT : TyWf (Δ + 1) T)
    (hj : j ≤ Δ) (hS : TyWf Δ S) : TyWf Δ (tySubst j S T) := by
  induction T generalizing Δ j S with
  | var k =>
      simp only [tySubst]
      split_ifs
      all_goals (simp only [TyWf] at hT ⊢)
      all_goals (first | assumption | omega)
  | arr A B ihA ihB =>
      simp only [tySubst, TyWf] at hT ⊢
      exact ⟨ihA hT.1 hj hS, ihB hT.2 hj hS⟩
  | all A ih =>
      simp only [tySubst, TyWf] at hT ⊢
      have hS' : TyWf (Δ + 1) (tyShift 1 0 S) := TyWf_tyShift hS (Nat.zero_le Δ)
      exact ih hT (show j + 1 ≤ Δ + 1 by omega) hS'

private inductive CtxIns : ℕ → Ty → List Ty → List Ty → Prop
  | here {A : Ty} {Γ : List Ty} : CtxIns 0 A Γ (A :: Γ)
  | there {j : ℕ} {A B : Ty} {Γ Γ' : List Ty} :
      CtxIns j A Γ Γ' → CtxIns (j + 1) A (B :: Γ) (B :: Γ')

private theorem ctxIns_lookup_lt {j : ℕ} {A : Ty} {Γ Γ' : List Ty}
    (h : CtxIns j A Γ Γ') : ∀ {k : ℕ}, k < j → Γ'[k]? = Γ[k]? := by
  induction h with
  | here => intro k hk; omega
  | there hctx ih =>
      intro k
      cases k with
      | zero => intro _; simp
      | succ k =>
          intro hk
          simp only [List.getElem?_cons_succ]
          exact ih (by omega)

private theorem ctxIns_lookup_eq {j : ℕ} {A : Ty} {Γ Γ' : List Ty}
    (h : CtxIns j A Γ Γ') : Γ'[j]? = some A := by
  induction h with
  | here => simp
  | there hctx ih => simp only [List.getElem?_cons_succ]; exact ih

private theorem ctxIns_lookup_gt {j : ℕ} {A : Ty} {Γ Γ' : List Ty}
    (h : CtxIns j A Γ Γ') : ∀ {k : ℕ}, j < k → Γ'[k]? = Γ[k - 1]? := by
  induction h with
  | here =>
      intro k
      cases k with
      | zero => intro hk; omega
      | succ k => intro _; simp only [List.getElem?_cons_succ, Nat.add_sub_cancel]
  | there hctx ih =>
      rename_i j A B Γ Γ'
      intro k
      cases k with
      | zero => intro hk; omega
      | succ k =>
          cases k with
          | zero => intro hk; omega
          | succ k =>
              intro hk
              simp only [List.getElem?_cons_succ, Nat.add_sub_cancel]
              have e : k + 1 - 1 = k := by omega
              have ih' := ih (k := k + 1) (by omega)
              rw [e] at ih'
              exact ih'

private theorem ctxIns_map {j : ℕ} {A : Ty} {Γ Γ' : List Ty}
    (h : CtxIns j A Γ Γ') (f : Ty → Ty) :
    CtxIns j (f A) (Γ.map f) (Γ'.map f) := by
  induction h with
  | here => exact CtxIns.here
  | there hctx ih => exact CtxIns.there ih

private theorem weaken_term {Δ : ℕ} {Γ : List Ty} {t : Tm} {T : Ty}
    (h : HasType Δ Γ t T) :
    ∀ {j : ℕ} {A : Ty} {Γ' : List Ty},
      CtxIns j A Γ Γ' → HasType Δ Γ' (tmShift 1 j t) T := by
  induction h with
  | var hlook hwf =>
      rename_i Δ Γ k T
      intro j A Γ' hctx
      simp only [tmShift]
      split_ifs with hk
      · refine HasType.var ?_ hwf
        rw [ctxIns_lookup_lt hctx (k := k) hk]
        exact hlook
      · refine HasType.var ?_ hwf
        have h1 := ctxIns_lookup_gt hctx (k := k + 1) (by omega)
        rw [h1]
        have e : k + 1 - 1 = k := by omega
        rw [e]
        exact hlook
  | lam hA h ih =>
      rename_i Δ Γ A B t
      intro j A' Γ' hctx
      simp only [tmShift]
      refine HasType.lam hA ?_
      exact ih (CtxIns.there hctx)
  | app h1 h2 ih1 ih2 =>
      rename_i Δ Γ A B t u
      intro j A' Γ' hctx
      simp only [tmShift]
      exact HasType.app (ih1 hctx) (ih2 hctx)
  | tlam h ih =>
      rename_i Δ Γ T t
      intro j A' Γ' hctx
      simp only [tmShift]
      refine HasType.tlam ?_
      exact ih (ctxIns_map hctx (tyShift 1 0))
  | tapp h hS ih =>
      rename_i Δ Γ T t S
      intro j A' Γ' hctx
      simp only [tmShift]
      exact HasType.tapp (ih hctx) hS

private theorem weaken_ty {Δ : ℕ} {Γ : List Ty} {t : Tm} {T : Ty}
    (h : HasType Δ Γ t T) :
    ∀ {c : ℕ}, c ≤ Δ →
      HasType (Δ + 1) (Γ.map (tyShift 1 c)) (tmTyShift 1 c t) (tyShift 1 c T) := by
  induction h with
  | var hlook hwf =>
      rename_i Δ Γ k T
      intro c hc
      simp only [tmTyShift]
      refine HasType.var ?_ (TyWf_tyShift hwf hc)
      simp [List.getElem?_map, hlook]
  | lam hA h ih =>
      rename_i Δ Γ A B t
      intro c hc
      simp only [tmTyShift, tyShift]
      refine HasType.lam (TyWf_tyShift hA hc) ?_
      exact ih hc
  | app h1 h2 ih1 ih2 =>
      rename_i Δ Γ A B t u
      intro c hc
      simp only [tmTyShift]
      exact HasType.app (ih1 hc) (ih2 hc)
  | tlam h ih =>
      rename_i Δ Γ T t
      intro c hc
      simp only [tmTyShift, tyShift]
      refine HasType.tlam ?_
      have hctx : (Γ.map (tyShift 1 c)).map (tyShift 1 0)
          = (Γ.map (tyShift 1 0)).map (tyShift 1 (c + 1)) := by
        rw [List.map_map, List.map_map]
        congr 1
        ext X
        simp only [Function.comp_apply]
        exact (tyShift_comm (d := 1) (d' := 1) (c := c) (c' := 0) (A := X)
          (Nat.zero_le c)).symm
      rw [hctx]
      exact ih (c := c + 1) (by omega)
  | tapp h hS ih =>
      rename_i Δ Γ T t S
      intro c hc
      simp only [tmTyShift]
      have hTy : tyShift 1 c (tySubst 0 S T)
          = tySubst 0 (tyShift 1 c S) (tyShift 1 (c + 1) T) :=
        tyShift_tySubst_le (Nat.zero_le c)
      rw [hTy]
      exact HasType.tapp (ih hc) (TyWf_tyShift hS hc)

private theorem tmSubst_typing {Δ : ℕ} {Γ' : List Ty} {t : Tm} {B : Ty}
    (h : HasType Δ Γ' t B) :
    ∀ {j : ℕ} {A : Ty} {Γ : List Ty} {u : Tm},
      CtxIns j A Γ Γ' → HasType Δ Γ u A →
        HasType Δ Γ (tmSubst j u t) B := by
  induction h with
  | var hlook hwf =>
      rename_i Δ Γ' k T
      intro j A Γ u hctx hu
      simp only [tmSubst]
      split_ifs with h1 h2
      · refine HasType.var ?_ hwf
        rw [← ctxIns_lookup_lt hctx (k := k) h1]
        exact hlook
      · rw [h2] at hlook
        have heq := ctxIns_lookup_eq hctx
        have hEq : some T = some A := hlook.symm.trans heq
        injection hEq with hTA
        subst hTA
        exact hu
      · refine HasType.var ?_ hwf
        have h1' := ctxIns_lookup_gt hctx (k := k) (by omega)
        rw [← h1']
        exact hlook
  | lam hA h ih =>
      rename_i Δ Γ' A B t
      intro j A₀ Γ u hctx hu
      simp only [tmSubst]
      refine HasType.lam hA ?_
      exact ih (CtxIns.there hctx) (weaken_term hu CtxIns.here)
  | app h1 h2 ih1 ih2 =>
      rename_i Δ Γ' A B t u
      intro j A₀ Γ s hctx hu
      simp only [tmSubst]
      exact HasType.app (ih1 hctx hu) (ih2 hctx hu)
  | tlam h ih =>
      rename_i Δ Γ' T t
      intro j A₀ Γ s hctx hu
      simp only [tmSubst]
      refine HasType.tlam ?_
      exact ih (ctxIns_map hctx (tyShift 1 0))
        (weaken_ty hu (Nat.zero_le Δ))
  | tapp h hS ih =>
      rename_i Δ Γ' T t S
      intro j A₀ Γ s hctx hu
      simp only [tmSubst]
      exact HasType.tapp (ih hctx hu) hS

private theorem tmTySubst_typing {L : ℕ} {Γ' : List Ty} {t : Tm} {T : Ty}
    (h : HasType L Γ' t T) :
    ∀ {Δ : ℕ}, L = Δ + 1 → ∀ {S : Ty}, TyWf Δ S → ∀ {j : ℕ}, j ≤ Δ →
      HasType Δ (Γ'.map (tySubst j S)) (tmTySubst j S t) (tySubst j S T) := by
  induction h with
  | var hlook hwf =>
      rename_i L Γ' k T
      intro Δ hL S hS j hj
      subst hL
      simp only [tmTySubst]
      refine HasType.var ?_ (TyWf_tySubst hwf hj hS)
      simp [List.getElem?_map, hlook]
  | lam hA h ih =>
      rename_i L Γ' A B t
      intro Δ hL S hS j hj
      subst hL
      simp only [tmTySubst, tySubst]
      refine HasType.lam (TyWf_tySubst hA hj hS) ?_
      exact ih rfl hS hj
  | app h1 h2 ih1 ih2 =>
      rename_i L Γ' A B t u
      intro Δ hL S hS j hj
      subst hL
      simp only [tmTySubst, tySubst]
      exact HasType.app (ih1 rfl hS hj) (ih2 rfl hS hj)
  | tlam h ih =>
      rename_i L Γ' T t
      intro Δ hL S hS j hj
      subst hL
      simp only [tmTySubst, tySubst]
      refine HasType.tlam ?_
      have hctx : ((Γ'.map (tySubst j S)).map (tyShift 1 0))
          = ((Γ'.map (tyShift 1 0)).map (tySubst (j + 1) (tyShift 1 0 S))) := by
        rw [List.map_map, List.map_map]
        congr 1
        ext X
        simp only [Function.comp_apply]
        exact tyShift_tySubst (c := 0) (j := j) (d := 1) (S := S) (A := X)
          (Nat.zero_le j)
      rw [hctx]
      exact ih rfl (TyWf_tyShift hS (Nat.zero_le Δ)) (show j + 1 ≤ Δ + 1 by omega)
  | tapp h hS' ih =>
      rename_i L Γ' T t S'
      intro Δ hL S hS j hj
      subst hL
      simp only [tmTySubst]
      have hTy : tySubst j S (tySubst 0 S' T)
          = tySubst 0 (tySubst j S S') (tySubst (j + 1) (tyShift 1 0 S) T) := by
        have h0 := tySubst_tySubst (j' := 0) (j := j) (S := S) (S' := S')
          (T := T) (Nat.zero_le j)
        simpa [tyShift_zero] using h0
      rw [hTy]
      exact HasType.tapp (ih rfl hS hj) (TyWf_tySubst hS' hj hS)

private theorem subject_reduction_aux {t t' : Tm} (hstep : Step t t') :
    ∀ {Δ : ℕ} {Γ : List Ty} {T : Ty},
      HasType Δ Γ t T → HasType Δ Γ t' T := by
  induction hstep with
  | beta =>
      rename_i A t u
      intro Δ Γ T h
      cases h with
      | app h1 h2 =>
          cases h1 with
          | lam hA hbody =>
              exact tmSubst_typing hbody CtxIns.here h2
  | tbeta =>
      rename_i t S
      intro Δ Γ T h
      cases h with
      | tapp h1 hS =>
          cases h1 with
          | tlam hbody =>
              have hmain := tmTySubst_typing hbody rfl hS (Nat.zero_le Δ)
              have hctx : (Γ.map (tyShift 1 0)).map (tySubst 0 S) = Γ := by
                simp [List.map_map, Function.comp_def, tySubst_tyShift_cancel]
              rw [hctx] at hmain
              exact hmain
  | appL hstep ih =>
      rename_i t t' u
      intro Δ Γ T h
      cases h with
      | app h1 h2 => exact HasType.app (ih h1) h2
  | appR hstep ih =>
      rename_i t u u'
      intro Δ Γ T h
      cases h with
      | app h1 h2 => exact HasType.app h1 (ih h2)
  | lam hstep ih =>
      rename_i A t t'
      intro Δ Γ T h
      cases h with
      | lam hA hbody => exact HasType.lam hA (ih hbody)
  | tlam hstep ih =>
      rename_i t t'
      intro Δ Γ T h
      cases h with
      | tlam hbody => exact HasType.tlam (ih hbody)
  | tapp hstep ih =>
      rename_i t t' S
      intro Δ Γ T h
      cases h with
      | tapp h1 hS => exact HasType.tapp (ih h1) hS

/-- Subject reduction: full beta reduction preserves System F
types. (The strong-normalization half of roadmap package VER-21
remains open; this is its subject-reduction deliverable.) -/
theorem subject_reduction {Δ : ℕ} {Γ : List Ty} {t t' : Tm}
    {T : Ty} (h : HasType Δ Γ t T) (hstep : Step t t') :
    HasType Δ Γ t' T := by
  exact subject_reduction_aux hstep h
