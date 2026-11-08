/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The simply typed lambda calculus with references: preservation and safety
-/
module

public import CSLibExt.Languages.LambdaCalculus.References.Progress

/-!
# Preservation and type safety

Pierce, *Types and Programming Languages*, Theorem 13.5.3 (preservation): if
`Γ | Σ ⊢ t : T`, `Γ | Σ ⊢ μ`, and `t | μ → t' | μ'`, then for some store
typing `Σ' ⊇ Σ`, `Γ | Σ' ⊢ t' : T` and `Γ | Σ' ⊢ μ'`. Store typings grow by
allocation, so `Σ ⊆ Σ'` is the prefix order `S <+: S'` on lists.

The proof uses TAPL's supporting lemmas: substitution (Lemma 13.5.4, here
derived from stability of typing under renamings and parallel substitutions
that respect the variable contexts), store update (Lemma 13.5.5: overwriting
a location with a value of its type keeps the store well typed), and store
weakening (Lemma 13.5.6: typing is stable under extension of the store
typing).

Type safety combines preservation with progress (Theorem 13.5.7): a closed
well-typed term evaluated in a well-typed store, in particular in the empty
store, never reaches a stuck configuration.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.References

universe u

variable {Base : Type u}

namespace HasType

/-- Typing is preserved by renamings that respect the variable contexts. -/
theorem rename {Γ Δ S : List (Ty Base)} {t : Term Base} {T : Ty Base}
    (h : HasType Γ S t T) {ρ : Nat → Nat}
    (hρ : ∀ x A, Γ[x]? = some A → Δ[ρ x]? = some A) :
    HasType Δ S (t.rename ρ) T := by
  induction h generalizing Δ ρ with
  | var hx => exact .var (hρ _ _ hx)
  | lam _ ih =>
      refine .lam (ih ?_)
      intro x A hx
      cases x with
      | zero => exact hx
      | succ x => exact hρ x A hx
  | app _ _ ihf iha => exact .app (ihf hρ) (iha hρ)
  | unit => exact .unit
  | loc hl => exact .loc hl
  | ref _ ih => exact .ref (ih hρ)
  | deref _ ih => exact .deref (ih hρ)
  | assign _ _ ih₁ ih₂ => exact .assign (ih₁ hρ) (ih₂ hρ)

/-- Weakening by one variable type at the front of the context. -/
theorem weaken {Γ S : List (Ty Base)} {t : Term Base} {T : Ty Base} (A : Ty Base)
    (h : HasType Γ S t T) : HasType (A :: Γ) S (t.rename Nat.succ) T :=
  h.rename fun _ _ hx => hx

/-- Typing is preserved by substitutions that send each variable to a term of
its type. -/
theorem subst {Γ Δ S : List (Ty Base)} {t : Term Base} {T : Ty Base}
    (h : HasType Γ S t T) {σ : Nat → Term Base}
    (hσ : ∀ x A, Γ[x]? = some A → HasType Δ S (σ x) A) :
    HasType Δ S (t.subst σ) T := by
  induction h generalizing Δ σ with
  | var hx => exact hσ _ _ hx
  | @lam _ _ T₁ _ _ _ ih =>
      refine .lam (ih ?_)
      intro x A hx
      cases x with
      | zero => exact .var hx
      | succ x => exact (hσ x A hx).weaken T₁
  | app _ _ ihf iha => exact .app (ihf hσ) (iha hσ)
  | unit => exact .unit
  | loc hl => exact .loc hl
  | ref _ ih => exact .ref (ih hσ)
  | deref _ ih => exact .deref (ih hσ)
  | assign _ _ ih₁ ih₂ => exact .assign (ih₁ hσ) (ih₂ hσ)

/-- Substitution for the innermost variable (TAPL Lemma 13.5.4). -/
theorem instantiate {Γ S : List (Ty Base)} {body s : Term Base} {A T : Ty Base}
    (hbody : HasType (A :: Γ) S body T) (hs : HasType Γ S s A) :
    HasType Γ S (body.instantiate s) T := by
  refine hbody.subst ?_
  intro x B hx
  cases x with
  | zero =>
      cases hx
      exact hs
  | succ x => exact .var hx

/-- Typing is preserved by extending the store typing (TAPL Lemma 13.5.6). -/
theorem extendStore {Γ S S' : List (Ty Base)} {t : Term Base} {T : Ty Base}
    (h : HasType Γ S t T) (hS : S <+: S') : HasType Γ S' t T := by
  induction h with
  | var hx => exact .var hx
  | lam _ ih => exact .lam (ih hS)
  | app _ _ ihf iha => exact .app (ihf hS) (iha hS)
  | unit => exact .unit
  | @loc _ S l _ hl =>
      obtain ⟨rest, rfl⟩ := hS
      refine .loc ?_
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1]
      exact hl
  | ref _ ih => exact .ref (ih hS)
  | deref _ ih => exact .deref (ih hS)
  | assign _ _ ih₁ ih₂ => exact .assign (ih₁ hS) (ih₂ hS)

end HasType

namespace StoreTyped

variable {Γ S : List (Ty Base)} {μ : Store Base}

/-- A well-typed store remains well typed when its entries are retyped under
an extended store typing. -/
theorem extendStore {S' : List (Ty Base)} (h : StoreTyped Γ S μ) (hS : S <+: S') :
    List.Forall₂ (fun v T => v.Value ∧ HasType Γ S' v T) μ S :=
  h.imp fun _ _ hv => ⟨hv.1, hv.2.extendStore hS⟩

/-- Allocation: appending a value of type `T` to a well-typed store gives a
store that is well typed under the store typing extended by `T`. -/
theorem append {v : Term Base} {T : Ty Base} (h : StoreTyped Γ S μ) (hval : v.Value)
    (hv : HasType Γ S v T) : StoreTyped Γ (S ++ [T]) (μ ++ [v]) :=
  List.rel_append (h.extendStore (List.prefix_append S [T]))
    (.cons ⟨hval, hv.extendStore (List.prefix_append S [T])⟩ .nil)

/-- Assignment: overwriting a location with a value of the type the store
typing assigns to it keeps the store well typed (TAPL Lemma 13.5.5). -/
theorem set {l : Nat} {v : Term Base} {T : Ty Base} (h : StoreTyped Γ S μ)
    (hl : S[l]? = some T) (hval : v.Value) (hv : HasType Γ S v T) :
    StoreTyped Γ S (μ.set l v) := by
  unfold StoreTyped at h ⊢
  suffices key : ∀ (μ₀ : Store Base) (S₀ : List (Ty Base)) (l : Nat),
      List.Forall₂ (fun v T => v.Value ∧ HasType Γ S v T) μ₀ S₀ → S₀[l]? = some T →
      List.Forall₂ (fun v T => v.Value ∧ HasType Γ S v T) (μ₀.set l v) S₀ from key μ S l h hl
  intro μ₀ S₀ l h₀ hl₀
  induction h₀ generalizing l with
  | nil => simp at hl₀
  | cons hhead _ ih =>
      cases l with
      | zero =>
          cases hl₀
          exact .cons ⟨hval, hv⟩ ‹_›
      | succ l => exact .cons hhead (ih l hl₀)

end StoreTyped

/-- Preservation (TAPL Theorem 13.5.3): a step from a well-typed configuration
leads to a configuration that is well typed, with the same type, under an
extension of the store typing. -/
theorem preservation {Γ S : List (Ty Base)} {t t' : Term Base} {μ μ' : Store Base}
    {T : Ty Base} (ht : HasType Γ S t T) (hμ : StoreTyped Γ S μ) (hstep : Step t μ t' μ') :
    ∃ S', S <+: S' ∧ HasType Γ S' t' T ∧ StoreTyped Γ S' μ' := by
  induction hstep generalizing T with
  | appLeft _ ih =>
      cases ht with
      | app hf ha =>
          obtain ⟨S', hS, hf', hμ'⟩ := ih hf hμ
          exact ⟨S', hS, .app hf' (ha.extendStore hS), hμ'⟩
  | appRight _ _ ih =>
      cases ht with
      | app hf ha =>
          obtain ⟨S', hS, ha', hμ'⟩ := ih ha hμ
          exact ⟨S', hS, .app (hf.extendStore hS) ha', hμ'⟩
  | appAbs _ =>
      cases ht with
      | app hf ha =>
          cases hf with
          | lam hbody => exact ⟨S, List.prefix_refl S, hbody.instantiate ha, hμ⟩
  | ref _ ih =>
      cases ht with
      | ref ht =>
          obtain ⟨S', hS, ht', hμ'⟩ := ih ht hμ
          exact ⟨S', hS, .ref ht', hμ'⟩
  | @refValue v μ hval =>
      cases ht with
      | @ref _ _ _ T₀ hv =>
          refine ⟨S ++ [T₀], List.prefix_append S [T₀], .loc ?_, hμ.append hval hv⟩
          rw [hμ.length_eq]
          simp
  | deref _ ih =>
      cases ht with
      | deref ht =>
          obtain ⟨S', hS, ht', hμ'⟩ := ih ht hμ
          exact ⟨S', hS, .deref ht', hμ'⟩
  | derefLoc hl =>
      cases ht with
      | deref ht =>
          cases ht with
          | loc hlS =>
              obtain ⟨v, hv, _, hvT⟩ := hμ.exists_of_getElem? hlS
              rw [hl] at hv
              cases hv
              exact ⟨S, List.prefix_refl S, hvT, hμ⟩
  | assignLeft _ ih =>
      cases ht with
      | assign ht₁ ht₂ =>
          obtain ⟨S', hS, ht₁', hμ'⟩ := ih ht₁ hμ
          exact ⟨S', hS, .assign ht₁' (ht₂.extendStore hS), hμ'⟩
  | assignRight _ _ ih =>
      cases ht with
      | assign ht₁ ht₂ =>
          obtain ⟨S', hS, ht₂', hμ'⟩ := ih ht₂ hμ
          exact ⟨S', hS, .assign (ht₁.extendStore hS) ht₂', hμ'⟩
  | assignLoc hval _ =>
      cases ht with
      | assign ht₁ ht₂ =>
          cases ht₁ with
          | loc hlS => exact ⟨S, List.prefix_refl S, .unit, hμ.set hlS hval ht₂⟩

/-- Preservation along any number of evaluation steps. -/
theorem Steps.preservation {Γ S : List (Ty Base)} {t t' : Term Base}
    {μ μ' : Store Base} {T : Ty Base} (h : Steps t μ t' μ')
    (ht : HasType Γ S t T) (hμ : StoreTyped Γ S μ) :
    ∃ S', S <+: S' ∧ HasType Γ S' t' T ∧ StoreTyped Γ S' μ' := by
  suffices key : ∀ c : Term Base × Store Base,
      Relation.ReflTransGen (fun (c c' : Term Base × Store Base) => Step c.1 c.2 c'.1 c'.2)
        (t, μ) c →
      ∃ S', S <+: S' ∧ HasType Γ S' c.1 T ∧ StoreTyped Γ S' c.2 from key _ h
  intro c hc
  induction hc with
  | refl => exact ⟨S, List.prefix_refl S, ht, hμ⟩
  | tail _ hstep ih =>
      obtain ⟨S₁, hS₁, ht₁, hμ₁⟩ := ih
      obtain ⟨S₂, hS₂, ht₂, hμ₂⟩ := References.preservation ht₁ hμ₁ hstep
      exact ⟨S₂, hS₁.trans hS₂, ht₂, hμ₂⟩

/-- Type safety: a closed term that is well typed in a well-typed store never
evaluates to a stuck configuration; every reachable term is a value or can
step. -/
theorem typeSafety {S : List (Ty Base)} {t t' : Term Base} {μ μ' : Store Base}
    {T : Ty Base} (ht : HasType [] S t T) (hμ : StoreTyped [] S μ)
    (h : Steps t μ t' μ') : t'.Value ∨ ∃ t'' μ'', Step t' μ' t'' μ'' := by
  obtain ⟨S', _, ht', hμ'⟩ := h.preservation ht hμ
  exact progress ht' hμ'

/-- Type safety for programs: a closed term typed under the empty store typing,
run from the empty store, never gets stuck. -/
theorem typeSafety_empty {t t' : Term Base} {μ' : Store Base} {T : Ty Base}
    (ht : HasType [] [] t T) (h : Steps t [] t' μ') :
    t'.Value ∨ ∃ t'' μ'', Step t' μ' t'' μ'' :=
  typeSafety ht .nil h

end Cslib.Languages.LambdaCalculus.References
