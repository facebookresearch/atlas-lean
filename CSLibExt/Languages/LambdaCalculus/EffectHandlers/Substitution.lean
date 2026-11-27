/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.EffectHandlers.Basic
public import CSLibExt.Languages.TypeSafety

/-!
# Renaming, weakening and substitution for the effect-handler calculus

For the typing judgments of `CSLibExt.Languages.LambdaCalculus.EffectHandlers.Basic`, on values,
computations and operation clauses: typed renaming, weakening by a block of innermost
variables, typed parallel substitution, single instantiation (`c[v/x]`, and its value twin), and
double instantiation (`c[v/x, κ/k]`, the instantiation of an operation clause by the
handler rule). The structural-typing interface `TypeSafety.StructuralTyping` of the type-safety
schema holds for the calculus with values and computations packaged as one sort of terms
(`structuralTyping`).

## References

* M. Pretnar, *An Introduction to Algebraic Effects and Handlers*, ENTCS 319 (MFPS XXXI), 2015,
  §§3 and 4 (Figs. 5 and 6).
* A. Bauer and M. Pretnar, *An effect system for algebraic effects and handlers*, Logical
  Methods in Computer Science 10(4), 2014, Theorem 4.1.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Languages.LambdaCalculus.EffectHandlers

universe u

variable {Op : Type u} [DecidableEq Op] {sig : Op → VTy Op × VTy Op}

/-! ### Renaming and weakening -/

omit [DecidableEq Op] in
/-- Lifting a renaming past a new innermost variable of type `A` keeps the context condition of
renaming. -/
private theorem liftRen_getElem? {Γ Γ' : List (VTy Op)} {ρ : ℕ → ℕ}
    (hρ : ∀ i T, Γ[i]? = some T → Γ'[ρ i]? = some T) (A : VTy Op) :
    ∀ i T, (A :: Γ)[i]? = some T → (A :: Γ')[References.Term.liftRen ρ i]? = some T := by
  intro i T h
  cases i with
  | zero => exact h
  | succ i => exact hρ i T h

omit [DecidableEq Op] in
/-- Renaming operation clauses keeps their labels. -/
private theorem map_fst_clausesRen (ρ : ℕ → ℕ) (cls : List (Op × Comp Op)) :
    (Clauses.ren ρ cls).map Prod.fst = cls.map Prod.fst := by
  induction cls with
  | nil => rfl
  | cons p cls ih =>
    obtain ⟨o, c⟩ := p
    simp only [Clauses.ren, List.map_cons, ih]

mutual

/-- **Renaming preserves the typing of values.** Let `ρ` be a renaming of de Bruijn indices such
that whenever `Γ` assigns the type `T` to the variable `i`, the context `Γ'` assigns `T` to
`ρ i`. If `Γ ⊢ v : A`, then `Γ' ⊢ v.ren ρ : A`. -/
theorem HasVTy.ren {Γ Γ' : List (VTy Op)} {v : Val Op} {A : VTy Op} (h : HasVTy sig Γ v A)
    {ρ : ℕ → ℕ} (hρ : ∀ i T, Γ[i]? = some T → Γ'[ρ i]? = some T) :
    HasVTy sig Γ' (v.ren ρ) A := by
  cases h with
  | var hi => exact .var (hρ _ _ hi)
  | unit => exact .unit
  | tt => exact .tt
  | ff => exact .ff
  | lam hc => exact .lam (HasCTy.ren hc (liftRen_getElem? hρ _))
  | hdl hr hcls hΔ =>
    refine .hdl (HasCTy.ren hr (liftRen_getElem? hρ _)) (HasClauses.ren hcls hρ) ?_
    change _ \ ((Clauses.ren ρ _).map Prod.fst).toFinset ⊆ _
    rw [map_fst_clausesRen]
    exact hΔ

/-- **Renaming preserves the typing of computations.** Let `ρ` be a renaming of de Bruijn
indices such that whenever `Γ` assigns the type `T` to the variable `i`, the context `Γ'`
assigns `T` to `ρ i`. If `Γ ⊢ c : C`, then `Γ' ⊢ c.ren ρ : C`. -/
theorem HasCTy.ren {Γ Γ' : List (VTy Op)} {c : Comp Op} {C : CTy Op} (h : HasCTy sig Γ c C)
    {ρ : ℕ → ℕ} (hρ : ∀ i T, Γ[i]? = some T → Γ'[ρ i]? = some T) :
    HasCTy sig Γ' (c.ren ρ) C := by
  cases h with
  | ret hv => exact .ret (HasVTy.ren hv hρ)
  | op ho hv => exact .op ho (HasVTy.ren hv hρ)
  | bind h₁ h₂ => exact .bind (HasCTy.ren h₁ hρ) (HasCTy.ren h₂ (liftRen_getElem? hρ _))
  | ite hv h₁ h₂ => exact .ite (HasVTy.ren hv hρ) (HasCTy.ren h₁ hρ) (HasCTy.ren h₂ hρ)
  | app hv hw => exact .app (HasVTy.ren hv hρ) (HasVTy.ren hw hρ)
  | handle hh hc => exact .handle (HasVTy.ren hh hρ) (HasCTy.ren hc hρ)

/-- **Renaming preserves the typing of operation clauses.** Let `ρ` be a renaming of de Bruijn
indices such that whenever `Γ` assigns the type `T` to the variable `i`, the context `Γ'`
assigns `T` to `ρ i`. If the clauses `cls` have type `B ! Δ'` in `Γ`, then the renamed clauses
`Clauses.ren ρ cls` have type `B ! Δ'` in `Γ'`. -/
theorem HasClauses.ren {Γ Γ' : List (VTy Op)} {cls : List (Op × Comp Op)} {B : VTy Op}
    {Δ' : Finset Op} (h : HasClauses sig Γ cls B Δ') {ρ : ℕ → ℕ}
    (hρ : ∀ i T, Γ[i]? = some T → Γ'[ρ i]? = some T) :
    HasClauses sig Γ' (Clauses.ren ρ cls) B Δ' := by
  cases h with
  | nil => exact .nil
  | cons hc hcls =>
    exact .cons (HasCTy.ren hc (liftRen_getElem? (liftRen_getElem? hρ _) _))
      (HasClauses.ren hcls hρ)

end

/-- **Weakening for values.** If `Γ ⊢ v : A`, then for every block `Θ` of new innermost
variables, `v` with every free variable shifted up by the length of `Θ` has type `A` in
`Θ ++ Γ`. -/
theorem HasVTy.weaken {Γ : List (VTy Op)} {v : Val Op} {A : VTy Op} (Θ : List (VTy Op))
    (h : HasVTy sig Γ v A) : HasVTy sig (Θ ++ Γ) (v.ren (· + Θ.length)) A := by
  refine HasVTy.ren h fun i T hi => ?_
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel]
  exact hi

/-- **Weakening for computations.** If `Γ ⊢ c : C`, then for every block `Θ` of new innermost
variables, `c` with every free variable shifted up by the length of `Θ` has type `C` in
`Θ ++ Γ`. -/
theorem HasCTy.weaken {Γ : List (VTy Op)} {c : Comp Op} {C : CTy Op} (Θ : List (VTy Op))
    (h : HasCTy sig Γ c C) : HasCTy sig (Θ ++ Γ) (c.ren (· + Θ.length)) C := by
  refine HasCTy.ren h fun i T hi => ?_
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel]
  exact hi

/-! ### Substitution and instantiation -/

/-- Lifting a substitution past a new innermost variable of type `A` keeps the typing condition
of substitution. -/
private theorem liftSub_typed {Γ Γ' : List (VTy Op)} {σ : ℕ → Val Op}
    (hσ : ∀ i T, Γ[i]? = some T → HasVTy sig Γ' (σ i) T) (A : VTy Op) :
    ∀ i T, (A :: Γ)[i]? = some T → HasVTy sig (A :: Γ') (liftSub σ i) T := by
  intro i T h
  cases i with
  | zero => exact .var h
  | succ i => exact HasVTy.weaken [A] (hσ i T h)

omit [DecidableEq Op] in
/-- Substituting into operation clauses keeps their labels. -/
private theorem map_fst_clausesSubst (σ : ℕ → Val Op) (cls : List (Op × Comp Op)) :
    (Clauses.subst σ cls).map Prod.fst = cls.map Prod.fst := by
  induction cls with
  | nil => rfl
  | cons p cls ih =>
    obtain ⟨o, c⟩ := p
    simp only [Clauses.subst, List.map_cons, ih]

/-- The substitution `singleSub v` sends the variables of `A :: Γ` to values typed in `Γ`. -/
private theorem singleSub_typed {Γ : List (VTy Op)} {v : Val Op} {A : VTy Op}
    (hv : HasVTy sig Γ v A) :
    ∀ i T, (A :: Γ)[i]? = some T → HasVTy sig Γ (singleSub v i) T := by
  intro i T h
  cases i with
  | zero =>
    cases h
    exact hv
  | succ i => exact .var h

/-- The substitution `doubleSub x k` sends the variables of `K :: A :: Γ` to values typed in
`Γ`. -/
private theorem doubleSub_typed {Γ : List (VTy Op)} {x k : Val Op} {A K : VTy Op}
    (hx : HasVTy sig Γ x A) (hk : HasVTy sig Γ k K) :
    ∀ i T, (K :: A :: Γ)[i]? = some T → HasVTy sig Γ (doubleSub x k i) T := by
  intro i T h
  match i, h with
  | 0, h =>
    cases h
    exact hk
  | 1, h =>
    cases h
    exact hx
  | i + 2, h => exact .var h

mutual

/-- **Parallel substitution preserves the typing of values.** Let `σ` be a substitution such
that whenever `Γ` assigns the type `T` to the variable `i`, the value `σ i` has type `T` in
`Γ'`. If `Γ ⊢ v : A`, then `Γ' ⊢ v.subst σ : A`. -/
theorem HasVTy.subst {Γ Γ' : List (VTy Op)} {v : Val Op} {A : VTy Op} (h : HasVTy sig Γ v A)
    {σ : ℕ → Val Op} (hσ : ∀ i T, Γ[i]? = some T → HasVTy sig Γ' (σ i) T) :
    HasVTy sig Γ' (v.subst σ) A := by
  cases h with
  | var hi => exact hσ _ _ hi
  | unit => exact .unit
  | tt => exact .tt
  | ff => exact .ff
  | lam hc => exact .lam (HasCTy.subst hc (liftSub_typed hσ _))
  | hdl hr hcls hΔ =>
    refine .hdl (HasCTy.subst hr (liftSub_typed hσ _)) (HasClauses.subst hcls hσ) ?_
    change _ \ ((Clauses.subst σ _).map Prod.fst).toFinset ⊆ _
    rw [map_fst_clausesSubst]
    exact hΔ

/-- **Parallel substitution preserves the typing of computations.** Let `σ` be a substitution
such that whenever `Γ` assigns the type `T` to the variable `i`, the value `σ i` has type `T` in
`Γ'`. If `Γ ⊢ c : C`, then `Γ' ⊢ c.subst σ : C`. -/
theorem HasCTy.subst {Γ Γ' : List (VTy Op)} {c : Comp Op} {C : CTy Op} (h : HasCTy sig Γ c C)
    {σ : ℕ → Val Op} (hσ : ∀ i T, Γ[i]? = some T → HasVTy sig Γ' (σ i) T) :
    HasCTy sig Γ' (c.subst σ) C := by
  cases h with
  | ret hv => exact .ret (HasVTy.subst hv hσ)
  | op ho hv => exact .op ho (HasVTy.subst hv hσ)
  | bind h₁ h₂ => exact .bind (HasCTy.subst h₁ hσ) (HasCTy.subst h₂ (liftSub_typed hσ _))
  | ite hv h₁ h₂ => exact .ite (HasVTy.subst hv hσ) (HasCTy.subst h₁ hσ) (HasCTy.subst h₂ hσ)
  | app hv hw => exact .app (HasVTy.subst hv hσ) (HasVTy.subst hw hσ)
  | handle hh hc => exact .handle (HasVTy.subst hh hσ) (HasCTy.subst hc hσ)

/-- **Parallel substitution preserves the typing of operation clauses.** Let `σ` be a
substitution such that whenever `Γ` assigns the type `T` to the variable `i`, the value `σ i`
has type `T` in `Γ'`. If the clauses `cls` have type `B ! Δ'` in `Γ`, then
`Clauses.subst σ cls` have type `B ! Δ'` in `Γ'`. -/
theorem HasClauses.subst {Γ Γ' : List (VTy Op)} {cls : List (Op × Comp Op)} {B : VTy Op}
    {Δ' : Finset Op} (h : HasClauses sig Γ cls B Δ') {σ : ℕ → Val Op}
    (hσ : ∀ i T, Γ[i]? = some T → HasVTy sig Γ' (σ i) T) :
    HasClauses sig Γ' (Clauses.subst σ cls) B Δ' := by
  cases h with
  | nil => exact .nil
  | cons hc hcls =>
    exact .cons (HasCTy.subst hc (liftSub_typed (liftSub_typed hσ _) _))
      (HasClauses.subst hcls hσ)

end

/-- **Single instantiation for values.** If `w` has type `B` in `Γ` extended by an innermost
variable `x : A`, and `Γ ⊢ v : A`, then `Γ ⊢ w[v/x] : B`. -/
theorem HasVTy.inst {Γ : List (VTy Op)} {w v : Val Op} {A B : VTy Op}
    (hw : HasVTy sig (A :: Γ) w B) (hv : HasVTy sig Γ v A) : HasVTy sig Γ (w.inst v) B := by
  exact HasVTy.subst hw (singleSub_typed hv)

/-- **Single instantiation for computations.** If `c` has type `C` in `Γ` extended by an
innermost variable `x : A`, and `Γ ⊢ v : A`, then `Γ ⊢ c[v/x] : C`. This covers the steps for
application, `do` after `return`, and the return clause of a handler (Pretnar 2015, §3). -/
theorem HasCTy.inst {Γ : List (VTy Op)} {c : Comp Op} {v : Val Op} {A : VTy Op} {C : CTy Op}
    (hc : HasCTy sig (A :: Γ) c C) (hv : HasVTy sig Γ v A) : HasCTy sig Γ (c.inst v) C := by
  exact HasCTy.subst hc (singleSub_typed hv)

/-- **Double instantiation.** If `c` has type `C` in `Γ` extended by `x : A` (index `1`) and
`k : K` (index `0`), and `Γ ⊢ x' : A` and `Γ ⊢ k' : K`, then `Γ ⊢ c[x'/x, k'/k] : C`. With
`A = A_o`, `K = B_o → B ! Δ'` and `C = B ! Δ'` this types the instantiated operation clause of
the handler rule. -/
theorem HasCTy.inst₂ {Γ : List (VTy Op)} {c : Comp Op} {x k : Val Op} {A K : VTy Op}
    {C : CTy Op} (hc : HasCTy sig (K :: A :: Γ) c C) (hx : HasVTy sig Γ x A)
    (hk : HasVTy sig Γ k K) : HasCTy sig Γ (c.inst₂ x k) C := by
  exact HasCTy.subst hc (doubleSub_typed hx hk)

/-! ### The structural-typing interface -/

/-- **Typing of packaged terms.** A value has a value type and a computation has a computation
type as in `HasVTy` and `HasCTy`; a value never has a computation type, nor a computation a
value type. Part of the packaging of the two sorts for `structuralTyping`. -/
def HasT (sig : Op → VTy Op × VTy Op) :
    List (VTy Op) → Val Op ⊕ Comp Op → VTy Op ⊕ CTy Op → Prop
  | Γ, .inl v, .inl A => HasVTy sig Γ v A
  | Γ, .inr c, .inr C => HasCTy sig Γ c C
  | _, .inl _, .inr _ => False
  | _, .inr _, .inl _ => False

/-- **Binding a variable of a packaged type.** Binding at a value type `A` adds an innermost
variable of type `A`; binding at a computation type leaves the context unchanged, since
fine-grain call-by-value has no computation variables. Part of the packaging of the two sorts
for `structuralTyping`. -/
def bindT (Γ : List (VTy Op)) (_ : Unit) : VTy Op ⊕ CTy Op → List (VTy Op)
  | .inl A => A :: Γ
  | .inr _ => Γ

/-- **Instantiating the bound variable of a packaged term.** Instantiating by a value `v`
substitutes `v` for index `0` of a value (`Val.inst`) or of a computation (`Comp.inst`);
instantiating by a computation, which binds nothing, is the identity. Part of the packaging of
the two sorts for `structuralTyping`. -/
def instT : Val Op ⊕ Comp Op → Unit → Val Op ⊕ Comp Op → Val Op ⊕ Comp Op
  | .inl w, _, .inl v => .inl (w.inst v)
  | .inr c, _, .inl v => .inr (c.inst v)
  | e, _, .inr _ => e

/-- **Weakening a packaged term.** For any two contexts `Γ` and `Γ'`, `wkT Γ Γ' t` shifts every
free variable of the value or computation `t` up by `Γ'.length - Γ.length`, the length of the
target context minus the length of the source context in truncated subtraction of natural
numbers: the shift is `0` when `Γ'` is not longer than `Γ`. Part of the packaging of the two
sorts for `structuralTyping`. -/
def wkT (Γ Γ' : List (VTy Op)) : Val Op ⊕ Comp Op → Val Op ⊕ Comp Op
  | .inl v => .inl (v.ren (· + (Γ'.length - Γ.length)))
  | .inr c => .inr (c.ren (· + (Γ'.length - Γ.length)))

/-- **The effect-handler calculus has the structural properties.** The interface
`TypeSafety.StructuralTyping` has one sort of terms, one sort of types and one kind of binder,
while fine-grain call-by-value has two sorts, values and computations, and only value
variables. The packaging into `Val Op ⊕ Comp Op` and `VTy Op ⊕ CTy Op` (`HasT`, `bindT`,
`instT`, `wkT`) exists to meet that single-sorted interface. The value branch carries the
content: binding at a value type `A` adds an innermost variable `x : A`, and instantiating by a
value `v` is the substitution `[v/x]` into a value or a computation, so the substitution field
is `HasVTy.inst` and `HasCTy.inst`. Binding at a computation type binds nothing and
instantiating by a computation is the identity; these branches hold trivially and only make the
operations total. A context `Γ` extends to `Θ ++ Γ` for a block `Θ` of new innermost variables;
for such an extension the shift `(Θ ++ Γ).length - Γ.length` of `wkT` is the length of `Θ`, and
weakening is `HasVTy.weaken` and `HasCTy.weaken`. -/
theorem structuralTyping :
    TypeSafety.StructuralTyping (HasT sig) bindT instT (fun Γ Γ' => ∃ Θ, Γ' = Θ ++ Γ) wkT := by
  refine ⟨?_, ?_⟩
  · intro Γ x A B e v he hv
    cases A with
    | inl A =>
      cases v with
      | inl v =>
        cases e with
        | inl w =>
          cases B with
          | inl B => exact HasVTy.inst he hv
          | inr B => cases he
        | inr c =>
          cases B with
          | inl B => cases he
          | inr B => exact HasCTy.inst he hv
      | inr c => cases hv
    | inr C =>
      cases v with
      | inl v => cases hv
      | inr c => cases e <;> exact he
  · rintro Γ Γ' t A ⟨Θ, rfl⟩ ht
    have hlen : (Θ ++ Γ).length - Γ.length = Θ.length := by simp
    cases t with
    | inl v =>
      cases A with
      | inl A =>
        change HasVTy sig (Θ ++ Γ) (v.ren (· + ((Θ ++ Γ).length - Γ.length))) A
        rw [hlen]
        exact HasVTy.weaken Θ ht
      | inr A => cases ht
    | inr c =>
      cases A with
      | inl A => cases ht
      | inr A =>
        change HasCTy sig (Θ ++ Γ) (c.ren (· + ((Θ ++ Γ).length - Γ.length))) A
        rw [hlen]
        exact HasCTy.weaken Θ ht

end Cslib.Languages.LambdaCalculus.EffectHandlers
