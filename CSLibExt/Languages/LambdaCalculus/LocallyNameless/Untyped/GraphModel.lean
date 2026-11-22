/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
public import MathlibExt.Order.ScottContinuity.GraphModel

/-!
# The graph model `P(ω)` of the untyped λ-calculus

Scott's graph model (D. Scott, *Data types as lattices*, SIAM J. Comput. 5 (1976), §2)
interprets untyped λ-terms in `P(ω) = Set ℕ`: application is the graph-model application
`app u x` and λ-abstraction takes the graph of the (Scott-continuous) function a body denotes.
This file gives that interpretation for CSLib's locally nameless untyped terms
(`Cslib.LambdaCalculus.LocallyNameless.Untyped.Term`) and proves:

* `scottContinuous_denote`, `scottContinuous_denote_fvar`: every term denotes a Scott-continuous
  function of the values of its bound variables and of its free variables (Scott's continuity
  theorem, Theorem 2.1);
* `denote_eq_of_fullBeta`, `denote_eq_of_reflTransGen_fullBeta`: full β-reduction, including
  reduction under λ (the ξ-rule), preserves denotations (the β and ξ parts of Scott's conversion
  theorem, Theorem 2.2);
* `app_denote_Y`: the paradoxical combinator `Y` computes least fixed points (Scott's first
  recursion theorem, Theorem 2.5);
* `denote_K_ne_denote_KStar`: two closed normal forms, `λx.λy.x` and `λx.λy.y`, have different
  denotations, so the model is not trivial;
* `exists_denote_eta_ne`: the η-rule is *not* sound in `P(ω)`.

Free variables are interpreted by `ρ : Var → Set ℕ` and bound variables (de Bruijn indices) by
`bs : ℕ → Set ℕ`; a binder pushes a value onto `bs` (`consEnv`).
-/

@[expose] public section

namespace Cslib.LambdaCalculus.LocallyNameless.Untyped.GraphModel

open MathlibExt.Order.ScottContinuity.GraphModel
open Term (LcAt LC openRec fv Beta FullBeta lcAt_iff_LC)
open scoped Term

universe u

variable {Var : Type u}

/-- **Extending a bound-variable environment.** `consEnv v bs` sends index `0` to `v` and
`n + 1` to `bs n`: the environment under one more binder, bound to `v`. -/
def consEnv (v : Set ℕ) (bs : ℕ → Set ℕ) : ℕ → Set ℕ
  | 0 => v
  | n + 1 => bs n

@[simp] theorem consEnv_zero (v : Set ℕ) (bs : ℕ → Set ℕ) : consEnv v bs 0 = v := rfl

@[simp] theorem consEnv_succ (v : Set ℕ) (bs : ℕ → Set ℕ) (n : ℕ) :
    consEnv v bs (n + 1) = bs n := rfl

/-- **Denotation of an untyped λ-term in the graph model.** With free variables valued by `ρ`
and bound variables by `bs`, a bound variable denotes its value, an application `M N` denotes
`app ⟦M⟧ ⟦N⟧`, and an abstraction `λ.M` denotes the graph of `v ↦ ⟦M⟧` with the new bound
variable valued by `v` (D. Scott, *Data types as lattices*, SIAM J. Comput. 5 (1976), §2,
semantics of `u(x)` and `λx.τ`). -/
def denote (ρ : Var → Set ℕ) : Term Var → (ℕ → Set ℕ) → Set ℕ
  | .bvar i, bs => bs i
  | .fvar x, _ => ρ x
  | .abs M, bs => graph fun v => denote ρ M (consEnv v bs)
  | .app M N, bs => app (denote ρ M bs) (denote ρ N bs)

section Continuity

theorem scottContinuous_eval (i : ℕ) : ScottContinuous fun bs : ℕ → Set ℕ => bs i := by
  refine ScottContinuous.of_map_sSup fun d _ _ => ?_
  ext m
  simp [sSup_apply]

theorem scottContinuous_consEnv_right (v : Set ℕ) :
    ScottContinuous (consEnv v) := by
  refine ScottContinuous.of_map_sSup fun d hne _ => ?_
  funext n
  ext m
  cases n with
  | zero =>
    obtain ⟨b, hb⟩ := hne
    simp only [consEnv_zero, sSup_apply, Set.iSup_eq_iUnion, Set.mem_iUnion]
    constructor
    · intro hm
      exact ⟨⟨_, ⟨b, hb, rfl⟩⟩, hm⟩
    · rintro ⟨⟨_, ⟨c, _, rfl⟩⟩, hm⟩
      exact hm
  | succ n =>
    simp only [consEnv_succ, sSup_apply, Set.iSup_eq_iUnion, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨b, hb⟩, hm⟩
      exact ⟨⟨_, ⟨b, hb, rfl⟩⟩, hm⟩
    · rintro ⟨⟨_, ⟨b, hb, rfl⟩⟩, hm⟩
      exact ⟨⟨b, hb⟩, hm⟩

theorem scottContinuous_consEnv_left (bs : ℕ → Set ℕ) :
    ScottContinuous fun v => consEnv v bs := by
  refine ScottContinuous.of_map_sSup fun d hne _ => ?_
  funext n
  ext m
  cases n with
  | zero =>
    simp only [consEnv_zero, sSup_apply, Set.iSup_eq_iUnion, Set.mem_iUnion, Set.sSup_eq_sUnion,
      Set.mem_sUnion]
    constructor
    · rintro ⟨v, hv, hm⟩
      exact ⟨⟨_, ⟨v, hv, rfl⟩⟩, hm⟩
    · rintro ⟨⟨_, ⟨v, hv, rfl⟩⟩, hm⟩
      exact ⟨v, hv, hm⟩
  | succ n =>
    obtain ⟨b, hb⟩ := hne
    simp only [consEnv_succ, sSup_apply, Set.iSup_eq_iUnion, Set.mem_iUnion]
    exact ⟨fun hm => ⟨⟨_, ⟨b, hb, rfl⟩⟩, hm⟩, fun ⟨⟨_, ⟨c, _, rfl⟩⟩, hm⟩ => hm⟩

/-- **Scott's continuity theorem for the graph model.** For every term `M` and valuation `ρ`
of its free variables, the denotation of `M` is a Scott-continuous function of the values of its
bound variables (D. Scott, *Data types as lattices*, SIAM J. Comput. 5 (1976), Theorem 2.1). -/
theorem scottContinuous_denote (ρ : Var → Set ℕ) (M : Term Var) :
    ScottContinuous (denote ρ M) := by
  induction M with
  | bvar i => exact scottContinuous_eval i
  | fvar x => exact ScottContinuous.const (ρ x)
  | app M N ihM ihN =>
    exact (ihM.prodMk ihN).comp scottContinuous_app
  | abs M ih =>
    have hG : ∀ v, ScottContinuous fun bs => denote ρ M (consEnv v bs) :=
      fun v => (scottContinuous_consEnv_right v).comp ih
    refine ScottContinuous.of_map_sSup fun d hne hd => ?_
    have hv : ∀ v, denote ρ M (consEnv v (sSup d)) =
        sSup ((fun bs => denote ρ M (consEnv v bs)) '' d) := fun v => (hG v).map_sSup hne hd
    ext k
    simp only [denote, graph, Set.mem_ofPred_eq, hv, Set.sSup_eq_sUnion, Set.mem_sUnion,
      Set.mem_image, exists_exists_and_eq_and]

/-- **Denotations are Scott-continuous in the free variables.** For every term `M` and valuation
`bs` of its bound variables, the denotation of `M` is a Scott-continuous function of the
valuation `ρ` of its free variables, ordered pointwise (D. Scott, *Data types as lattices*, SIAM
J. Comput. 5 (1976), Theorem 2.1: LAMBDA-definable functions of their free variables are
continuous). -/
theorem scottContinuous_denote_fvar (M : Term Var) (bs : ℕ → Set ℕ) :
    ScottContinuous fun ρ : Var → Set ℕ => denote ρ M bs := by
  induction M generalizing bs with
  | bvar i => exact ScottContinuous.const (bs i)
  | fvar x =>
    refine ScottContinuous.of_map_sSup fun d _ _ => ?_
    ext m
    simp [denote, sSup_apply]
  | app M N ihM ihN =>
    exact ((ihM bs).prodMk (ihN bs)).comp scottContinuous_app
  | abs M ih =>
    refine ScottContinuous.of_map_sSup fun d hne hd => ?_
    have hv : ∀ v, denote (sSup d) M (consEnv v bs) =
        sSup ((fun ρ => denote ρ M (consEnv v bs)) '' d) := fun v =>
      (ih (consEnv v bs)).map_sSup hne hd
    ext k
    simp only [denote, graph, Set.mem_ofPred_eq, hv, Set.sSup_eq_sUnion, Set.mem_sUnion,
      Set.mem_image, exists_exists_and_eq_and]

theorem scottContinuous_denote_consEnv (ρ : Var → Set ℕ) (M : Term Var) (bs : ℕ → Set ℕ) :
    ScottContinuous fun v => denote ρ M (consEnv v bs) :=
  (scottContinuous_consEnv_left bs).comp (scottContinuous_denote ρ M)

/-- **β at the level of denotations.** Applying the denotation of `λ.M` to `v` gives the
denotation of `M` with the new bound variable valued by `v`; this is Scott's graph theorem
`app (graph f) = f` applied to the continuous function the body denotes. -/
theorem app_denote_abs (ρ : Var → Set ℕ) (M : Term Var) (bs : ℕ → Set ℕ) (v : Set ℕ) :
    app (denote ρ (.abs M) bs) v = denote ρ M (consEnv v bs) := by
  rw [denote, app_graph (scottContinuous_denote_consEnv ρ M bs)]

end Continuity

section Substitution

/-- **Denotations depend only on the bound variables in scope.** If every bound index of `M` is
below `k`, the denotation of `M` depends only on the first `k` values of the bound-variable
environment. -/
theorem denote_congr_of_lcAt (ρ : Var → Set ℕ) {M : Term Var} {k : ℕ} (hM : LcAt k M)
    {bs bs' : ℕ → Set ℕ} (h : ∀ i < k, bs i = bs' i) : denote ρ M bs = denote ρ M bs' := by
  induction M generalizing k bs bs' with
  | bvar i => exact h i (by simpa using hM)
  | fvar x => rfl
  | app M N ihM ihN =>
    simp only [LcAt, Bool.and_eq_true] at hM
    simp only [denote, ihM hM.1 h, ihN hM.2 h]
  | abs M ih =>
    simp only [LcAt] at hM
    simp only [denote]
    congr 1
    funext v
    refine ih hM fun i hi => ?_
    cases i with
    | zero => rfl
    | succ i => exact h i (by omega)

/-- **Locally closed terms ignore the bound-variable environment.** A locally closed term has
the same denotation under every valuation of bound variables. -/
theorem denote_congr_of_LC [HasFresh Var] (ρ : Var → Set ℕ) {M : Term Var} (hM : LC M)
    (bs bs' : ℕ → Set ℕ) : denote ρ M bs = denote ρ M bs' :=
  denote_congr_of_lcAt ρ ((lcAt_iff_LC M).2 hM) (fun _ hi => absurd hi (Nat.not_lt_zero _))

theorem denote_update_of_notMem [DecidableEq Var] {ρ : Var → Set ℕ} {x : Var} {M : Term Var}
    (hx : x ∉ M.fv) (v : Set ℕ) (bs : ℕ → Set ℕ) :
    denote (Function.update ρ x v) M bs = denote ρ M bs := by
  induction M generalizing bs with
  | bvar i => rfl
  | fvar y =>
    simp only [fv, Finset.mem_singleton] at hx
    simp [denote, Function.update_of_ne (Ne.symm hx)]
  | app M N ihM ihN =>
    simp only [fv, Finset.mem_union, not_or] at hx
    simp only [denote, ihM hx.1, ihN hx.2]
  | abs M ih =>
    simp only [fv] at hx
    simp only [denote, ih hx]

theorem update_consEnv_succ (v : Set ℕ) (bs : ℕ → Set ℕ) (i : ℕ) (w : Set ℕ) :
    Function.update (consEnv v bs) (i + 1) w = consEnv v (Function.update bs i w) := by
  funext n
  cases n with
  | zero => simp
  | succ n => by_cases h : n = i <;> simp [Function.update, h]

theorem update_consEnv_zero (v : Set ℕ) (bs : ℕ → Set ℕ) :
    Function.update (consEnv v bs) 0 v = consEnv v bs := by
  funext n
  cases n <;> simp

/-- **Substitution lemma for opening.** Opening the bound variable `i` of `M` with a term `s`
whose denotation does not depend on bound variables denotes `M` with index `i` valued by
the denotation of `s`. -/
theorem denote_openRec (ρ : Var → Set ℕ) {s : Term Var}
    (hs : ∀ bs bs', denote ρ s bs = denote ρ s bs') (M : Term Var) (i : ℕ) (bs : ℕ → Set ℕ) :
    denote ρ (M⟦i ↝ s⟧) bs = denote ρ M (Function.update bs i (denote ρ s bs)) := by
  induction M generalizing i bs with
  | bvar j =>
    by_cases h : i = j
    · subst h
      simp [openRec, denote]
    · simp [openRec, denote, h, Function.update_of_ne (Ne.symm h)]
  | fvar x => rfl
  | app M N ihM ihN =>
    change app _ _ = app _ _
    rw [ihM, ihN]
  | abs M ih =>
    change graph _ = graph _
    simp only [ih]
    congr 1
    funext v
    rw [update_consEnv_succ, hs (consEnv v bs) bs]

end Substitution

section Soundness

variable [HasFresh Var]

/-- **Soundness of a β-contraction in the graph model.** If `(λ.M) N` contracts to `M ^ N`,
both sides have the same denotation (D. Scott, *Data types as lattices*, SIAM J. Comput. 5
(1976), Theorem 2.2, the β part). -/
theorem denote_eq_of_beta {M N : Term Var} (h : Beta M N) (ρ : Var → Set ℕ)
    (bs : ℕ → Set ℕ) : denote ρ M bs = denote ρ N bs := by
  obtain @⟨M, N, hM, hN⟩ := h
  have hM1 : LcAt 1 M := by simpa [LcAt] using (lcAt_iff_LC _).2 hM
  change app _ _ = denote ρ (M⟦0 ↝ N⟧) bs
  rw [app_denote_abs, denote_openRec ρ (denote_congr_of_LC ρ hN)]
  refine denote_congr_of_lcAt ρ hM1 fun i hi => ?_
  obtain rfl : i = 0 := by omega
  simp

/-- **Soundness of full β-reduction in the graph model.** One step of full β-reduction,
contracting a redex anywhere in a term, under λ included, preserves the denotation in `P(ω)`
under every valuation of free and bound variables (D. Scott, *Data types as lattices*, SIAM J.
Comput. 5 (1976), Theorem 2.2: the rules β and ξ are valid in `P(ω)`). -/
theorem denote_eq_of_fullBeta {M N : Term Var} (h : FullBeta M N) (ρ : Var → Set ℕ)
    (bs : ℕ → Set ℕ) : denote ρ M bs = denote ρ N bs := by
  induction h generalizing ρ bs with
  | base h => exact denote_eq_of_beta h ρ bs
  | appL _ _ ih =>
    change app _ _ = app _ _
    rw [ih]
  | appR _ _ ih =>
    change app _ _ = app _ _
    rw [ih]
  | @abs M N xs _ ih =>
    classical
    change graph _ = graph _
    congr 1
    funext v
    obtain ⟨x, hx⟩ := fresh_exists (xs ∪ M.fv ∪ N.fv)
    simp only [Finset.mem_union, not_or] at hx
    have key := ih x hx.1.1 (Function.update ρ x v) (consEnv v bs)
    have hfx : ∀ bs bs', denote (Function.update ρ x v) (Term.fvar x) bs =
        denote (Function.update ρ x v) (Term.fvar x) bs' := fun _ _ => rfl
    change denote _ (M⟦0 ↝ Term.fvar x⟧) _ = denote _ (N⟦0 ↝ Term.fvar x⟧) _ at key
    rw [denote_openRec _ hfx, denote_openRec _ hfx] at key
    simpa [denote, update_consEnv_zero, denote_update_of_notMem hx.1.2,
      denote_update_of_notMem hx.2] using key

/-- **Soundness of multi-step full β-reduction in the graph model.** If `M` reduces to `N` in
any number of full β-steps, `M` and `N` have the same denotation in `P(ω)`. -/
theorem denote_eq_of_reflTransGen_fullBeta {M N : Term Var}
    (h : Relation.ReflTransGen FullBeta M N) (ρ : Var → Set ℕ) (bs : ℕ → Set ℕ) :
    denote ρ M bs = denote ρ N bs := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (denote_eq_of_fullBeta hstep ρ bs)

end Soundness

section Recursion

/-- **The paradoxical combinator `Y`.** The closed term `λu.(λx.u (x x)) (λx.u (x x))`, written
with de Bruijn indices as `λ.(λ.1 (0 0)) (λ.1 (0 0))` (D. Scott, *Data types as lattices*, SIAM J.
Comput. 5 (1976), equation (2.8)). -/
def Y : Term Var :=
  .abs (.app (.abs (.app (.bvar 1) (.app (.bvar 0) (.bvar 0))))
    (.abs (.app (.bvar 1) (.app (.bvar 0) (.bvar 0)))))

/-- **Scott's first recursion theorem.** In the graph model, the paradoxical combinator `Y`
applied to any `u ⊆ ℕ` denotes the least fixed point `⨆ k, (app u)^[k] ∅` of the continuous
function `app u` that `u` determines (D. Scott, *Data types as lattices*, SIAM J. Comput. 5
(1976), Theorem 2.5). -/
theorem app_denote_Y (ρ : Var → Set ℕ) (bs : ℕ → Set ℕ) (u : Set ℕ) :
    app (denote ρ Y bs) u = ⨆ k, (app u)^[k] ⊥ := by
  rw [Y, app_denote_abs]
  exact app_graph_diag u

end Recursion

section NonDegeneracy

/-- **The graph model separates `λx.λy.x` from `λx.λy.y`.** The closed normal forms
`K = λ.λ.1` and `K* = λ.λ.0` have different denotations in `P(ω)`, so the model does not
identify all terms. -/
theorem denote_K_ne_denote_KStar (ρ : Var → Set ℕ) (bs : ℕ → Set ℕ) :
    denote ρ (.abs (.abs (.bvar 1))) bs ≠ denote ρ (.abs (.abs (.bvar 0))) bs := by
  intro h
  have hK : app (app (denote ρ (.abs (.abs (.bvar 1))) bs) ∅) Set.univ =
      ∅ := by
    rw [app_denote_abs, app_denote_abs]
    rfl
  have hKs : app (app (denote ρ (.abs (.abs (.bvar 0))) bs) ∅) Set.univ =
      Set.univ := by
    rw [app_denote_abs, app_denote_abs]
    rfl
  rw [h, hKs] at hK
  exact Set.univ_nonempty.ne_empty hK

/-- **The η-rule is not sound in the graph model.** For a free variable `x`, the η-redex
`λy. x y` (`λ.(x 0)`) and `x` have different denotations under a suitable valuation, because
`graph (app u) ≠ u` for some `u` (D. Scott, *Data types as lattices*, SIAM J. Comput. 5 (1976),
Theorem 1.2; Theorem 2.2 lists only α, β and ξ). -/
theorem exists_denote_eta_ne (x : Var) (bs : ℕ → Set ℕ) :
    ∃ ρ : Var → Set ℕ,
      denote ρ (.abs (.app (.fvar x) (.bvar 0))) bs ≠ denote ρ (.fvar x) bs := by
  obtain ⟨u, hu⟩ := exists_graph_app_ne
  exact ⟨fun _ => u, by simpa [denote] using hu⟩

end NonDegeneracy

end Cslib.LambdaCalculus.LocallyNameless.Untyped.GraphModel
