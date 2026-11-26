/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.HindleyMilner.Safety

@[expose] public section

/-!
# Tests for the type safety of let-polymorphism

A concrete signature: the nullary constructors `one : int` and `tt ff : bool`, and the unary
destructor `not : bool → bool` with δ-rules `not tt ↦ ff` and `not ff ↦ tt`; δ agrees with it.

- With the Church pair `λa b c. c a b`, `let id = λx. x in pair (id one) (id tt)` is typed, well
  formed and safe, and evaluates to the value `λc. c one tt`, while `λf. pair (f one) (f tt)` has
  no type: `let` is what lets `id` take both types.
- Negative controls: `one tt` is stuck and untyped (ill-typed programs do go wrong); `not not`, a
  saturated destructor application outside δ, is stuck and untyped; δ' with `not tt ↦ one`
  breaks preservation and does not agree with the signature.
- Capture: substituting `one` under a binder named `one` renames the binder, which keeps the type
  of the reduct; plain replacement would not. That program binds a constant, so it is not well
  formed.
- Overapplication: with the nullary constructor `u : int` and the unary destructor
  `d : int → (int → int)`, where `d u ↦ λx. x`, the typed `(d u) u` is neither a value nor a
  δ-redex, yet it reduces, by reducing its head `d u`. δ agrees with this signature, which needs
  agreement to ask for reducibility rather than a δ-step at the root; `(d u) u` reduces to `u`
  and is safe.
- A primitive on an expression that is no program: the identity primitive
  `d : (int → int) → (int → int)` with `d v ↦ v` for every value `v` agrees with its signature.
  The value `λd. d`, whose binder shadows the constant `d`, has type `int → int`, so `d (λd. d)`
  is typed and reduces to `λd. d`; neither is well formed, and agreement asks nothing of them.
- Statement pins for the safety theorems, closed by the theorems themselves.
-/

set_option autoImplicit false

namespace CSLibExtTest.Languages.LambdaCalculus.HindleyMilner.Safety

open Cslib Cslib.Unification Cslib.Unification.Term Cslib.HindleyMilner

/-- Base types for the examples. -/
inductive Base where
  | int
  | bool
  deriving DecidableEq, Repr

/-- The base type `int`. -/
abbrev tI : Ty Base := const .int
/-- The base type `bool`. -/
abbrev tB : Ty Base := const .bool

/-- The signature: constructors `one : int`, `tt ff : bool` of arity 0, and the destructor
`not : bool → bool` of arity 1. -/
def K₀ : Constants Base where
  ctx := [("one", toScheme tI), ("tt", toScheme tB), ("ff", toScheme tB),
    ("not", toScheme (node tB tB))]
  arity c := if c = "not" then 1 else 0
  IsCtor c := c ≠ "not"
  closed := by decide

/-- δ for `not`: `not tt ↦ ff` and `not ff ↦ tt`. -/
def δ₀ (e e' : Expr) : Prop :=
  e = .app (.var "not") (.var "tt") ∧ e' = .var "ff" ∨
    e = .app (.var "not") (.var "ff") ∧ e' = .var "tt"

/-- A bad δ: `not tt ↦ one`. -/
def δ₁ (e e' : Expr) : Prop := e = .app (.var "not") (.var "tt") ∧ e' = .var "one"

/-- δ agrees with the signature: the requirements of Definition 10.5.5 hold for a real
instance. -/
theorem agrees : K₀.Agrees δ₀ := by
  have val : ∀ c, c ∈ K₀.names → c ≠ "not" → K₀.IsValue (.var c) := fun c hc hn ↦
    Constants.IsValue.const (c := c) (args := []) hc (by simp) (Or.inl ⟨hn, by simp⟩)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e e' h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨"not", [.var "tt"], rfl, by decide, by simp [K₀], by simp [K₀],
        by simpa using val "tt" (by decide) (by decide)⟩
    · exact ⟨"not", [.var "ff"], rfl, by decide, by simp [K₀], by simp [K₀],
        by simpa using val "ff" (by decide) (by decide)⟩
  · intro e e' h _
    rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [Constants.WF, Expr.bv]
  · intro e e' τ h he _
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨τ₁, h₁, -⟩ := hasType_app_iff.mp he
      obtain ⟨σ, ts, hσ, hτ⟩ := hasType_var_iff.mp h₁
      simp [K₀, Ctx.lookup] at hσ
      subst hσ
      rw [inst_toScheme] at hτ
      cases hτ
      simpa [inst_toScheme] using HasType.var (Γ := K₀.ctx) (x := "ff") (fun _ ↦ tB)
        (σ := toScheme tB) (by simp [K₀, Ctx.lookup])
    · obtain ⟨τ₁, h₁, -⟩ := hasType_app_iff.mp he
      obtain ⟨σ, ts, hσ, hτ⟩ := hasType_var_iff.mp h₁
      simp [K₀, Ctx.lookup] at hσ
      subst hσ
      rw [inst_toScheme] at hτ
      cases hτ
      simpa [inst_toScheme] using HasType.var (Γ := K₀.ctx) (x := "tt") (fun _ ↦ tB)
        (σ := toScheme tB) (by simp [K₀, Ctx.lookup])
  · intro c args τ hc hargs he _
    have hhead : ∀ (rest : List Expr) (h : Expr) (τ : Ty Base),
        HasType K₀.ctx (h.apps rest) τ → ∃ τ', HasType K₀.ctx h τ' := by
      intro rest
      induction rest with
      | nil => exact fun h τ hh ↦ ⟨τ, hh⟩
      | cons r rs ih =>
        intro h τ hh
        obtain ⟨τ', h'⟩ := ih (.app h r) τ hh
        obtain ⟨τ₁, h₁, -⟩ := hasType_app_iff.mp h'
        exact ⟨_, h₁⟩
    have hnames : c = "one" ∨ c = "tt" ∨ c = "ff" ∨ c = "not" := by
      simpa [Constants.names, K₀] using hc
    rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · left
      rcases hnames with rfl | rfl | rfl | rfl
      · exact val _ hc (by decide)
      · exact val _ hc (by decide)
      · exact val _ hc (by decide)
      · exact Constants.IsValue.const hc (by simp) (Or.inr ⟨by simp [K₀], by simp [K₀]⟩)
    · obtain ⟨τ₁, h₁, h₂⟩ := hasType_app_iff.mp he
      obtain ⟨σ, ts, hσ, hτ⟩ := hasType_var_iff.mp h₁
      rcases hnames with rfl | rfl | rfl | rfl <;> simp [K₀, Ctx.lookup] at hσ <;> subst hσ <;>
        rw [inst_toScheme] at hτ <;> cases hτ
      right
      have hva := hargs a (by simp)
      cases hva with
      | var hz =>
        obtain ⟨σ, ts, hσ, -⟩ := hasType_var_iff.mp h₂
        exact absurd (List.mem_toFinset.mpr (Ctx.mem_names_of_lookup hσ)) hz
      | lam =>
        obtain ⟨τ₁, τ₂, h, -⟩ := hasType_lam_iff.mp h₂
        cases h
      | @const c' args' hc' _ hlen' =>
        have hnames' : c' = "one" ∨ c' = "tt" ∨ c' = "ff" ∨ c' = "not" := by
          simpa [Constants.names, K₀] using hc'
        have hargs' : args' = [] := by
          rcases hnames' with rfl | rfl | rfl | rfl <;> simpa [K₀] using hlen'
        subst hargs'
        obtain ⟨σ, ts, hσ, hτ⟩ := hasType_var_iff.mp h₂
        rcases hnames' with rfl | rfl | rfl | rfl <;> simp [K₀, Ctx.lookup] at hσ <;> subst hσ <;>
          rw [inst_toScheme] at hτ <;> cases hτ
        · exact ⟨.var "ff", Constants.Step.delta (Or.inl ⟨rfl, rfl⟩)⟩
        · exact ⟨.var "tt", Constants.Step.delta (Or.inr ⟨rfl, rfl⟩)⟩
    · exfalso
      obtain ⟨τ', h'⟩ := hhead rest _ τ he
      obtain ⟨τ₂, h₂, -⟩ := hasType_app_iff.mp h'
      obtain ⟨τ₁, h₁, -⟩ := hasType_app_iff.mp h₂
      obtain ⟨σ, ts, hσ, hτ⟩ := hasType_var_iff.mp h₁
      rcases hnames with rfl | rfl | rfl | rfl <;> simp [K₀, Ctx.lookup] at hσ <;> subst hσ <;>
        rw [inst_toScheme] at hτ <;> cases hτ

/-! ### The polymorphic identity under `let`, with a Church pair -/

/-- The Church pair `λa b c. c a b`. -/
def pair : Expr := .lam "a" (.lam "b" (.lam "c" (.app (.app (.var "c") (.var "a")) (.var "b"))))

/-- `pair (f one) (f tt)`. -/
def body (f : String) : Expr :=
  .app (.app pair (.app (.var f) (.var "one"))) (.app (.var f) (.var "tt"))

/-- `let id = λx. x in pair (id one) (id tt)`. -/
def eLet : Expr := .let_ "id" (.lam "x" (.var "x")) (body "id")

/-- `λf. pair (f one) (f tt)`. -/
def eLam : Expr := .lam "f" (body "f")

/-- The value `λc. c one tt`. -/
def result : Expr := .lam "c" (.app (.app (.var "c") (.var "one")) (.var "tt"))

/-- The `let` program has type `(int → bool → int) → int`. -/
theorem eLet_hasType : HasType K₀.ctx eLet (node (node tI (node tB tI)) tI) := by
  have v : ∀ {Γ : Ctx Base} {x : String} {τ : Ty Base} (ts : ℕ → Ty Base),
      (Γ.lookup x).map (Scheme.inst ts) = some τ → HasType Γ (.var x) τ := fun ts h ↦ by
    obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .var ts hσ
  exact .let_ (τ₁ := node (Term.var 0) (Term.var 0)) (.lam (v Term.var (by decide)))
    (.app (τ₁ := tB) (.app (τ₁ := tI) (.lam (.lam (.lam (.app (τ₁ := tB)
        (.app (τ₁ := tI) (v Term.var (by decide)) (v Term.var (by decide)))
        (v Term.var (by decide))))))
      (.app (τ₁ := tI) (v (fun _ ↦ tI) (by decide)) (v Term.var (by decide))))
      (.app (τ₁ := tB) (v (fun _ ↦ tB) (by decide)) (v Term.var (by decide))))

/-- The `let` program binds no constant. -/
theorem eLet_wf : K₀.WF eLet := by
  unfold Constants.WF
  decide

/-- The `let` program evaluates to `λc. c one tt`. -/
theorem eLet_eval : Relation.ReflTransGen (K₀.Step δ₀) eLet result := by
  have val : ∀ c, c ∈ K₀.names → c ≠ "not" → K₀.IsValue (.var c) := fun c hc hn ↦
    Constants.IsValue.const (c := c) (args := []) hc (by simp) (Or.inl ⟨hn, by simp⟩)
  have vone := val "one" (by decide) (by decide)
  have vtt := val "tt" (by decide) (by decide)
  have s₁ : K₀.Step δ₀ eLet (.app (.app pair (.app (.lam "x" (.var "x")) (.var "one")))
      (.app (.lam "x" (.var "x")) (.var "tt"))) := by
    have := Constants.Step.letV (K := K₀) (δ := δ₀) (z := "id") (e := body "id")
      (Constants.IsValue.lam (z := "x") (e := .var "x"))
    simpa [eLet, body, pair, Expr.subst_def, Expr.subst, Expr.fv] using this
  have s₂ : K₀.Step δ₀ (.app (.app pair (.app (.lam "x" (.var "x")) (.var "one")))
      (.app (.lam "x" (.var "x")) (.var "tt")))
      (.app (.app pair (.var "one")) (.app (.lam "x" (.var "x")) (.var "tt"))) := by
    have := Constants.Step.appL (K := K₀) (δ := δ₀) (e₂ := .app (.lam "x" (.var "x")) (.var "tt"))
      (Constants.Step.appR (v := pair) Constants.IsValue.lam
        (Constants.Step.beta (z := "x") (e := .var "x") vone))
    simpa [Expr.subst_def, Expr.subst] using this
  have s₃ : K₀.Step δ₀ (.app (.app pair (.var "one")) (.app (.lam "x" (.var "x")) (.var "tt")))
      (.app (.lam "b" (.lam "c" (.app (.app (.var "c") (.var "one")) (.var "b"))))
        (.app (.lam "x" (.var "x")) (.var "tt"))) := by
    have := Constants.Step.appL (K := K₀) (δ := δ₀) (e₂ := .app (.lam "x" (.var "x")) (.var "tt"))
      (Constants.Step.beta (z := "a")
        (e := .lam "b" (.lam "c" (.app (.app (.var "c") (.var "a")) (.var "b")))) vone)
    simpa [pair, Expr.subst_def, Expr.subst, Expr.fv] using this
  have s₄ : K₀.Step δ₀ (.app (.lam "b" (.lam "c" (.app (.app (.var "c") (.var "one")) (.var "b"))))
        (.app (.lam "x" (.var "x")) (.var "tt")))
      (.app (.lam "b" (.lam "c" (.app (.app (.var "c") (.var "one")) (.var "b"))))
        (.var "tt")) := by
    have := Constants.Step.appR
      (Constants.IsValue.lam (K := K₀) (z := "b")
        (e := .lam "c" (.app (.app (.var "c") (.var "one")) (.var "b"))))
      (Constants.Step.beta (K := K₀) (δ := δ₀) (z := "x") (e := .var "x") vtt)
    simpa [Expr.subst_def, Expr.subst] using this
  have s₅ : K₀.Step δ₀ (.app (.lam "b" (.lam "c" (.app (.app (.var "c") (.var "one"))
      (.var "b")))) (.var "tt")) result := by
    have := Constants.Step.beta (K := K₀) (δ := δ₀) (z := "b")
      (e := .lam "c" (.app (.app (.var "c") (.var "one")) (.var "b"))) vtt
    simpa [result, Expr.subst_def, Expr.subst, Expr.fv] using this
  exact .head s₁ (.head s₂ (.head s₃ (.head s₄ (.single s₅))))

/-- `λc. c one tt` is a value of the type of the `let` program. -/
theorem result_isValue :
    K₀.IsValue result ∧ HasType K₀.ctx result (node (node tI (node tB tI)) tI) := by
  have v : ∀ {Γ : Ctx Base} {x : String} {τ : Ty Base} (ts : ℕ → Ty Base),
      (Γ.lookup x).map (Scheme.inst ts) = some τ → HasType Γ (.var x) τ := fun ts h ↦ by
    obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .var ts hσ
  exact ⟨Constants.IsValue.lam, .lam (.app (τ₁ := tB) (.app (τ₁ := tI) (v Term.var (by decide))
    (v Term.var (by decide))) (v Term.var (by decide)))⟩

/-- With `id` λ-bound instead of `let`-bound, the program has no type. -/
theorem eLam_not_hasType (τ : Ty Base) : ¬ HasType K₀.ctx eLam τ := by
  have inv : ∀ {Γ : Ctx Base} {x : String} {τ σ : Ty Base}, HasType Γ (.var x) τ →
      Γ.lookup x = some (toScheme σ) → τ = σ := fun h hx ↦ by
    obtain ⟨σ', ts, h', rfl⟩ := hasType_var_iff.mp h
    rw [hx, Option.some.injEq] at h'
    rw [← h', inst_toScheme]
  intro h
  obtain ⟨τ₁, τ₂, -, h⟩ := hasType_lam_iff.mp h
  obtain ⟨τb, h₁, h₂⟩ := hasType_app_iff.mp h
  obtain ⟨τa, -, h₃⟩ := hasType_app_iff.mp h₁
  obtain ⟨ρ₁, hf₁, ho⟩ := hasType_app_iff.mp h₃
  obtain ⟨ρ₂, hf₂, ht⟩ := hasType_app_iff.mp h₂
  have e := (inv hf₁ (σ := τ₁) (by simp [Ctx.lookup])).trans
    (inv hf₂ (σ := τ₁) (by simp [Ctx.lookup])).symm
  rw [inv ho (σ := tI) (by simp [Ctx.lookup, K₀]),
    inv ht (σ := tB) (by simp [Ctx.lookup, K₀])] at e
  simp [tI, tB] at e

/-- Algorithm W accepts the `let` program and rejects the λ-bound one. -/
theorem W_eLet_eLam : (∃ s τ n', W K₀.ctx eLet 0 = some (s, τ, n')) ∧ W K₀.ctx eLam 0 = none :=
  by
    refine ⟨?_, ?_⟩
    · have h : (W K₀.ctx eLet 0).isSome = true := by
        simp (config := {decide := true}) [W, eLet, body, pair, K₀, Ctx.lookup, toScheme,
          Scheme.inst, Scheme.eval, Scheme.boundSup, gen, Ctx.subst, Ctx.ftv, Ctx.visibleVars,
          unify, Subst.comp, Term.subst, Term.vars, Scheme.substTy, substEqs, Subst.single]
      obtain ⟨⟨s, τ, n'⟩, hs⟩ := Option.isSome_iff_exists.mp h
      exact ⟨s, τ, n', hs⟩
    · cases h : W K₀.ctx eLam 0 with
      | none => rfl
      | some r =>
        obtain ⟨s, τ, n'⟩ := r
        refine (eLam_not_hasType τ ((hasType_of_W_eq_some h).mono
          (Ctx.MoreGeneral.of_lookup_eq fun z ↦ ?_))).elim
        rw [Ctx.lookup_subst_congr (t := Term.var) (fun x hx ↦ by simp [K₀.closed] at hx),
          Ctx.subst_var]

/-- The `let` program is safe in the operational semantics. -/
theorem eLet_safe : (Constants.opSem agrees).Safe eLet := Constants.safe agrees eLet_hasType eLet_wf

/-! ### Negative controls -/

/-- `one tt` is stuck: it is not a value and does not reduce. -/
theorem oneTT_stuck : ¬ K₀.IsValue (.app (.var "one") (.var "tt")) ∧
    ∀ e', ¬ K₀.Step δ₀ (.app (.var "one") (.var "tt")) e' := by
  have key : ∀ (as : List Expr) (h : Expr), h.apps as = .app (.var "one") (.var "tt") →
      h = .var "one" ∧ as = [.var "tt"] ∨ h = .app (.var "one") (.var "tt") ∧ as = [] := by
    intro as
    induction as with
    | nil => exact fun h hh ↦ Or.inr ⟨hh, rfl⟩
    | cons a as ih =>
      intro h hh
      rcases ih (.app h a) hh with ⟨h1, -⟩ | ⟨h1, rfl⟩
      · cases h1
      · cases h1
        exact Or.inl ⟨rfl, rfl⟩
  refine ⟨fun hv ↦ ?_, fun e' hs ↦ ?_⟩
  · generalize he : Expr.app (.var "one") (.var "tt") = e at hv
    cases hv with
    | var => cases he
    | lam => cases he
    | @const c args _ _ hlen =>
      rcases key args (.var c) he.symm with ⟨h1, rfl⟩ | ⟨h1, -⟩
      · cases h1
        simp [K₀] at hlen
      · cases h1
  · cases hs with
    | delta h => simp [δ₀] at h
    | appL h => cases h with | delta h => simp [δ₀] at h
    | appR _ h => cases h with | delta h => simp [δ₀] at h

/-- `one tt` has no type. -/
theorem oneTT_not_hasType (τ : Ty Base) : ¬ HasType K₀.ctx (.app (.var "one") (.var "tt")) τ :=
  by
    intro h
    obtain ⟨τ₁, h₁, -⟩ := hasType_app_iff.mp h
    obtain ⟨σ, ts, hσ, hτ⟩ := hasType_var_iff.mp h₁
    simp [K₀, Ctx.lookup] at hσ
    subst hσ
    rw [inst_toScheme] at hτ
    cases hτ

/-- `not not` is stuck: a saturated destructor application outside δ is not a value and does not
reduce. -/
theorem notNot_stuck : ¬ K₀.IsValue (.app (.var "not") (.var "not")) ∧
    ∀ e', ¬ K₀.Step δ₀ (.app (.var "not") (.var "not")) e' := by
  have key : ∀ (as : List Expr) (h : Expr), h.apps as = .app (.var "not") (.var "not") →
      h = .var "not" ∧ as = [.var "not"] ∨ h = .app (.var "not") (.var "not") ∧ as = [] := by
    intro as
    induction as with
    | nil => exact fun h hh ↦ Or.inr ⟨hh, rfl⟩
    | cons a as ih =>
      intro h hh
      rcases ih (.app h a) hh with ⟨h1, -⟩ | ⟨h1, rfl⟩
      · cases h1
      · cases h1
        exact Or.inl ⟨rfl, rfl⟩
  refine ⟨fun hv ↦ ?_, fun e' hs ↦ ?_⟩
  · generalize he : Expr.app (.var "not") (.var "not") = e at hv
    cases hv with
    | var => cases he
    | lam => cases he
    | @const c args _ _ hlen =>
      rcases key args (.var c) he.symm with ⟨h1, rfl⟩ | ⟨h1, -⟩
      · cases h1
        simp [K₀] at hlen
      · cases h1
  · cases hs with
    | delta h => simp [δ₀] at h
    | appL h => cases h with | delta h => simp [δ₀] at h
    | appR _ h => cases h with | delta h => simp [δ₀] at h

/-- `not not` has no type. -/
theorem notNot_not_hasType (τ : Ty Base) : ¬ HasType K₀.ctx (.app (.var "not") (.var "not")) τ :=
  by
    intro h
    obtain ⟨τ₁, h₁, h₂⟩ := hasType_app_iff.mp h
    obtain ⟨σ, ts, hσ, hτ⟩ := hasType_var_iff.mp h₁
    simp [K₀, Ctx.lookup] at hσ
    subst hσ
    rw [inst_toScheme] at hτ
    cases hτ
    obtain ⟨σ, ts, hσ, hτ⟩ := hasType_var_iff.mp h₂
    simp [K₀, Ctx.lookup] at hσ
    subst hσ
    rw [inst_toScheme] at hτ
    cases hτ

/-- With `not tt ↦ one`, the typed `not tt : bool` reduces to `one`, which is not a `bool`. -/
theorem badDelta_breaks : K₀.Step δ₁ (.app (.var "not") (.var "tt")) (.var "one") ∧
    HasType K₀.ctx (.app (.var "not") (.var "tt")) tB ∧ ¬ HasType K₀.ctx (.var "one") tB := by
  refine ⟨Constants.Step.delta ⟨rfl, rfl⟩, ?_, ?_⟩
  · refine HasType.app (τ₁ := tB) ?_ ?_
    · simpa [inst_toScheme] using HasType.var (Γ := K₀.ctx) (x := "not") (fun _ ↦ tB)
        (σ := toScheme (node tB tB)) (by simp [K₀, Ctx.lookup])
    · simpa [inst_toScheme] using HasType.var (Γ := K₀.ctx) (x := "tt") (fun _ ↦ tB)
        (σ := toScheme tB) (by simp [K₀, Ctx.lookup])
  · intro h
    obtain ⟨σ, ts, hσ, hτ⟩ := hasType_var_iff.mp h
    simp [K₀, Ctx.lookup] at hσ
    subst hσ
    rw [inst_toScheme] at hτ
    cases hτ

/-- The bad δ does not agree with the signature. -/
theorem badDelta_not_agrees : ¬ K₀.Agrees δ₁ :=
  fun h ↦ badDelta_breaks.2.2
    (h.preserve ⟨rfl, rfl⟩ badDelta_breaks.2.1 (by unfold Constants.WF; decide))

/-! ### Capture -/

/-- `(λx. λone. x) one`, which binds the constant `one`. -/
def eCap : Expr := .app (.lam "x" (.lam "one" (.var "x"))) (.var "one")

/-- Substitution renames the binder `one` to the fresh name `xxxx`. -/
theorem capture_subst :
    (Expr.lam "one" (.var "x"))["x" := Expr.var "one"] = .lam "xxxx" (.var "one") := by
  rw [Expr.subst_def, Expr.subst]
  simp [Expr.fv, Expr.names, Expr.rename, Expr.subst]
  decide

/-- `eCap` reduces to `λxxxx. one`. -/
theorem eCap_step : K₀.Step δ₀ eCap (.lam "xxxx" (.var "one")) := by
  have vone : K₀.IsValue (.var "one") :=
    Constants.IsValue.const (c := "one") (args := []) (by decide) (by simp)
      (Or.inl ⟨by simp [K₀], by simp⟩)
  have := Constants.Step.beta (K := K₀) (δ := δ₀) (z := "x") (e := .lam "one" (.var "x")) vone
  rw [capture_subst] at this
  exact this

/-- `eCap` and its reduct have type `bool → int`; plain replacement, `λone. one`, does not. -/
theorem capture_types : HasType K₀.ctx eCap (node tB tI) ∧
    HasType K₀.ctx (.lam "xxxx" (.var "one")) (node tB tI) ∧
    ¬ HasType K₀.ctx (.lam "one" (.var "one")) (node tB tI) := by
  have v : ∀ {Γ : Ctx Base} {x : String} {τ : Ty Base} (ts : ℕ → Ty Base),
      (Γ.lookup x).map (Scheme.inst ts) = some τ → HasType Γ (.var x) τ := fun ts h ↦ by
    obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .var ts hσ
  refine ⟨.app (τ₁ := tI) (.lam (.lam (v Term.var (by decide)))) (v Term.var (by decide)),
    .lam (v Term.var (by decide)), fun h ↦ ?_⟩
  obtain ⟨τ₁, τ₂, heq, h⟩ := hasType_lam_iff.mp h
  cases heq
  obtain ⟨σ, ts, hσ, hτ⟩ := hasType_var_iff.mp h
  simp [Ctx.lookup] at hσ
  subst hσ
  rw [inst_toScheme] at hτ
  cases hτ

/-- `eCap` is not well formed. -/
theorem eCap_not_wf : ¬ K₀.WF eCap := by
  unfold Constants.WF
  decide

/-! ### Overapplication -/

/-- A second signature: the constructor `u : int` of arity 0 and the destructor
`d : int → (int → int)` of arity 1. -/
def Kud : Constants Base where
  ctx := [("u", toScheme tI), ("d", toScheme (node tI (node tI tI)))]
  arity c := if c = "d" then 1 else 0
  IsCtor c := c ≠ "d"
  closed := by decide

/-- δ for `d`: `d u ↦ λx. x`. -/
def δud (e e' : Expr) : Prop := e = .app (.var "d") (.var "u") ∧ e' = .lam "x" (.var "x")

/-- `(d u) u`: the destructor `d` applied to one more value than its arity. -/
def overapp : Expr := .app (.app (.var "d") (.var "u")) (.var "u")

/-- δ agrees with the second signature. A typed application of a constant to values is a value,
the δ-redex `d u`, or an overapplication of `d u` to more values, which is no δ-redex but reduces
by reducing its head `d u`. -/
theorem agrees_ud : Kud.Agrees δud := by
  have valU : Kud.IsValue (.var "u") :=
    Constants.IsValue.const (c := "u") (args := []) (by decide) (by simp)
      (Or.inl ⟨by simp [Kud], by simp [Kud]⟩)
  have hsteps : ∀ (rest : List Expr) (h h' : Expr), Kud.Step δud h h' →
      Kud.Step δud (h.apps rest) (h'.apps rest) := by
    intro rest
    induction rest with
    | nil => exact fun h h' hs ↦ hs
    | cons r rs ih => exact fun h h' hs ↦ ih (.app h r) (.app h' r) (Constants.Step.appL hs)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e e' h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨"d", [.var "u"], rfl, by decide, by simp [Kud], by simp [Kud], by simpa using valU⟩
  · intro e e' h _
    obtain ⟨-, rfl⟩ := h
    unfold Constants.WF
    decide
  · intro e e' τ h he _
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨τ₁, h₁, -⟩ := hasType_app_iff.mp he
    obtain ⟨σ, ts, hσ, hτ⟩ := hasType_var_iff.mp h₁
    simp [Kud, Ctx.lookup] at hσ
    subst hσ
    rw [inst_toScheme] at hτ
    cases hτ
    refine HasType.lam ?_
    simpa [inst_toScheme] using HasType.var (Γ := ("x", toScheme tI) :: Kud.ctx) (x := "x")
      (fun _ ↦ tI) (σ := toScheme tI) (by simp [Ctx.lookup])
  · intro c args τ hc hargs he _
    have hhead : ∀ (rest : List Expr) (h : Expr) (τ : Ty Base),
        HasType Kud.ctx (h.apps rest) τ → ∃ τ', HasType Kud.ctx h τ' := by
      intro rest
      induction rest with
      | nil => exact fun h τ hh ↦ ⟨τ, hh⟩
      | cons r rs ih =>
        intro h τ hh
        obtain ⟨τ', h'⟩ := ih (.app h r) τ hh
        obtain ⟨τ₁, h₁, -⟩ := hasType_app_iff.mp h'
        exact ⟨_, h₁⟩
    have hint : ∀ a, Kud.IsValue a → HasType Kud.ctx a tI → a = .var "u" := by
      intro a hv ht
      cases hv with
      | var hz =>
        obtain ⟨σ, ts, hσ, -⟩ := hasType_var_iff.mp ht
        exact absurd (List.mem_toFinset.mpr (Ctx.mem_names_of_lookup hσ)) hz
      | lam =>
        obtain ⟨τ₁, τ₂, h, -⟩ := hasType_lam_iff.mp ht
        cases h
      | @const c' args' hc' _ hlen' =>
        have hnames' : c' = "u" ∨ c' = "d" := by simpa [Constants.names, Kud] using hc'
        have hargs' : args' = [] := by
          rcases hnames' with rfl | rfl <;> simpa [Kud] using hlen'
        subst hargs'
        obtain ⟨σ, ts, hσ, hτ⟩ := hasType_var_iff.mp ht
        rcases hnames' with rfl | rfl <;> simp [Kud, Ctx.lookup] at hσ <;> subst hσ <;>
          rw [inst_toScheme] at hτ
        · rfl
        · cases hτ
    have hnames : c = "u" ∨ c = "d" := by simpa [Constants.names, Kud] using hc
    rcases args with _ | ⟨a, rest⟩
    · left
      rcases hnames with rfl | rfl
      · exact valU
      · exact Constants.IsValue.const hc (by simp) (Or.inr ⟨by simp [Kud], by simp [Kud]⟩)
    · obtain ⟨τ', h'⟩ := hhead rest (.app (.var c) a) τ he
      obtain ⟨τ₁, h₁, h₂⟩ := hasType_app_iff.mp h'
      obtain ⟨σ, ts, hσ, hτ⟩ := hasType_var_iff.mp h₁
      rcases hnames with rfl | rfl <;> simp [Kud, Ctx.lookup] at hσ <;> subst hσ <;>
        rw [inst_toScheme] at hτ <;> cases hτ
      right
      obtain rfl := hint a (hargs a List.mem_cons_self) h₂
      exact ⟨_, hsteps rest _ _ (Constants.Step.delta ⟨rfl, rfl⟩)⟩

/-- `(d u) u` has type `int` and reduces, in the evaluation context `[] u`, to `(λx. x) u`; it is
not a value, and no δ-rule applies to it at the root. -/
theorem overapp_reduces : HasType Kud.ctx overapp tI ∧
    Kud.Step δud overapp (.app (.lam "x" (.var "x")) (.var "u")) ∧
    ¬ Kud.IsValue overapp ∧ ∀ e', ¬ δud overapp e' := by
  have hs : Kud.Step δud overapp (.app (.lam "x" (.var "x")) (.var "u")) :=
    Constants.Step.appL (Constants.Step.delta ⟨rfl, rfl⟩)
  have hu : HasType Kud.ctx (.var "u") tI := by
    simpa [inst_toScheme] using HasType.var (Γ := Kud.ctx) (x := "u") (fun _ ↦ tI)
      (σ := toScheme tI) (by simp [Kud, Ctx.lookup])
  have hd : HasType Kud.ctx (.var "d") (node tI (node tI tI)) := by
    simpa [inst_toScheme] using HasType.var (Γ := Kud.ctx) (x := "d") (fun _ ↦ tI)
      (σ := toScheme (node tI (node tI tI))) (by simp [Kud, Ctx.lookup])
  refine ⟨.app (.app hd hu) hu, hs, fun hv ↦ Constants.IsValue.not_step agrees_ud hv hs, ?_⟩
  intro e' h
  simp [δud, overapp] at h

/-- `(d u) u` reduces to the value `u`, and it is safe. -/
theorem overapp_safe : Relation.ReflTransGen (Kud.Step δud) overapp (.var "u") ∧
    (Constants.opSem agrees_ud).Safe overapp := by
  have valU : Kud.IsValue (.var "u") :=
    Constants.IsValue.const (c := "u") (args := []) (by decide) (by simp)
      (Or.inl ⟨by simp [Kud], by simp [Kud]⟩)
  have hβ : Kud.Step δud (.app (.lam "x" (.var "x")) (.var "u")) (.var "u") := by
    simpa [Expr.subst_def, Expr.subst] using
      Constants.Step.beta (K := Kud) (δ := δud) (z := "x") (e := .var "x") valU
  refine ⟨.head overapp_reduces.2.1 (.single hβ), Constants.safe agrees_ud overapp_reduces.1 ?_⟩
  unfold Constants.WF
  decide

/-! ### A primitive on an expression that is no program -/

/-- A third signature: the destructor `d : (int → int) → (int → int)` of arity 1. -/
def Kid : Constants Base where
  ctx := [("d", toScheme (node (node tI tI) (node tI tI)))]
  arity _ := 1
  IsCtor _ := False
  closed := by decide

/-- δ for the identity primitive: `d v ↦ v` for every value `v`. -/
def δid (e e' : Expr) : Prop := ∃ v, Kid.IsValue v ∧ e = .app (.var "d") v ∧ e' = v

/-- `d (λd. d)`: the binder of the argument shadows the constant `d`. -/
def dShadow : Expr := .app (.var "d") (.lam "d" (.var "d"))

/-- The identity primitive agrees with its signature. Its reduct is its argument, so the reduct
of a well-formed δ-redex is well formed; a typed application `d v` has `v : int → int`, so the
reduct keeps the type; and `d` applied to one or more values reduces. -/
theorem agrees_id : Kid.Agrees δid := by
  have hsteps : ∀ (rest : List Expr) (h h' : Expr), Kid.Step δid h h' →
      Kid.Step δid (h.apps rest) (h'.apps rest) := by
    intro rest
    induction rest with
    | nil => exact fun h h' hs ↦ hs
    | cons r rs ih => exact fun h h' hs ↦ ih (.app h r) (.app h' r) (Constants.Step.appL hs)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e e' h
    obtain ⟨v, hv, rfl, he'⟩ := h
    subst e'
    exact ⟨"d", [v], rfl, by decide, by simp [Kid], by simp [Kid], by simpa using hv⟩
  · intro e e' h hwf
    obtain ⟨v, -, rfl, he'⟩ := h
    subst e'
    simpa [Constants.WF, Expr.bv] using hwf
  · intro e e' τ h he _
    obtain ⟨v, -, rfl, he'⟩ := h
    subst e'
    obtain ⟨τ₁, h₁, h₂⟩ := hasType_app_iff.mp he
    obtain ⟨σ, ts, hσ, hτ⟩ := hasType_var_iff.mp h₁
    simp [Kid, Ctx.lookup] at hσ
    subst hσ
    rw [inst_toScheme] at hτ
    cases hτ
    exact h₂
  · intro c args τ hc hargs _ _
    have hcd : c = "d" := by simpa [Constants.names, Kid] using hc
    subst hcd
    rcases args with _ | ⟨a, rest⟩
    · exact Or.inl (Constants.IsValue.const hc (by simp) (Or.inr ⟨by simp [Kid], by simp [Kid]⟩))
    · exact Or.inr ⟨_, hsteps rest (.app (.var "d") a) a
        (Constants.Step.delta ⟨a, hargs a List.mem_cons_self, rfl, rfl⟩)⟩

/-- The boundary: `d (λd. d)` has type `int → int` and reduces to `λd. d`, but neither is well
formed, so the conditions of agreement say nothing about them. -/
theorem dShadow_boundary : HasType Kid.ctx dShadow (node tI tI) ∧
    Kid.Step δid dShadow (.lam "d" (.var "d")) ∧ ¬ Kid.WF dShadow ∧
    ¬ Kid.WF (.lam "d" (.var "d")) := by
  have v : ∀ {Γ : Ctx Base} {x : String} {τ : Ty Base} (ts : ℕ → Ty Base),
      (Γ.lookup x).map (Scheme.inst ts) = some τ → HasType Γ (.var x) τ := fun ts h ↦ by
    obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .var ts hσ
  refine ⟨.app (τ₁ := node tI tI) (v Term.var (by decide)) (.lam (v Term.var (by decide))),
    Constants.Step.delta ⟨.lam "d" (.var "d"), Constants.IsValue.lam, rfl, rfl⟩, ?_, ?_⟩
  · unfold Constants.WF
    decide
  · unfold Constants.WF
    decide

/-! ### Statement pins -/

section Pins

variable {B : Type} {K : Constants B} {δ : Expr → Expr → Prop} {e e' : Expr} {τ : Ty B}

example : K.Agrees δ → HasType K.ctx e τ → K.WF e → K.Step δ e e' →
    HasType K.ctx e' τ ∧ K.WF e' := Constants.Step.preservation

example : K.Agrees δ → HasType K.ctx e τ → K.WF e → K.IsValue e ∨ ∃ e', K.Step δ e e' :=
  Constants.progress

example : K.Agrees δ → K.IsValue e → ¬ K.Step δ e e' := Constants.IsValue.not_step

example (hK : K.Agrees δ) : δ e e' → K.WF e → K.WF e' := hK.wf

example (hK : K.Agrees δ) : δ e e' → HasType K.ctx e τ → K.WF e → HasType K.ctx e' τ :=
  hK.preserve

example (hK : K.Agrees δ) {c : String} {args : List Expr} : c ∈ K.names →
    (∀ a ∈ args, K.IsValue a) → HasType K.ctx ((Expr.var c).apps args) τ →
    K.WF ((Expr.var c).apps args) →
    K.IsValue ((Expr.var c).apps args) ∨ ∃ e', K.Step δ ((Expr.var c).apps args) e' :=
  hK.progress

example : K.Agrees δ → HasType K.ctx e τ → K.WF e → Relation.ReflTransGen (K.Step δ) e e' →
    K.IsValue e' ∨ ∃ e'', K.Step δ e' e'' := Constants.typeSafety

example (hK : K.Agrees δ) : HasType K.ctx e τ → K.WF e → (Constants.opSem hK).Safe e :=
  Constants.safe hK

example {Γ : Ctx B} {x : String} {v : Expr} {τ₁ : Ty B} : Γ.lookup x = none →
    HasType Γ v τ₁ → HasType ((x, gen Γ τ₁) :: Γ) e τ → Disjoint e.bv v.fv →
    HasType Γ (e[x := v]) τ := HasType.subst_gen

end Pins

end CSLibExtTest.Languages.LambdaCalculus.HindleyMilner.Safety
