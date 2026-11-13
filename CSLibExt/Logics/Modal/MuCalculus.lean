/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.Kripke
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Order.FixedPoints

/-!
# The modal μ-calculus

The modal μ-calculus (Kozen, *Results on the propositional μ-calculus*, TCS 1983) extends basic
modal logic (`CSLibExt/Logics/Modal/Kripke.lean`) with least and greatest fixed-point operators
`μ` and `ν` over de Bruijn variables. A formula denotes a set of worlds: `μ X. φ` is the least
pre-fixed point of `S ↦ ⟦φ⟧[X ↦ S]` and `ν X. φ` the greatest post-fixed point. There is no
negation constructor (so every formula is monotone in every variable), but a meta-level
negation `neg` swapping atoms with negated atoms, `∧`/`∨`, `□`/`◇`, `μ`/`ν` supports the
duality theorem `sat_neg`.

Main results:

* `sat_mono_env`: satisfaction is monotone in the environment.
* `sat_mu_unfold`, `sat_nu_unfold`: **the fixed-point unfoldings** `μ X. φ ≡ φ[μ X. φ / X]` and
  the dual for `ν`.
* `mu_induction`, `nu_coinduction`: **Park induction / coinduction** for the fixed points.
* `sat_mu_eq_lfp`, `sat_nu_eq_gfp`: the fixed points agree with Mathlib's `OrderHom.lfp` /
  `OrderHom.gfp` (the same fixed-point operators used for the independent `EF` / `EG`
  characterizations in `CSLibExt/Logics/CTL/Basic.lean`).
* `sat_neg`: **duality** `⟦¬φ⟧ = (⟦φ⟧)ᶜ` under the complemented environment.
* `EF_iff_reachable`, `AG_iff_forall_reachable`: `EF p` holds exactly at the states that can
  reach a `p`-state, and `AG p` holds exactly at the states whose reachable states all satisfy
  `p`. These are the μ-calculus forms of CTL's `EF` and `AG`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib
namespace Modal
namespace MuCalculus

universe u

/-- **Formulas of the modal μ-calculus.** The formulas over a type of atoms are built from
atoms $a$, negated atoms $\neg a$, variables $X_n$ for $n \in \mathbb{N}$ (de Bruijn indices for
the fixed-point binders), $\bot$ and $\top$ by conjunction $\varphi \wedge \psi$, disjunction
$\varphi \vee \psi$, the modalities $\Box\varphi$ and $\Diamond\varphi$, and the fixed-point
binders $\mu\varphi$ and $\nu\varphi$.

There is no negation of arbitrary formulas. Negated atoms are present so that the meta-level
negation, which swaps each connective with its dual, is an involution. -/
inductive MuFormula (Atom : Type u) : Type u where
  | atom : Atom → MuFormula Atom
  | natom : Atom → MuFormula Atom
  | var : ℕ → MuFormula Atom
  | bot : MuFormula Atom
  | top : MuFormula Atom
  | and : MuFormula Atom → MuFormula Atom → MuFormula Atom
  | or : MuFormula Atom → MuFormula Atom → MuFormula Atom
  | box : MuFormula Atom → MuFormula Atom
  | dia : MuFormula Atom → MuFormula Atom
  | mu : MuFormula Atom → MuFormula Atom
  | nu : MuFormula Atom → MuFormula Atom

namespace MuFormula

variable {Atom : Type u}

/-- **Negation of μ-calculus formulas.** The meta-level negation $\neg\varphi$ of a μ-calculus
formula $\varphi$ swaps each connective with its dual. It is defined by recursion: an atom $p$
becomes the negated atom $\overline{p}$ and $\overline{p}$ becomes $p$, each variable $x_n$
stays $x_n$, $\neg\bot = \top$, $\neg\top = \bot$,
$\neg(\varphi \wedge \psi) = \neg\varphi \vee \neg\psi$,
$\neg(\varphi \vee \psi) = \neg\varphi \wedge \neg\psi$, $\neg\Box\varphi = \Diamond\neg\varphi$,
$\neg\Diamond\varphi = \Box\neg\varphi$, $\neg\mu\varphi = \nu\neg\varphi$ and
$\neg\nu\varphi = \mu\neg\varphi$. -/
def neg : MuFormula Atom → MuFormula Atom
  | .atom a => .natom a
  | .natom a => .atom a
  | .var n => .var n
  | .bot => .top
  | .top => .bot
  | .and φ ψ => .or (neg φ) (neg ψ)
  | .or φ ψ => .and (neg φ) (neg ψ)
  | .box φ => .dia (neg φ)
  | .dia φ => .box (neg φ)
  | .mu φ => .nu (neg φ)
  | .nu φ => .mu (neg φ)

/-- **Meta-level negation is an involution.** Write $\neg\varphi$ for the meta-level negation of
a μ-calculus formula $\varphi$, which swaps each connective with its dual. For every μ-calculus
formula $\varphi$, negating twice gives back $\varphi$: $\neg\neg\varphi = \varphi$. -/
theorem neg_neg : ∀ (φ : MuFormula Atom), (neg (neg φ)) = φ
  | .atom _ => rfl
  | .natom _ => rfl
  | .var _ => rfl
  | .bot => rfl
  | .top => rfl
  | .and _ _ => by simp [neg, neg_neg]
  | .or _ _ => by simp [neg, neg_neg]
  | .box _ => by simp [neg, neg_neg]
  | .dia _ => by simp [neg, neg_neg]
  | .mu _ => by simp [neg, neg_neg]
  | .nu _ => by simp [neg, neg_neg]

end MuFormula

/-- **Extending an environment under a binder.** An environment $\rho$ assigns to each variable
index $n \in \mathbb{N}$ a predicate $\rho(n)$ on worlds. Its extension by a predicate $S$ on
worlds is the environment that assigns $S$ to index $0$ and $\rho(n)$ to index $n + 1$.

With de Bruijn indices, variable $1$ inside a binder thus refers to the enclosing binder. -/
def extendEnv {World : Type*} (env : ℕ → World → Prop) (S : World → Prop) :
    ℕ → World → Prop
  | 0 => S
  | n + 1 => env n

theorem extendEnv_zero {World : Type*} (env : ℕ → World → Prop) (S : World → Prop) :
    extendEnv env S 0 = S := rfl

theorem extendEnv_succ {World : Type*} (env : ℕ → World → Prop) (S : World → Prop)
    (n : ℕ) :
    extendEnv env S (n + 1) = env n := rfl

section Satisfaction

variable {World Atom : Type*} (M : KripkeModel World Atom)

/-- **Satisfaction in the modal μ-calculus.** Let $M$ be a Kripke model with accessibility
relation $R$ and valuation $V$, and let $\rho$ be an environment assigning a set of worlds to
each variable index $n \in \mathbb{N}$. For a set of worlds $S$, write $\rho[0 \mapsto S]$ for the
environment sending index $0$ to $S$ and index $n + 1$ to $\rho(n)$. The set $[\![\varphi]\!]_\rho$
of worlds satisfying a formula $\varphi$ in $M$ under $\rho$ is defined by recursion on
$\varphi$: an atom $a$ holds at $w$ when $V$ makes $a$ true at $w$, and the negated atom of $a$
when $V$ does not; the variable with index $n$ denotes $\rho(n)$; $\bot$ holds nowhere and $\top$
everywhere; conjunction and disjunction denote intersection and union; $\Box\varphi$ holds at $w$
when $\varphi$ holds at every $v$ with $w \mathrel{R} v$, and $\Diamond\varphi$ when $\varphi$
holds at some such $v$; $\mu\varphi$ holds at $w$ when $w \in S$ for every set of worlds $S$ with
$[\![\varphi]\!]_{\rho[0 \mapsto S]} \subseteq S$; and $\nu\varphi$ holds at $w$ when $w \in S$
for some set of worlds $S$ with $S \subseteq [\![\varphi]\!]_{\rho[0 \mapsto S]}$.

So $\mu\varphi$ is the least pre-fixed point of $S \mapsto [\![\varphi]\!]_{\rho[0 \mapsto S]}$,
stated directly as an infimum over pre-fixed points, and $\nu\varphi$ is the greatest
post-fixed point, stated as a supremum over post-fixed points. -/
def sat (env : ℕ → World → Prop) : MuFormula Atom → (World → Prop)
  | .atom a => fun w => M.valuation w a
  | .natom a => fun w => ¬ M.valuation w a
  | .var n => env n
  | .bot => fun _ => False
  | .top => fun _ => True
  | .and φ ψ => fun w => sat env φ w ∧ sat env ψ w
  | .or φ ψ => fun w => sat env φ w ∨ sat env ψ w
  | .box φ => fun w => ∀ v, M.rel w v → sat env φ v
  | .dia φ => fun w => ∃ v, M.rel w v ∧ sat env φ v
  | .mu φ => fun w => ∀ S : World → Prop,
      (∀ v, sat (extendEnv env S) φ v → S v) → S w
  | .nu φ => fun w => ∃ S : World → Prop,
      (∀ v, S v → sat (extendEnv env S) φ v) ∧ S w

@[simp] theorem sat_atom (env : ℕ → World → Prop) (a : Atom) (w : World) :
    sat M env (.atom a) w ↔ M.valuation w a := Iff.rfl

@[simp] theorem sat_natom (env : ℕ → World → Prop) (a : Atom) (w : World) :
    sat M env (.natom a) w ↔ ¬ M.valuation w a := Iff.rfl

@[simp] theorem sat_var (env : ℕ → World → Prop) (n : ℕ) (w : World) :
    sat M env (.var n) w ↔ env n w := Iff.rfl

@[simp] theorem sat_bot (env : ℕ → World → Prop) (w : World) :
    sat M env (.bot : MuFormula Atom) w ↔ False := Iff.rfl

@[simp] theorem sat_top (env : ℕ → World → Prop) (w : World) :
    sat M env (.top : MuFormula Atom) w ↔ True := Iff.rfl

@[simp] theorem sat_and (env : ℕ → World → Prop) (φ ψ : MuFormula Atom) (w : World) :
    sat M env (.and φ ψ) w ↔ sat M env φ w ∧ sat M env ψ w := Iff.rfl

@[simp] theorem sat_or (env : ℕ → World → Prop) (φ ψ : MuFormula Atom) (w : World) :
    sat M env (.or φ ψ) w ↔ sat M env φ w ∨ sat M env ψ w := Iff.rfl

@[simp] theorem sat_box (env : ℕ → World → Prop) (φ : MuFormula Atom) (w : World) :
    sat M env (.box φ) w ↔ ∀ v, M.rel w v → sat M env φ v := Iff.rfl

@[simp] theorem sat_dia (env : ℕ → World → Prop) (φ : MuFormula Atom) (w : World) :
    sat M env (.dia φ) w ↔ ∃ v, M.rel w v ∧ sat M env φ v := Iff.rfl

@[simp] theorem sat_mu (env : ℕ → World → Prop) (φ : MuFormula Atom) (w : World) :
    sat M env (.mu φ) w ↔ ∀ S : World → Prop,
      (∀ v, sat M (extendEnv env S) φ v → S v) → S w := Iff.rfl

@[simp] theorem sat_nu (env : ℕ → World → Prop) (φ : MuFormula Atom) (w : World) :
    sat M env (.nu φ) w ↔ ∃ S : World → Prop,
      (∀ v, S v → sat M (extendEnv env S) φ v) ∧ S w := Iff.rfl

/-- **Satisfaction is monotone in the environment.** Let $M$ be a Kripke model and let $\rho$
and $\rho'$ be environments (each assigns a set of worlds of $M$ to every variable $n$) with
$\rho(n) \subseteq \rho'(n)$ for every $n$. Then every μ-calculus formula $\varphi$ holds under
$\rho'$ at every world of $M$ where it holds under $\rho$: enlarging every variable's denotation
can only enlarge a formula's denotation. -/
theorem sat_mono_env : ∀ (φ : MuFormula Atom) {env env' : ℕ → World → Prop},
    (∀ n, env n ≤ env' n) → sat M env φ ≤ sat M env' φ := by
  intro φ
  induction φ with
  | atom _ => intro env env' _; exact fun w hw => hw
  | natom _ => intro env env' _; exact fun w hw => hw
  | var n => intro env env' hle; exact hle n
  | bot => intro env env' _; exact fun w hw => hw
  | top => intro env env' _; exact fun w _ => trivial
  | and φ ψ ihφ ihψ =>
      intro env env' hle w hw
      exact ⟨ihφ hle w hw.1, ihψ hle w hw.2⟩
  | or φ ψ ihφ ihψ =>
      intro env env' hle w hw
      exact hw.elim (fun h => Or.inl (ihφ hle w h)) (fun h => Or.inr (ihψ hle w h))
  | box φ ih =>
      intro env env' hle w hw v hvr
      exact ih hle v (hw v hvr)
  | dia φ ih =>
      intro env env' hle w hw
      obtain ⟨v, hvr, hφ⟩ := hw
      exact ⟨v, hvr, ih hle v hφ⟩
  | mu φ ih =>
      intro env env' hle w hw S hS
      apply hw S
      intro v hv
      apply hS v
      exact ih (fun n => by cases n with | zero => exact le_rfl | succ n => exact hle n) v hv
  | nu φ ih =>
      intro env env' hle w hw
      obtain ⟨S, hS, hwS⟩ := hw
      refine ⟨S, ?_, hwS⟩
      intro v hv
      exact ih (fun n => by cases n with | zero => exact le_rfl | succ n => exact hle n) v (hS v hv)

/-- **Monotonicity in the bound variable.** Let $M$ be a Kripke model, $\rho$ an environment
assigning a set of worlds to each variable index $n \in \mathbb{N}$, and $\varphi$ a μ-calculus
formula. For a set of worlds $S$, write $\rho[0 \mapsto S]$ for the environment sending index $0$
to $S$ and index $n + 1$ to $\rho(n)$. If $S_1 \subseteq S_2$ are sets of worlds, then every world
that satisfies $\varphi$ in $M$ under $\rho[0 \mapsto S_1]$ also satisfies $\varphi$ in $M$ under
$\rho[0 \mapsto S_2]$. -/
theorem sat_mono_extend {env : ℕ → World → Prop} {S₁ S₂ : World → Prop} (h : S₁ ≤ S₂)
    (φ : MuFormula Atom) :
    sat M (extendEnv env S₁) φ ≤ sat M (extendEnv env S₂) φ :=
  sat_mono_env M φ (fun n => by cases n with | zero => exact h | succ _ => exact le_rfl)

/-- **The least fixed point is a pre-fixed point.** Let $M$ be a Kripke model, $\rho$ an
environment and $\varphi$ a μ-calculus formula. Write $\llbracket\psi\rrbracket_\sigma$ for the
set of worlds of $M$ at which $\psi$ holds under the environment $\sigma$, and $\rho[S]$ for the
extension of $\rho$ under a binder by a set of worlds $S$ (variable $0$ denotes $S$ and variable
$n + 1$ denotes $\rho(n)$). For $T = \llbracket\mu\varphi\rrbracket_\rho$, where $\mu\varphi$
binds variable $0$ of $\varphi$, we have $\llbracket\varphi\rrbracket_{\rho[T]} \subseteq T$. -/
theorem mu_pre_fixed (env : ℕ → World → Prop) (φ : MuFormula Atom) :
    sat M (extendEnv env (sat M env (.mu φ))) φ ≤ sat M env (.mu φ) := by
  intro w hw S hS
  apply hS w
  apply sat_mono_extend M _ φ w hw
  intro u hu
  exact hu S hS

/-- **The least fixed point is contained in its unfolding.** For every Kripke model $M$,
environment $\rho$ and μ-calculus formula $\varphi$, every world satisfying $\mu\varphi$ in $\rho$
also satisfies $\varphi$ in the extension of $\rho$ by the set of worlds satisfying $\mu\varphi$
in $\rho$. -/
theorem mu_le_fixed (env : ℕ → World → Prop) (φ : MuFormula Atom) :
    sat M env (.mu φ) ≤ sat M (extendEnv env (sat M env (.mu φ))) φ := by
  intro w hw
  exact hw _ (sat_mono_extend M (mu_pre_fixed M env φ) φ)

/-- **The μ unfolding.** Let $M$ be a Kripke model, $\rho$ an environment assigning a set of
worlds to each variable index $n \in \mathbb{N}$, and $\varphi$ a μ-calculus formula. Let $A$ be
the set of worlds satisfying $\mu\varphi$ in $M$ under $\rho$. Then $A$ is exactly the set of
worlds satisfying $\varphi$ in $M$ under the environment that sends index $0$ to $A$ and index
$n + 1$ to $\rho(n)$. -/
theorem sat_mu_unfold (env : ℕ → World → Prop) (φ : MuFormula Atom) :
    sat M env (.mu φ) = sat M (extendEnv env (sat M env (.mu φ))) φ :=
  le_antisymm (mu_le_fixed M env φ) (mu_pre_fixed M env φ)

/-- **The greatest fixed point is a post-fixed point.** Let $M$ be a Kripke model, $\rho$ an
environment and $\varphi$ a μ-calculus formula. Write $\llbracket\psi\rrbracket_\sigma$ for the
set of worlds of $M$ at which $\psi$ holds under the environment $\sigma$, and $\rho[S]$ for the
extension of $\rho$ under a binder by a set of worlds $S$ (variable $0$ denotes $S$ and variable
$n + 1$ denotes $\rho(n)$). For $T = \llbracket\nu\varphi\rrbracket_\rho$, where $\nu\varphi$
binds variable $0$ of $\varphi$, we have $T \subseteq \llbracket\varphi\rrbracket_{\rho[T]}$. -/
theorem nu_post_fixed (env : ℕ → World → Prop) (φ : MuFormula Atom) :
    sat M env (.nu φ) ≤ sat M (extendEnv env (sat M env (.nu φ))) φ := by
  rintro w ⟨S, hS, hwS⟩
  exact sat_mono_extend M (fun u hu => ⟨S, hS, hu⟩) φ w (hS w hwS)

/-- **The greatest fixed point is a pre-fixed point.** Let $M$ be a Kripke model, $\rho$ an
environment and $\varphi$ a μ-calculus formula. Write $\llbracket\psi\rrbracket_\sigma$ for the
set of worlds of $M$ at which $\psi$ holds under the environment $\sigma$, and $\rho[S]$ for the
extension of $\rho$ under a binder by a set of worlds $S$ (variable $0$ denotes $S$ and variable
$n + 1$ denotes $\rho(n)$). For $T = \llbracket\nu\varphi\rrbracket_\rho$, where $\nu\varphi$
binds variable $0$ of $\varphi$, we have $\llbracket\varphi\rrbracket_{\rho[T]} \subseteq T$. -/
theorem nu_le_post_fixed (env : ℕ → World → Prop) (φ : MuFormula Atom) :
    sat M (extendEnv env (sat M env (.nu φ))) φ ≤ sat M env (.nu φ) := by
  intro w hw
  exact ⟨sat M (extendEnv env (sat M env (.nu φ))) φ,
    sat_mono_extend M (nu_post_fixed M env φ) φ, hw⟩

/-- **The ν unfolding.** Let $M$ be a Kripke model, $\rho$ an environment assigning a set of
worlds to each variable index $n \in \mathbb{N}$, and $\varphi$ a μ-calculus formula. Let $A$ be
the set of worlds satisfying $\nu\varphi$ in $M$ under $\rho$. Then $A$ is exactly the set of
worlds satisfying $\varphi$ in $M$ under the environment that sends index $0$ to $A$ and index
$n + 1$ to $\rho(n)$. -/
theorem sat_nu_unfold (env : ℕ → World → Prop) (φ : MuFormula Atom) :
    sat M env (.nu φ) = sat M (extendEnv env (sat M env (.nu φ))) φ :=
  le_antisymm (nu_post_fixed M env φ) (nu_le_post_fixed M env φ)

/-- **Park induction.** Let $M$ be a Kripke model, $\rho$ an environment, $\varphi$ a μ-calculus
formula and $P$ a predicate on worlds. If every world satisfying $\varphi$ in the extension of
$\rho$ by $P$ satisfies $P$, then every world satisfying $\mu\varphi$ in $\rho$ satisfies $P$. -/
theorem mu_induction {env : ℕ → World → Prop} {φ : MuFormula Atom} {P : World → Prop}
    (hP : sat M (extendEnv env P) φ ≤ P) : sat M env (.mu φ) ≤ P := by
  intro w hw
  exact hw P hP

/-- **Coinduction for the greatest fixed point.** Let $M$ be a Kripke model, $\rho$ an
environment, $\varphi$ a μ-calculus formula and $P$ a set of worlds of $M$. Write
$\llbracket\psi\rrbracket_\sigma$ for the set of worlds at which $\psi$ holds under the
environment $\sigma$, and $\rho[P]$ for the extension of $\rho$ under a binder by $P$ (variable
$0$ denotes $P$ and variable $n + 1$ denotes $\rho(n)$). If
$P \subseteq \llbracket\varphi\rrbracket_{\rho[P]}$, then
$P \subseteq \llbracket\nu\varphi\rrbracket_\rho$, where $\nu\varphi$ binds variable $0$ of
$\varphi$: every post-fixed point is below the greatest fixed point. -/
theorem nu_coinduction {env : ℕ → World → Prop} {φ : MuFormula Atom} {P : World → Prop}
    (hP : P ≤ sat M (extendEnv env P) φ) : P ≤ sat M env (.nu φ) := by
  intro w hw
  exact ⟨P, hP, hw⟩

/-- **The fixed-point operator of a formula.** Given a Kripke model $M$, an environment $\rho$
(a set of worlds $\rho(n)$ for each variable $n$) and a μ-calculus formula $\varphi$, this is
the monotone map on sets of worlds of $M$ sending $S$ to the set of worlds at which $\varphi$
holds under $\rho[S]$, the extension of $\rho$ under a binder by $S$ (variable $0$ denotes $S$
and variable $n + 1$ denotes $\rho(n)$). -/
def muOp (env : ℕ → World → Prop) (φ : MuFormula Atom) :
    (World → Prop) →o (World → Prop) :=
  ⟨fun S => sat M (extendEnv env S) φ, fun _ _ hle => sat_mono_extend M hle φ⟩

/-- **The μ formula denotes the least fixed point.** Let $M$ be a Kripke model, $\rho$ an
environment assigning a set of worlds to each variable index $n \in \mathbb{N}$, and $\varphi$ a
μ-calculus formula. For a set of worlds $S$, write $\rho[0 \mapsto S]$ for the environment sending
index $0$ to $S$ and index $n + 1$ to $\rho(n)$. Then the set of worlds satisfying $\mu\varphi$ in
$M$ under $\rho$ is the least fixed point of the monotone operator on sets of worlds that sends
$S$ to the set of worlds satisfying $\varphi$ in $M$ under $\rho[0 \mapsto S]$. -/
theorem sat_mu_eq_lfp (env : ℕ → World → Prop) (φ : MuFormula Atom) :
    sat M env (.mu φ) = (muOp M env φ).lfp := by
  apply le_antisymm
  · intro w hw
    exact hw _ (le_of_eq (OrderHom.map_lfp (muOp M env φ)))
  · exact OrderHom.lfp_le (muOp M env φ) (mu_pre_fixed M env φ)

/-- **The ν formula denotes the greatest fixed point.** Let $M$ be a Kripke model, $\rho$ an
environment assigning a set of worlds to each variable index $n \in \mathbb{N}$, and $\varphi$ a
μ-calculus formula. For a set of worlds $S$, write $\rho[0 \mapsto S]$ for the environment sending
index $0$ to $S$ and index $n + 1$ to $\rho(n)$. Then the set of worlds satisfying $\nu\varphi$ in
$M$ under $\rho$ is the greatest fixed point of the monotone operator on sets of worlds that sends
$S$ to the set of worlds satisfying $\varphi$ in $M$ under $\rho[0 \mapsto S]$. -/
theorem sat_nu_eq_gfp (env : ℕ → World → Prop) (φ : MuFormula Atom) :
    sat M env (.nu φ) = (muOp M env φ).gfp := by
  apply le_antisymm
  · rintro w ⟨S, hS, hwS⟩
    exact OrderHom.le_gfp (muOp M env φ) hS w hwS
  · intro w hw
    exact ⟨_, le_of_eq (OrderHom.map_gfp (muOp M env φ)).symm, hw⟩

end Satisfaction

section Duality

variable {World Atom : Type*} (M : KripkeModel World Atom)

/-- **Complementing an extended environment.** For every environment $\rho$ (assigning to each
variable index $n$ a predicate $\rho(n)$ on worlds) and every predicate $S$ on worlds,
complementing every predicate of the extension of $\rho$ by $S$ gives the extension of the
complemented environment $n \mapsto \neg\rho(n)$ by the predicate $w \mapsto \neg S(w)$. -/
theorem extendEnv_compl (env : ℕ → World → Prop) (S : World → Prop) :
    (fun n => fun w => ¬ extendEnv env S n w) =
      extendEnv (fun n => fun w => ¬ env n w) (fun w => ¬ S w) := by
  funext n w
  cases n with
  | zero => rfl
  | succ _ => rfl

/-- **Double complement of a predicate.** For every predicate $S$ on worlds, the predicate
$w \mapsto \neg\neg S(w)$ equals $S$. -/
theorem compl_compl (S : World → Prop) :
    (fun w => ¬ ¬ S w) = S := by
  funext w
  exact propext not_not

/-- **Duality.** Let $M$ be a Kripke model, $\rho$ an environment assigning a set of worlds to
each variable index $n \in \mathbb{N}$, and $\varphi$ a μ-calculus formula. Let $\neg\varphi$ be
the dual formula of $\varphi$, obtained by swapping atoms with negated atoms, $\bot$ with $\top$,
$\wedge$ with $\vee$, $\Box$ with $\Diamond$ and $\mu$ with $\nu$, and keeping variables. Write
$\overline{\rho}$ for the environment sending each index $n$ to the complement of $\rho(n)$. Then
for every world $w$, $w$ satisfies $\neg\varphi$ in $M$ under $\overline{\rho}$ if and only if $w$
does not satisfy $\varphi$ in $M$ under $\rho$. -/
theorem sat_neg : ∀ (φ : MuFormula Atom) (env : ℕ → World → Prop) (w : World),
    sat M (fun n => fun w => ¬ env n w) (MuFormula.neg φ) w ↔ ¬ sat M env φ w := by
  intro φ
  induction φ with
  | atom a => intro env w; simp [MuFormula.neg]
  | natom a => intro env w; simp [MuFormula.neg]
  | var n => intro env w; simp [MuFormula.neg]
  | bot => intro env w; simp [MuFormula.neg]
  | top => intro env w; simp [MuFormula.neg]
  | and φ ψ ihφ ihψ =>
      intro env w
      simp only [MuFormula.neg, sat_or, sat_and]
      rw [ihφ, ihψ]
      exact not_and_or.symm
  | or φ ψ ihφ ihψ =>
      intro env w
      simp only [MuFormula.neg, sat_and, sat_or]
      rw [ihφ, ihψ]
      exact not_or.symm
  | box φ ih =>
      intro env w
      simp only [MuFormula.neg, sat_dia, sat_box]
      rw [not_forall]
      constructor
      · rintro ⟨v, hvr, hφ⟩
        exact ⟨v, not_imp.mpr ⟨hvr, fun hsat => (ih env v).mp hφ hsat⟩⟩
      · rintro ⟨v, h⟩
        rw [not_imp] at h
        exact ⟨v, h.1, (ih env v).mpr h.2⟩
  | dia φ ih =>
      intro env w
      simp only [MuFormula.neg, sat_box, sat_dia]
      rw [not_exists]
      constructor
      · intro h v hvr
        exact (ih env v).mp (h v hvr.1) hvr.2
      · intro h v hvr
        exact (ih env v).mpr (fun hsat => h v ⟨hvr, hsat⟩)
  | mu φ ih =>
      intro env w
      simp only [MuFormula.neg]
      -- `F' S = (F (Sᶜ))ᶜ` for the two operators, via the IH and `extendEnv_compl`.
      have hF : ∀ S : World → Prop,
          sat M (extendEnv (fun n => fun w => ¬ env n w) (fun w => ¬ ¬ S w))
              (MuFormula.neg φ) =
            fun w => ¬ sat M (extendEnv env (fun w => ¬ S w)) φ w := by
        intro S
        have hcomp : extendEnv (fun n => fun w => ¬ env n w) (fun w => ¬ ¬ S w) =
            fun n => fun w => ¬ extendEnv env (fun w => ¬ S w) n w :=
          (extendEnv_compl env (fun w => ¬ S w)).symm
        funext v
        rw [hcomp]
        exact propext (ih _ v)
      have hF' : ∀ S : World → Prop,
          sat M (extendEnv (fun n => fun w => ¬ env n w) S) (MuFormula.neg φ) =
            fun w => ¬ sat M (extendEnv env (fun w => ¬ S w)) φ w := by
        intro S
        conv_lhs => rw [← compl_compl S]
        exact hF S
      constructor
      · intro hw
        by_contra hcon
        have hle : sat M env (.mu φ) ≤
            fun w => ¬ sat M (fun n => fun w => ¬ env n w) (.nu (MuFormula.neg φ)) w := by
          apply mu_induction
          intro v hv hmem
          rw [sat_nu_unfold] at hmem
          have h2 := congrFun (hF'
            (sat M (fun n => fun w => ¬ env n w) (.nu (MuFormula.neg φ)))) v
          rw [h2] at hmem
          exact hmem hv
        exact hle w hcon hw
      · intro hcon
        exact nu_coinduction (M := M) (env := fun n => fun w => ¬ env n w)
          (φ := MuFormula.neg φ) (P := fun w => ¬ sat M env (.mu φ) w)
          (by
            intro v hv
            have h2 : sat M (extendEnv (fun n => fun w => ¬ env n w)
                (fun w => ¬ sat M env (.mu φ) w)) (MuFormula.neg φ) v =
                ¬ sat M (extendEnv env
                  (fun w => ¬ (fun w => ¬ sat M env (.mu φ) w) w)) φ v :=
              congrFun (hF' (fun w => ¬ sat M env (.mu φ) w)) v
            rw [h2]
            have hPc : (fun w => ¬ (fun w => ¬ sat M env (.mu φ) w) w) = sat M env (.mu φ) := by
              funext u
              exact propext not_not
            rw [hPc, ← sat_mu_unfold]
            exact hv) w hcon
  | nu φ ih =>
      intro env w
      simp only [MuFormula.neg]
      have hF : ∀ S : World → Prop,
          sat M (extendEnv (fun n => fun w => ¬ env n w) (fun w => ¬ ¬ S w))
              (MuFormula.neg φ) =
            fun w => ¬ sat M (extendEnv env (fun w => ¬ S w)) φ w := by
        intro S
        have hcomp : extendEnv (fun n => fun w => ¬ env n w) (fun w => ¬ ¬ S w) =
            fun n => fun w => ¬ extendEnv env (fun w => ¬ S w) n w :=
          (extendEnv_compl env (fun w => ¬ S w)).symm
        funext v
        rw [hcomp]
        exact propext (ih _ v)
      have hF' : ∀ S : World → Prop,
          sat M (extendEnv (fun n => fun w => ¬ env n w) S) (MuFormula.neg φ) =
            fun w => ¬ sat M (extendEnv env (fun w => ¬ S w)) φ w := by
        intro S
        conv_lhs => rw [← compl_compl S]
        exact hF S
      constructor
      · intro hw
        by_contra hcon
        have hle : sat M (fun n => fun w => ¬ env n w) (.mu (MuFormula.neg φ)) ≤
            fun w => ¬ sat M env (.nu φ) w := by
          apply mu_induction
          intro v hv hmem
          rw [sat_nu_unfold] at hmem
          have hPc : (fun w => ¬ (fun w => ¬ sat M env (.nu φ) w) w) = sat M env (.nu φ) := by
            funext u
            exact propext not_not
          rw [← hPc] at hmem
          have h2 := congrFun (hF' (fun w => ¬ sat M env (.nu φ) w)) v
          rw [h2] at hv
          exact hv hmem
        exact hle w hw hcon
      · intro hcon
        rw [sat_mu]
        intro S hS
        -- The complement of `S` is a post-fixed point of `F`, hence below `gfp F`.
        have hSc : (fun w => ¬ S w) ≤ sat M env (.nu φ) := by
          apply nu_coinduction
          intro v hv
          by_contra hnot
          have h2 := congrFun (hF' S) v
          have hFS : sat M (extendEnv (fun n => fun w => ¬ env n w) S)
              (MuFormula.neg φ) v := h2.symm ▸ hnot
          exact hv (hS v hFS)
        by_contra hSw
        exact hcon (hSc w hSw)

end Duality

section Reachability

variable {World Atom : Type*} (M : KripkeModel World Atom)

/-- **The μ-calculus formula $\mathsf{EF}\,p$.** For an atom $p$, $\mathsf{EF}\,p$ is the least
fixed point formula $\mu X.\,(p \vee \Diamond X)$. It expresses that some state reachable from
the current one satisfies $p$. -/
def EF (p : Atom) : MuFormula Atom := .mu (.or (.atom p) (.dia (.var 0)))

/-- **The μ-calculus formula $\mathsf{AG}\,p$.** For an atom $p$, $\mathsf{AG}\,p$ is the
greatest fixed point formula $\nu X.\,(p \wedge \Box X)$. It expresses that every state reachable
from the current one satisfies $p$. -/
def AG (p : Atom) : MuFormula Atom := .nu (.and (.atom p) (.box (.var 0)))

/-- **$\mathsf{EF}$ is reachability.** For every Kripke model $M$, every environment $\rho$ (an
assignment of a predicate on worlds to each variable index), every atom $p$ and every world $w$,
the μ-calculus formula $\mathsf{EF}\,p$ holds at $w$ in $\rho$ if and only if $p$ is true at some
world reachable from $w$ in zero or more steps of the accessibility relation of $M$. -/
theorem EF_iff_reachable (env : ℕ → World → Prop) (p : Atom) (w : World) :
    sat M env (EF p) w ↔
      ∃ v, Relation.ReflTransGen M.rel w v ∧ M.valuation v p := by
  have hunfold : sat M env (EF p) =
      sat M (extendEnv env (sat M env (EF p))) (.or (.atom p) (.dia (.var 0))) :=
    sat_mu_unfold M env _
  constructor
  · -- Park induction: the reachable set is a pre-fixed point of the `EF` functional.
    intro hw
    have hle : sat M env (EF p) ≤
        fun w => ∃ v, Relation.ReflTransGen M.rel w v ∧ M.valuation v p := by
      apply mu_induction
      rintro v (hval | ⟨u, hru, hu⟩)
      · exact ⟨v, Relation.ReflTransGen.refl, hval⟩
      · obtain ⟨t, hrt, hpt⟩ := hu
        exact ⟨t, Relation.ReflTransGen.head hru hrt, hpt⟩
    exact hle w hw
  · rintro ⟨v, hreach, hval⟩
    -- Head induction on the reaching path, unfolding `EF` once per step.
    induction hreach using Relation.ReflTransGen.head_induction_on with
    | refl =>
        rw [hunfold]
        exact Or.inl hval
    | head hstep _ ih =>
        rw [hunfold]
        exact Or.inr ⟨_, hstep, ih⟩

/-- **$\mathsf{AG}$ is universal reachability.** For every Kripke model $M$, every environment
$\rho$ (an assignment of a predicate on worlds to each variable index), every atom $p$ and every
world $w$, the μ-calculus formula $\mathsf{AG}\,p$ holds at $w$ in $\rho$ if and only if $p$ is
true at every world reachable from $w$ in zero or more steps of the accessibility relation of
$M$. -/
theorem AG_iff_forall_reachable (env : ℕ → World → Prop) (p : Atom) (w : World) :
    sat M env (AG p) w ↔
      ∀ v, Relation.ReflTransGen M.rel w v → M.valuation v p := by
  have hunfold : sat M env (AG p) =
      sat M (extendEnv env (sat M env (AG p))) (.and (.atom p) (.box (.var 0))) :=
    sat_nu_unfold M env _
  constructor
  · intro hw v hreach
    revert hw
    induction hreach using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro hw
        rw [hunfold] at hw
        exact hw.1
    | head hstep _ ih =>
        intro hw
        rw [hunfold] at hw
        exact ih (hw.2 _ hstep)
  · -- Coinduction: the universally-good set is a post-fixed point of the `AG` functional.
    intro hall
    exact nu_coinduction (M := M) (env := env)
      (φ := .and (.atom p) (.box (.var 0)))
      (P := fun w => ∀ v', Relation.ReflTransGen M.rel w v' → M.valuation v' p)
      (by
        intro v hv
        refine ⟨hv v Relation.ReflTransGen.refl, fun u hru => ?_⟩
        intro v' hrt
        exact hv v' (Relation.ReflTransGen.head hru hrt)) w hall

/-- **The formula $\mu X.\, \mu Y.\, X$ is false everywhere.** For every Kripke model $M$ and
every environment $\rho$, the formula $\mu X.\, \mu Y.\, X$ holds at no world of $M$ under $\rho$.
In de Bruijn form this formula is $\mu\, \mu\, x_1$: inside the inner binder, variable $1$ refers
to the outer binder, not to the inner one. -/
theorem mu_mu_var_one_eq_bot (env : ℕ → World → Prop) :
    sat M env (.mu (.mu (.var 1))) = fun _ => False := by
  apply le_antisymm
  · apply mu_induction
    intro w hw
    exact hw _ (fun v hv => hv)
  · intro w hw
    exact False.elim hw

/-- **The formula $\nu X.\, \nu Y.\, X$ is true everywhere.** For every Kripke model $M$ and
every environment $\rho$, the formula $\nu X.\, \nu Y.\, X$ holds at every world of $M$ under
$\rho$. In de Bruijn form this formula is $\nu\, \nu\, x_1$: inside the inner binder, variable
$1$ refers to the outer binder. This is the dual of the fact that $\mu X.\, \mu Y.\, X$ is false
everywhere. -/
theorem nu_nu_var_one_eq_top (env : ℕ → World → Prop) :
    sat M env (.nu (.nu (.var 1))) = fun _ => True := by
  apply le_antisymm
  · intro w _
    trivial
  · apply nu_coinduction
    intro w _
    exact ⟨fun _ => True, fun v _ => trivial, trivial⟩

end Reachability

end MuCalculus
end Modal
end Cslib
