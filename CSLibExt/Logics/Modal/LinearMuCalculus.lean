/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Pairing
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Order.FixedPoints

/-!
# The linear-time modal μ-calculus

The linear-time (or linear) modal μ-calculus (Vardi, *A temporal fixpoint
calculus*, POPL 1988) is the μ-calculus interpreted over *words* rather than
branching trees: a formula is evaluated at a position of an infinite word
`ℕ → Atom → Prop`, and the only modality is `next`, moving to the next
position. A formula denotes a set of positions: `μ X. φ` is the least
pre-fixed point of `S ↦ ⟦φ⟧[X ↦ S]` and `ν X. φ` the greatest post-fixed
point. As in `CSLibExt.Logics.Modal.MuCalculus`, there is no negation
constructor (so every formula is monotone), but a meta-level negation `neg`
swapping atoms with negated atoms, `∧`/`∨`, `μ`/`ν` supports the duality
theorem `sat_neg`.

Main results:

* `sat_mono_env`: satisfaction is monotone in the environment.
* `sat_mu_unfold`, `sat_nu_unfold`: the fixed-point unfoldings.
* `mu_induction`, `nu_coinduction`: Park induction / coinduction.
* `sat_mu_eq_lfp`, `sat_nu_eq_gfp`: agreement with Mathlib's `OrderHom.lfp` /
  `OrderHom.gfp`.
* `sat_neg`: duality `⟦¬φ⟧ = (⟦φ⟧)ᶜ` under the complemented environment.
* `F_iff`, `G_iff`: `F p` holds at `n` iff `p` holds at some `m ≥ n`, and
  `G p` holds at `n` iff `p` holds at every `m ≥ n`.
* `sat_closed_env`: closed formulas do not depend on the environment.
* `linearMuCode`, `linearMuCode_injective`: an injective encoding of
  formulas with `ℕ` atoms as natural numbers, used for the complexity
  statements in `WantedExt`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib
namespace Modal
namespace LinearMuCalculus

universe u

/-- Formulas of the linear-time μ-calculus over atoms `Atom`, with de Bruijn
variables for the fixed-point binders. -/
inductive LinearMuFormula (Atom : Type u) : Type u where
  | atom : Atom → LinearMuFormula Atom
  | natom : Atom → LinearMuFormula Atom
  | var : ℕ → LinearMuFormula Atom
  | bot : LinearMuFormula Atom
  | top : LinearMuFormula Atom
  | and : LinearMuFormula Atom → LinearMuFormula Atom → LinearMuFormula Atom
  | or : LinearMuFormula Atom → LinearMuFormula Atom → LinearMuFormula Atom
  | next : LinearMuFormula Atom → LinearMuFormula Atom
  | mu : LinearMuFormula Atom → LinearMuFormula Atom
  | nu : LinearMuFormula Atom → LinearMuFormula Atom

namespace LinearMuFormula

variable {Atom : Type u}

/-- Meta-level negation, swapping each connective with its dual. -/
def neg : LinearMuFormula Atom → LinearMuFormula Atom
  | .atom a => .natom a
  | .natom a => .atom a
  | .var n => .var n
  | .bot => .top
  | .top => .bot
  | .and φ ψ => .or (neg φ) (neg ψ)
  | .or φ ψ => .and (neg φ) (neg ψ)
  | .next φ => .next (neg φ)
  | .mu φ => .nu (neg φ)
  | .nu φ => .mu (neg φ)

/-- Negation is an involution. -/
theorem neg_neg : ∀ (φ : LinearMuFormula Atom), (neg (neg φ)) = φ
  | .atom _ => rfl
  | .natom _ => rfl
  | .var _ => rfl
  | .bot => rfl
  | .top => rfl
  | .and _ _ => by simp [neg, neg_neg]
  | .or _ _ => by simp [neg, neg_neg]
  | .next _ => by simp [neg, neg_neg]
  | .mu _ => by simp [neg, neg_neg]
  | .nu _ => by simp [neg, neg_neg]

/-- `φ` is closed at depth `d` when every free variable is below `d`
(de Bruijn): `var n` needs `n < d`, and binders increase the depth. -/
def ClosedAt (d : ℕ) : LinearMuFormula Atom → Prop
  | .atom _ => True
  | .natom _ => True
  | .var n => n < d
  | .bot => True
  | .top => True
  | .and φ ψ => ClosedAt d φ ∧ ClosedAt d ψ
  | .or φ ψ => ClosedAt d φ ∧ ClosedAt d ψ
  | .next φ => ClosedAt d φ
  | .mu φ => ClosedAt (d + 1) φ
  | .nu φ => ClosedAt (d + 1) φ

/-- A formula with no free variables. -/
def Closed (φ : LinearMuFormula Atom) : Prop := ClosedAt 0 φ

/-- The depth of a formula: the length of its longest root-to-leaf path, counting
each connective once. -/
def depth : LinearMuFormula Atom → ℕ
  | .atom _ => 0
  | .natom _ => 0
  | .var _ => 0
  | .bot => 0
  | .top => 0
  | .and φ ψ => 1 + max (depth φ) (depth ψ)
  | .or φ ψ => 1 + max (depth φ) (depth ψ)
  | .next φ => 1 + depth φ
  | .mu φ => 1 + depth φ
  | .nu φ => 1 + depth φ

end LinearMuFormula

/-- Extend an environment under a binder (de Bruijn). -/
def extendEnv (env : ℕ → ℕ → Prop) (S : ℕ → Prop) :
    ℕ → ℕ → Prop
  | 0 => S
  | n + 1 => env n

theorem extendEnv_zero (env : ℕ → ℕ → Prop) (S : ℕ → Prop) :
    extendEnv env S 0 = S := rfl

theorem extendEnv_succ (env : ℕ → ℕ → Prop) (S : ℕ → Prop)
    (n : ℕ) :
    extendEnv env S (n + 1) = env n := rfl

section Satisfaction

variable {Atom : Type*} (val : ℕ → Atom → Prop)

/-- Satisfaction of a linear μ-calculus formula at a position of the word
`val`. `μ X. φ` is the least pre-fixed point of `S ↦ ⟦φ⟧[X ↦ S]`, stated
directly as an infimum over pre-fixed points; `ν X. φ` is the greatest
post-fixed point, stated as a supremum over post-fixed points. -/
def sat (env : ℕ → ℕ → Prop) : LinearMuFormula Atom → (ℕ → Prop)
  | .atom a => fun n => val n a
  | .natom a => fun n => ¬ val n a
  | .var n => env n
  | .bot => fun _ => False
  | .top => fun _ => True
  | .and φ ψ => fun n => sat env φ n ∧ sat env ψ n
  | .or φ ψ => fun n => sat env φ n ∨ sat env ψ n
  | .next φ => fun n => sat env φ (n + 1)
  | .mu φ => fun n => ∀ S : ℕ → Prop,
      (∀ m, sat (extendEnv env S) φ m → S m) → S n
  | .nu φ => fun n => ∃ S : ℕ → Prop,
      (∀ m, S m → sat (extendEnv env S) φ m) ∧ S n

@[simp] theorem sat_atom (env : ℕ → ℕ → Prop) (a : Atom) (n : ℕ) :
    sat val env (.atom a) n ↔ val n a := Iff.rfl

@[simp] theorem sat_natom (env : ℕ → ℕ → Prop) (a : Atom) (n : ℕ) :
    sat val env (.natom a) n ↔ ¬ val n a := Iff.rfl

@[simp] theorem sat_var (env : ℕ → ℕ → Prop) (n m : ℕ) :
    sat val env (.var n) m ↔ env n m := Iff.rfl

@[simp] theorem sat_bot (env : ℕ → ℕ → Prop) (n : ℕ) :
    sat val env (.bot : LinearMuFormula Atom) n ↔ False := Iff.rfl

@[simp] theorem sat_top (env : ℕ → ℕ → Prop) (n : ℕ) :
    sat val env (.top : LinearMuFormula Atom) n ↔ True := Iff.rfl

@[simp] theorem sat_and (env : ℕ → ℕ → Prop) (φ ψ : LinearMuFormula Atom)
    (n : ℕ) :
    sat val env (.and φ ψ) n ↔ sat val env φ n ∧ sat val env ψ n := Iff.rfl

@[simp] theorem sat_or (env : ℕ → ℕ → Prop) (φ ψ : LinearMuFormula Atom)
    (n : ℕ) :
    sat val env (.or φ ψ) n ↔ sat val env φ n ∨ sat val env ψ n := Iff.rfl

@[simp] theorem sat_next (env : ℕ → ℕ → Prop) (φ : LinearMuFormula Atom)
    (n : ℕ) :
    sat val env (.next φ) n ↔ sat val env φ (n + 1) := Iff.rfl

@[simp] theorem sat_mu (env : ℕ → ℕ → Prop) (φ : LinearMuFormula Atom)
    (n : ℕ) :
    sat val env (.mu φ) n ↔ ∀ S : ℕ → Prop,
      (∀ m, sat val (extendEnv env S) φ m → S m) → S n := Iff.rfl

@[simp] theorem sat_nu (env : ℕ → ℕ → Prop) (φ : LinearMuFormula Atom)
    (n : ℕ) :
    sat val env (.nu φ) n ↔ ∃ S : ℕ → Prop,
      (∀ m, S m → sat val (extendEnv env S) φ m) ∧ S n := Iff.rfl

/-- Satisfaction is monotone in the environment. -/
theorem sat_mono_env : ∀ (φ : LinearMuFormula Atom) {env env' : ℕ → ℕ → Prop},
    (∀ n, env n ≤ env' n) → sat val env φ ≤ sat val env' φ := by
  intro φ
  induction φ with
  | atom _ => intro env env' _; exact fun n hn => hn
  | natom _ => intro env env' _; exact fun n hn => hn
  | var n => intro env env' hle; exact hle n
  | bot => intro env env' _; exact fun n hn => hn
  | top => intro env env' _; exact fun n _ => trivial
  | and φ ψ ihφ ihψ =>
      intro env env' hle n hn
      exact ⟨ihφ hle n hn.1, ihψ hle n hn.2⟩
  | or φ ψ ihφ ihψ =>
      intro env env' hle n hn
      exact hn.elim (fun h => Or.inl (ihφ hle n h)) (fun h => Or.inr (ihψ hle n h))
  | next φ ih =>
      intro env env' hle n hn
      exact ih hle (n + 1) hn
  | mu φ ih =>
      intro env env' hle n hn S hS
      apply hn S
      intro m hm
      apply hS m
      exact ih (fun k => by cases k with | zero => exact le_rfl | succ k => exact hle k) m hm
  | nu φ ih =>
      intro env env' hle n hn
      obtain ⟨S, hS, hnS⟩ := hn
      refine ⟨S, ?_, hnS⟩
      intro m hm
      exact ih (fun k => by cases k with | zero => exact le_rfl | succ k => exact hle k) m
        (hS m hm)

/-- Monotonicity in the bound variable's denotation. -/
theorem sat_mono_extend {env : ℕ → ℕ → Prop} {S₁ S₂ : ℕ → Prop} (h : S₁ ≤ S₂)
    (φ : LinearMuFormula Atom) :
    sat val (extendEnv env S₁) φ ≤ sat val (extendEnv env S₂) φ :=
  sat_mono_env val φ (fun n => by cases n with | zero => exact h | succ _ => exact le_rfl)

/-- The least fixed point is a pre-fixed point. -/
theorem mu_pre_fixed (env : ℕ → ℕ → Prop) (φ : LinearMuFormula Atom) :
    sat val (extendEnv env (sat val env (.mu φ))) φ ≤ sat val env (.mu φ) := by
  intro n hn S hS
  apply hS n
  apply sat_mono_extend val _ φ n hn
  intro m hm
  exact hm S hS

/-- The least fixed point is a fixed point (the lower half). -/
theorem mu_le_fixed (env : ℕ → ℕ → Prop) (φ : LinearMuFormula Atom) :
    sat val env (.mu φ) ≤ sat val (extendEnv env (sat val env (.mu φ))) φ := by
  intro n hn
  exact hn _ (sat_mono_extend val (mu_pre_fixed val env φ) φ)

/-- **The μ unfolding**: `μ X. φ ≡ φ[μ X. φ / X]`. -/
theorem sat_mu_unfold (env : ℕ → ℕ → Prop) (φ : LinearMuFormula Atom) :
    sat val env (.mu φ) = sat val (extendEnv env (sat val env (.mu φ))) φ :=
  le_antisymm (mu_le_fixed val env φ) (mu_pre_fixed val env φ)

/-- The greatest fixed point is a post-fixed point (the upper half). -/
theorem nu_post_fixed (env : ℕ → ℕ → Prop) (φ : LinearMuFormula Atom) :
    sat val env (.nu φ) ≤ sat val (extendEnv env (sat val env (.nu φ))) φ := by
  rintro n ⟨S, hS, hnS⟩
  exact sat_mono_extend val (fun m hm => ⟨S, hS, hm⟩) φ n (hS n hnS)

/-- The greatest fixed point is a fixed point (the upper half). -/
theorem nu_le_post_fixed (env : ℕ → ℕ → Prop) (φ : LinearMuFormula Atom) :
    sat val (extendEnv env (sat val env (.nu φ))) φ ≤ sat val env (.nu φ) := by
  intro n hn
  exact ⟨sat val (extendEnv env (sat val env (.nu φ))) φ,
    sat_mono_extend val (nu_post_fixed val env φ) φ, hn⟩

/-- **The ν unfolding**: `ν X. φ ≡ φ[ν X. φ / X]`. -/
theorem sat_nu_unfold (env : ℕ → ℕ → Prop) (φ : LinearMuFormula Atom) :
    sat val env (.nu φ) = sat val (extendEnv env (sat val env (.nu φ))) φ :=
  le_antisymm (nu_post_fixed val env φ) (nu_le_post_fixed val env φ)

/-- **Park induction**: to show `μ X. φ ≤ P`, it suffices that `P` is a
pre-fixed point. -/
theorem mu_induction {env : ℕ → ℕ → Prop} {φ : LinearMuFormula Atom}
    {P : ℕ → Prop}
    (hP : sat val (extendEnv env P) φ ≤ P) : sat val env (.mu φ) ≤ P := by
  intro n hn
  exact hn P hP

/-- **Coinduction**: every post-fixed point is below `ν X. φ`. -/
theorem nu_coinduction {env : ℕ → ℕ → Prop} {φ : LinearMuFormula Atom}
    {P : ℕ → Prop}
    (hP : P ≤ sat val (extendEnv env P) φ) : P ≤ sat val env (.nu φ) := by
  intro n hn
  exact ⟨P, hP, hn⟩

/-- The μ operator as a monotone operator on predicates. -/
def muOp (env : ℕ → ℕ → Prop) (φ : LinearMuFormula Atom) :
    (ℕ → Prop) →o (ℕ → Prop) :=
  ⟨fun S => sat val (extendEnv env S) φ, fun _ _ hle => sat_mono_extend val hle φ⟩

/-- The μ fixed point is Mathlib's least fixed point of the operator. -/
theorem sat_mu_eq_lfp (env : ℕ → ℕ → Prop) (φ : LinearMuFormula Atom) :
    sat val env (.mu φ) = (muOp val env φ).lfp := by
  apply le_antisymm
  · intro n hn
    exact hn _ (le_of_eq (OrderHom.map_lfp (muOp val env φ)))
  · exact OrderHom.lfp_le (muOp val env φ) (mu_pre_fixed val env φ)

/-- The ν fixed point is Mathlib's greatest fixed point of the operator. -/
theorem sat_nu_eq_gfp (env : ℕ → ℕ → Prop) (φ : LinearMuFormula Atom) :
    sat val env (.nu φ) = (muOp val env φ).gfp := by
  apply le_antisymm
  · rintro n ⟨S, hS, hnS⟩
    exact OrderHom.le_gfp (muOp val env φ) hS n hnS
  · intro n hn
    exact ⟨_, le_of_eq (OrderHom.map_gfp (muOp val env φ)).symm, hn⟩

/-- A closed formula does not depend on the environment: environments
agreeing below the depth give the same denotation. -/
theorem sat_closed_env : ∀ (φ : LinearMuFormula Atom) (d : ℕ)
    {env env' : ℕ → ℕ → Prop},
    LinearMuFormula.ClosedAt d φ →
    (∀ n, n < d → env n = env' n) →
    sat val env φ = sat val env' φ := by
  intro φ
  induction φ with
  | atom _ => intro d env env' _ _; rfl
  | natom _ => intro d env env' _ _; rfl
  | var n => intro d env env' hcl hEq; exact hEq n hcl
  | bot => intro d env env' _ _; rfl
  | top => intro d env env' _ _; rfl
  | and φ ψ ihφ ihψ =>
      intro d env env' hcl hEq
      funext n
      show (sat val env φ n ∧ sat val env ψ n) =
        (sat val env' φ n ∧ sat val env' ψ n)
      rw [congrFun (ihφ d hcl.1 hEq) n, congrFun (ihψ d hcl.2 hEq) n]
  | or φ ψ ihφ ihψ =>
      intro d env env' hcl hEq
      funext n
      show (sat val env φ n ∨ sat val env ψ n) =
        (sat val env' φ n ∨ sat val env' ψ n)
      rw [congrFun (ihφ d hcl.1 hEq) n, congrFun (ihψ d hcl.2 hEq) n]
  | next φ ih =>
      intro d env env' hcl hEq
      funext n
      show sat val env φ (n + 1) = sat val env' φ (n + 1)
      exact congrFun (ih d hcl hEq) (n + 1)
  | mu φ ih =>
      intro d env env' hcl hEq
      have key : ∀ S : ℕ → Prop,
          sat val (extendEnv env S) φ = sat val (extendEnv env' S) φ := by
        intro S
        apply ih (d + 1) hcl
        intro n hn
        cases n with
        | zero => rfl
        | succ n => exact hEq n (Nat.lt_of_succ_lt_succ hn)
      have hop : muOp val env φ = muOp val env' φ :=
        OrderHom.ext _ _ (funext fun S => key S)
      rw [sat_mu_eq_lfp val env φ, sat_mu_eq_lfp val env' φ, hop]
  | nu φ ih =>
      intro d env env' hcl hEq
      have key : ∀ S : ℕ → Prop,
          sat val (extendEnv env S) φ = sat val (extendEnv env' S) φ := by
        intro S
        apply ih (d + 1) hcl
        intro n hn
        cases n with
        | zero => rfl
        | succ n => exact hEq n (Nat.lt_of_succ_lt_succ hn)
      have hop : muOp val env φ = muOp val env' φ :=
        OrderHom.ext _ _ (funext fun S => key S)
      rw [sat_nu_eq_gfp val env φ, sat_nu_eq_gfp val env' φ, hop]

end Satisfaction

section Duality

variable {Atom : Type*} (val : ℕ → Atom → Prop)

/-- Complementing an environment commutes with extending it. -/
theorem extendEnv_compl (env : ℕ → ℕ → Prop) (S : ℕ → Prop) :
    (fun n => fun m => ¬ extendEnv env S n m) =
      extendEnv (fun n => fun m => ¬ env n m) (fun m => ¬ S m) := by
  funext n m
  cases n with
  | zero => rfl
  | succ _ => rfl

/-- Complementing a predicate twice returns it. -/
theorem compl_compl (S : ℕ → Prop) :
    (fun m => ¬ ¬ S m) = S := by
  funext m
  exact propext not_not

/-- **Duality**: `⟦¬φ⟧ = (⟦φ⟧)ᶜ` when the environment is complemented. -/
theorem sat_neg : ∀ (φ : LinearMuFormula Atom) (env : ℕ → ℕ → Prop) (n : ℕ),
    sat val (fun k => fun m => ¬ env k m) (LinearMuFormula.neg φ) n ↔
      ¬ sat val env φ n := by
  intro φ
  induction φ with
  | atom a => intro env n; simp [LinearMuFormula.neg]
  | natom a => intro env n; simp [LinearMuFormula.neg]
  | var n => intro env n; simp [LinearMuFormula.neg]
  | bot => intro env n; simp [LinearMuFormula.neg]
  | top => intro env n; simp [LinearMuFormula.neg]
  | and φ ψ ihφ ihψ =>
      intro env n
      simp only [LinearMuFormula.neg, sat_or, sat_and]
      rw [ihφ, ihψ]
      exact not_and_or.symm
  | or φ ψ ihφ ihψ =>
      intro env n
      simp only [LinearMuFormula.neg, sat_and, sat_or]
      rw [ihφ, ihψ]
      exact not_or.symm
  | next φ ih =>
      intro env n
      simp only [LinearMuFormula.neg, sat_next]
      exact ih env (n + 1)
  | mu φ ih =>
      intro env n
      simp only [LinearMuFormula.neg]
      have hF : ∀ S : ℕ → Prop,
          sat val (extendEnv (fun k => fun m => ¬ env k m) (fun m => ¬ ¬ S m))
              (LinearMuFormula.neg φ) =
            fun m => ¬ sat val (extendEnv env (fun m => ¬ S m)) φ m := by
        intro S
        have hcomp : extendEnv (fun k => fun m => ¬ env k m) (fun m => ¬ ¬ S m) =
            fun k => fun m => ¬ extendEnv env (fun m => ¬ S m) k m :=
          (extendEnv_compl env (fun m => ¬ S m)).symm
        funext m
        rw [hcomp]
        exact propext (ih _ m)
      have hF' : ∀ S : ℕ → Prop,
          sat val (extendEnv (fun k => fun m => ¬ env k m) S) (LinearMuFormula.neg φ) =
            fun m => ¬ sat val (extendEnv env (fun m => ¬ S m)) φ m := by
        intro S
        conv_lhs => rw [← compl_compl S]
        exact hF S
      constructor
      · intro hw
        by_contra hcon
        have hle : sat val env (.mu φ) ≤
            fun m => ¬ sat val (fun k => fun m => ¬ env k m) (.nu (LinearMuFormula.neg φ)) m := by
          apply mu_induction
          intro m hm hmem
          rw [sat_nu_unfold] at hmem
          have h2 := congrFun (hF'
            (sat val (fun k => fun m => ¬ env k m) (.nu (LinearMuFormula.neg φ)))) m
          rw [h2] at hmem
          exact hmem hm
        exact hle n hcon hw
      · intro hcon
        exact nu_coinduction (val := val) (env := fun k => fun m => ¬ env k m)
          (φ := LinearMuFormula.neg φ) (P := fun m => ¬ sat val env (.mu φ) m)
          (by
            intro m hm
            have h2 : sat val (extendEnv (fun k => fun m => ¬ env k m)
                (fun m => ¬ sat val env (.mu φ) m)) (LinearMuFormula.neg φ) m =
                ¬ sat val (extendEnv env
                  (fun m => ¬ (fun m => ¬ sat val env (.mu φ) m) m)) φ m :=
              congrFun (hF' (fun m => ¬ sat val env (.mu φ) m)) m
            rw [h2]
            have hPc : (fun m => ¬ (fun m => ¬ sat val env (.mu φ) m) m) =
                sat val env (.mu φ) := by
              funext u
              exact propext not_not
            rw [hPc, ← sat_mu_unfold]
            exact hm) n hcon
  | nu φ ih =>
      intro env n
      simp only [LinearMuFormula.neg]
      have hF : ∀ S : ℕ → Prop,
          sat val (extendEnv (fun k => fun m => ¬ env k m) (fun m => ¬ ¬ S m))
              (LinearMuFormula.neg φ) =
            fun m => ¬ sat val (extendEnv env (fun m => ¬ S m)) φ m := by
        intro S
        have hcomp : extendEnv (fun k => fun m => ¬ env k m) (fun m => ¬ ¬ S m) =
            fun k => fun m => ¬ extendEnv env (fun m => ¬ S m) k m :=
          (extendEnv_compl env (fun m => ¬ S m)).symm
        funext m
        rw [hcomp]
        exact propext (ih _ m)
      have hF' : ∀ S : ℕ → Prop,
          sat val (extendEnv (fun k => fun m => ¬ env k m) S) (LinearMuFormula.neg φ) =
            fun m => ¬ sat val (extendEnv env (fun m => ¬ S m)) φ m := by
        intro S
        conv_lhs => rw [← compl_compl S]
        exact hF S
      constructor
      · intro hw
        by_contra hcon
        have hle : sat val (fun k => fun m => ¬ env k m) (.mu (LinearMuFormula.neg φ)) ≤
            fun m => ¬ sat val env (.nu φ) m := by
          apply mu_induction
          intro m hm hmem
          rw [sat_nu_unfold] at hmem
          have hPc : (fun m => ¬ (fun m => ¬ sat val env (.nu φ) m) m) =
              sat val env (.nu φ) := by
            funext u
            exact propext not_not
          rw [← hPc] at hmem
          have h2 := congrFun (hF' (fun m => ¬ sat val env (.nu φ) m)) m
          rw [h2] at hm
          exact hm hmem
        exact hle n hw hcon
      · intro hcon
        rw [sat_mu]
        intro S hS
        have hSc : (fun m => ¬ S m) ≤ sat val env (.nu φ) := by
          apply nu_coinduction
          intro m hm
          by_contra hnot
          have h2 := congrFun (hF' S) m
          have hFS : sat val (extendEnv (fun k => fun m => ¬ env k m) S)
              (LinearMuFormula.neg φ) m := h2.symm ▸ hnot
          exact hm (hS m hFS)
        by_contra hSw
        exact hcon (hSc n hSw)

end Duality

section EventuallyAlways

variable {Atom : Type*} (val : ℕ → Atom → Prop)

/-- `F p`: `p` holds at some future position. -/
def F (p : Atom) : LinearMuFormula Atom := .mu (.or (.atom p) (.next (.var 0)))

/-- `G p`: `p` holds at every future position. -/
def G (p : Atom) : LinearMuFormula Atom := .nu (.and (.atom p) (.next (.var 0)))

/-- **The linear μ-calculus `F` is eventuality. -/
theorem F_iff (env : ℕ → ℕ → Prop) (p : Atom) (n : ℕ) :
    sat val env (F p) n ↔ ∃ m, n ≤ m ∧ val m p := by
  have hunfold : sat val env (F p) =
      sat val (extendEnv env (sat val env (F p))) (.or (.atom p) (.next (.var 0))) :=
    sat_mu_unfold val env _
  constructor
  · intro hw
    have hle : sat val env (F p) ≤ fun n => ∃ m, n ≤ m ∧ val m p := by
      apply mu_induction
      rintro m (hval | ⟨hnext⟩)
      · exact ⟨m, le_refl m, hval⟩
      · obtain ⟨k, hk, hpk⟩ := hnext
        exact ⟨k, Nat.le_trans (Nat.le_succ m) hk, hpk⟩
    exact hle n hw
  · -- Induction on the distance `k`, with `val (n + k) p`.
    intro hmn
    obtain ⟨m, hmn, hval⟩ := hmn
    have aux : ∀ k : ℕ, ∀ n : ℕ, val (n + k) p → sat val env (F p) n := by
      intro k
      induction k with
      | zero =>
        intro n hval
        rw [hunfold]
        exact Or.inl (by simpa using hval)
      | succ k ih =>
        intro n hval
        rw [hunfold]
        apply Or.inr
        have hval' : val ((n + 1) + k) p := by
          have hEq : (n + 1) + k = n + (k + 1) := by omega
          rw [hEq]
          exact hval
        exact ih (n + 1) hval'
    have hmn' : n + (m - n) = m := by omega
    have hval' : val (n + (m - n)) p := by rw [hmn']; exact hval
    exact aux (m - n) n hval'

/-- **The linear μ-calculus `G` is universality over the future. -/
theorem G_iff (env : ℕ → ℕ → Prop) (p : Atom) (n : ℕ) :
    sat val env (G p) n ↔ ∀ m, n ≤ m → val m p := by
  have hunfold : sat val env (G p) =
      sat val (extendEnv env (sat val env (G p))) (.and (.atom p) (.next (.var 0))) :=
    sat_nu_unfold val env _
  constructor
  · intro hw m hmn
    have aux : ∀ k : ℕ, ∀ n : ℕ, sat val env (G p) n → val (n + k) p := by
      intro k
      induction k with
      | zero =>
        intro n hsat
        rw [hunfold] at hsat
        exact (by simpa using hsat.1)
      | succ k ih =>
        intro n hsat
        rw [hunfold] at hsat
        have h := ih (n + 1) hsat.2
        have hEq : n + 1 + k = n + (k + 1) := by omega
        rwa [hEq] at h
    have hmn' : n + (m - n) = m := by omega
    have h := aux (m - n) n hw
    rwa [hmn'] at h
  · intro hall
    exact nu_coinduction (val := val) (env := env)
      (φ := .and (.atom p) (.next (.var 0)))
      (P := fun n => ∀ m, n ≤ m → val m p)
      (by
        intro n hn
        refine ⟨hn n (le_refl n), fun m hmn => ?_⟩
        exact hn m (Nat.le_trans (Nat.le_succ n) hmn)) n hall

end EventuallyAlways

section Encoding

/-- An injective encoding of linear μ-calculus formulas over `ℕ` atoms as
natural numbers, via the Cantor pairing function `Nat.pair`. -/
def linearMuCode : LinearMuFormula ℕ → ℕ
  | .atom a => Nat.pair 0 a
  | .natom a => Nat.pair 1 a
  | .var n => Nat.pair 2 n
  | .bot => Nat.pair 3 0
  | .top => Nat.pair 4 0
  | .and φ ψ => Nat.pair 5 (Nat.pair (linearMuCode φ) (linearMuCode ψ))
  | .or φ ψ => Nat.pair 6 (Nat.pair (linearMuCode φ) (linearMuCode ψ))
  | .next φ => Nat.pair 7 (linearMuCode φ)
  | .mu φ => Nat.pair 8 (linearMuCode φ)
  | .nu φ => Nat.pair 9 (linearMuCode φ)

/-- The encoding is injective. -/
theorem linearMuCode_injective : Function.Injective linearMuCode := by
  intro φ
  induction φ with
  | atom a =>
      intro ψ h
      cases ψ with
      | atom b => simp only [linearMuCode, Nat.pair_eq_pair] at h; rw [h.2]
      | natom b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | var b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | bot => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | top => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | and _ _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | or _ _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | next _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | mu _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | nu _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
  | natom a =>
      intro ψ h
      cases ψ with
      | atom b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | natom b => simp only [linearMuCode, Nat.pair_eq_pair] at h; rw [h.2]
      | var b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | bot => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | top => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | and _ _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | or _ _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | next _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | mu _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | nu _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
  | var n =>
      intro ψ h
      cases ψ with
      | atom b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | natom b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | var b => simp only [linearMuCode, Nat.pair_eq_pair] at h; rw [h.2]
      | bot => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | top => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | and _ _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | or _ _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | next _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | mu _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | nu _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
  | bot =>
      intro ψ h
      cases ψ with
      | atom b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | natom b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | var b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | bot => rfl
      | top => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | and _ _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | or _ _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | next _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | mu _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | nu _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
  | top =>
      intro ψ h
      cases ψ with
      | atom b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | natom b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | var b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | bot => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | top => rfl
      | and _ _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | or _ _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | next _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | mu _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | nu _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
  | and φ ψ ihφ ihψ =>
      intro ψ' h
      cases ψ' with
      | atom b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | natom b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | var b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | bot => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | top => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | and φ' ψ' =>
          have h1 : linearMuCode φ = linearMuCode φ' :=
            (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp h).2).1
          have h2 : linearMuCode ψ = linearMuCode ψ' :=
            (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp h).2).2
          rw [ihφ h1, ihψ h2]
      | or _ _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | next _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | mu _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | nu _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
  | or φ ψ ihφ ihψ =>
      intro ψ' h
      cases ψ' with
      | atom b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | natom b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | var b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | bot => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | top => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | and _ _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | or φ' ψ' =>
          have h1 : linearMuCode φ = linearMuCode φ' :=
            (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp h).2).1
          have h2 : linearMuCode ψ = linearMuCode ψ' :=
            (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp h).2).2
          rw [ihφ h1, ihψ h2]
      | next _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | mu _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | nu _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
  | next φ ih =>
      intro ψ' h
      cases ψ' with
      | atom b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | natom b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | var b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | bot => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | top => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | and _ _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | or _ _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | next φ' =>
          have h1 : linearMuCode φ = linearMuCode φ' :=
            (Nat.pair_eq_pair.mp h).2
          rw [ih h1]
      | mu _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | nu _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
  | mu φ ih =>
      intro ψ' h
      cases ψ' with
      | atom b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | natom b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | var b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | bot => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | top => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | and _ _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | or _ _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | next _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | mu φ' =>
          have h1 : linearMuCode φ = linearMuCode φ' :=
            (Nat.pair_eq_pair.mp h).2
          rw [ih h1]
      | nu _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
  | nu φ ih =>
      intro ψ' h
      cases ψ' with
      | atom b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | natom b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | var b => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | bot => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | top => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | and _ _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | or _ _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | next _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | mu _ => exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
      | nu φ' =>
          have h1 : linearMuCode φ = linearMuCode φ' :=
            (Nat.pair_eq_pair.mp h).2
          rw [ih h1]

/-- Fuelled decoding of a `linearMuCode` number back to a formula. The fuel bounds
the recursion depth; `linearMuDecode` supplies fuel `c + 1`, which exceeds every
formula's depth (see `linearDepth_le_code`). -/
def linearMuDecodeFuel : ℕ → ℕ → Option (LinearMuFormula ℕ)
  | 0, _ => none
  | fuel + 1, c =>
    match Nat.unpair c with
    | (0, a) => some (.atom a)
    | (1, a) => some (.natom a)
    | (2, n) => some (.var n)
    | (3, _) => some .bot
    | (4, _) => some .top
    | (5, r) =>
      match Nat.unpair r with
      | (c₁, c₂) =>
        match linearMuDecodeFuel fuel c₁, linearMuDecodeFuel fuel c₂ with
        | some f₁, some f₂ => some (.and f₁ f₂)
        | _, _ => none
    | (6, r) =>
      match Nat.unpair r with
      | (c₁, c₂) =>
        match linearMuDecodeFuel fuel c₁, linearMuDecodeFuel fuel c₂ with
        | some f₁, some f₂ => some (.or f₁ f₂)
        | _, _ => none
    | (7, c₁) => .next <$> linearMuDecodeFuel fuel c₁
    | (8, c₁) => .mu <$> linearMuDecodeFuel fuel c₁
    | (9, c₁) => .nu <$> linearMuDecodeFuel fuel c₁
    | (_, _) => none

/-- Decode a `linearMuCode` number back to the formula it encodes. -/
def linearMuDecode (c : ℕ) : Option (LinearMuFormula ℕ) :=
  linearMuDecodeFuel (c + 1) c

/-- A formula's depth is at most its code: pairing dominates each component
(`Nat.add_le_pair`). -/
theorem linearDepth_le_code : ∀ φ : LinearMuFormula ℕ,
    LinearMuFormula.depth φ ≤ linearMuCode φ := by
  intro φ
  induction φ with
  | atom a => simp [LinearMuFormula.depth, linearMuCode]
  | natom a => simp [LinearMuFormula.depth, linearMuCode]
  | var n => simp [LinearMuFormula.depth, linearMuCode]
  | bot => simp [LinearMuFormula.depth, linearMuCode]
  | top => simp [LinearMuFormula.depth, linearMuCode]
  | and φ ψ ihφ ihψ =>
      calc LinearMuFormula.depth (.and φ ψ)
          = 1 + max (LinearMuFormula.depth φ) (LinearMuFormula.depth ψ) := rfl
      _ ≤ 1 + (linearMuCode φ + linearMuCode ψ) := by
          have h1 := ihφ
          have h2 := ihψ
          omega
      _ ≤ 5 + Nat.pair (linearMuCode φ) (linearMuCode ψ) := by
          have h := Nat.add_le_pair (linearMuCode φ) (linearMuCode ψ)
          omega
      _ ≤ Nat.pair 5 (Nat.pair (linearMuCode φ) (linearMuCode ψ)) :=
          Nat.add_le_pair 5 _
      _ = linearMuCode (.and φ ψ) := rfl
  | or φ ψ ihφ ihψ =>
      calc LinearMuFormula.depth (.or φ ψ)
          = 1 + max (LinearMuFormula.depth φ) (LinearMuFormula.depth ψ) := rfl
      _ ≤ 1 + (linearMuCode φ + linearMuCode ψ) := by
          have h1 := ihφ
          have h2 := ihψ
          omega
      _ ≤ 6 + Nat.pair (linearMuCode φ) (linearMuCode ψ) := by
          have h := Nat.add_le_pair (linearMuCode φ) (linearMuCode ψ)
          omega
      _ ≤ Nat.pair 6 (Nat.pair (linearMuCode φ) (linearMuCode ψ)) :=
          Nat.add_le_pair 6 _
      _ = linearMuCode (.or φ ψ) := rfl
  | next φ ih =>
      calc LinearMuFormula.depth (.next φ) = 1 + LinearMuFormula.depth φ := rfl
      _ ≤ 1 + linearMuCode φ := by have h := ih; omega
      _ ≤ 7 + linearMuCode φ := by omega
      _ ≤ Nat.pair 7 (linearMuCode φ) := Nat.add_le_pair 7 _
      _ = linearMuCode (.next φ) := rfl
  | mu φ ih =>
      calc LinearMuFormula.depth (.mu φ) = 1 + LinearMuFormula.depth φ := rfl
      _ ≤ 1 + linearMuCode φ := by have h := ih; omega
      _ ≤ 8 + linearMuCode φ := by omega
      _ ≤ Nat.pair 8 (linearMuCode φ) := Nat.add_le_pair 8 _
      _ = linearMuCode (.mu φ) := rfl
  | nu φ ih =>
      calc LinearMuFormula.depth (.nu φ) = 1 + LinearMuFormula.depth φ := rfl
      _ ≤ 1 + linearMuCode φ := by have h := ih; omega
      _ ≤ 9 + linearMuCode φ := by omega
      _ ≤ Nat.pair 9 (linearMuCode φ) := Nat.add_le_pair 9 _
      _ = linearMuCode (.nu φ) := rfl

/-- Decoding inverts encoding, with enough fuel. -/
theorem linearMuDecodeFuel_linearMuCode : ∀ (φ : LinearMuFormula ℕ) (fuel : ℕ),
    LinearMuFormula.depth φ ≤ fuel →
    linearMuDecodeFuel (fuel + 1) (linearMuCode φ) = some φ := by
  intro φ
  induction φ with
  | atom a => intro fuel _; simp [linearMuDecodeFuel, linearMuCode, Nat.unpair_pair]
  | natom a => intro fuel _; simp [linearMuDecodeFuel, linearMuCode, Nat.unpair_pair]
  | var n => intro fuel _; simp [linearMuDecodeFuel, linearMuCode, Nat.unpair_pair]
  | bot => intro fuel _; simp [linearMuDecodeFuel, linearMuCode, Nat.unpair_pair]
  | top => intro fuel _; simp [linearMuDecodeFuel, linearMuCode, Nat.unpair_pair]
  | and φ ψ ihφ ihψ =>
      intro fuel hfuel
      cases fuel with
      | zero => simp only [LinearMuFormula.depth] at hfuel; omega
      | succ fuel' =>
        have hφ : LinearMuFormula.depth φ ≤ fuel' := by
          simp only [LinearMuFormula.depth] at hfuel; omega
        have hψ : LinearMuFormula.depth ψ ≤ fuel' := by
          simp only [LinearMuFormula.depth] at hfuel; omega
        unfold linearMuDecodeFuel
        simp only [linearMuCode, Nat.unpair_pair]
        rw [ihφ fuel' hφ, ihψ fuel' hψ]
  | or φ ψ ihφ ihψ =>
      intro fuel hfuel
      cases fuel with
      | zero => simp only [LinearMuFormula.depth] at hfuel; omega
      | succ fuel' =>
        have hφ : LinearMuFormula.depth φ ≤ fuel' := by
          simp only [LinearMuFormula.depth] at hfuel; omega
        have hψ : LinearMuFormula.depth ψ ≤ fuel' := by
          simp only [LinearMuFormula.depth] at hfuel; omega
        unfold linearMuDecodeFuel
        simp only [linearMuCode, Nat.unpair_pair]
        rw [ihφ fuel' hφ, ihψ fuel' hψ]
  | next φ ih =>
      intro fuel hfuel
      cases fuel with
      | zero => simp only [LinearMuFormula.depth] at hfuel; omega
      | succ fuel' =>
        have hφ : LinearMuFormula.depth φ ≤ fuel' := by
          simp only [LinearMuFormula.depth] at hfuel; omega
        unfold linearMuDecodeFuel
        simp only [linearMuCode, Nat.unpair_pair]
        rw [ih fuel' hφ]
        rfl
  | mu φ ih =>
      intro fuel hfuel
      cases fuel with
      | zero => simp only [LinearMuFormula.depth] at hfuel; omega
      | succ fuel' =>
        have hφ : LinearMuFormula.depth φ ≤ fuel' := by
          simp only [LinearMuFormula.depth] at hfuel; omega
        unfold linearMuDecodeFuel
        simp only [linearMuCode, Nat.unpair_pair]
        rw [ih fuel' hφ]
        rfl
  | nu φ ih =>
      intro fuel hfuel
      cases fuel with
      | zero => simp only [LinearMuFormula.depth] at hfuel; omega
      | succ fuel' =>
        have hφ : LinearMuFormula.depth φ ≤ fuel' := by
          simp only [LinearMuFormula.depth] at hfuel; omega
        unfold linearMuDecodeFuel
        simp only [linearMuCode, Nat.unpair_pair]
        rw [ih fuel' hφ]
        rfl

/-- Decoding inverts encoding. -/
theorem linearMuDecode_linearMuCode (φ : LinearMuFormula ℕ) :
    linearMuDecode (linearMuCode φ) = some φ :=
  linearMuDecodeFuel_linearMuCode φ (linearMuCode φ) (linearDepth_le_code φ)

end Encoding

end LinearMuCalculus
end Modal
end Cslib
