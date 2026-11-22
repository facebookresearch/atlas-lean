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
  `OrderHom.gfp` (used by `CSLibExt/Logics/CTL/Basic.lean` for `EF` / `EG`).
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

/-- Formulas of the modal μ-calculus over atoms `Atom`, with de Bruijn variables for the
fixed-point binders. `natom a` is a negated atom, present so that the meta-level negation
`neg` is an involution. -/
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

/-- Meta-level negation, swapping each connective with its dual. -/
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

/-- Negation is an involution. -/
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

/-- Extend an environment under a binder (de Bruijn): slot `0` gets the bound
predicate, and slot `n + 1` gets the old slot `n`, so `var 1` inside a binder
refers to the enclosing binder. -/
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

/-- Satisfaction of a μ-calculus formula as a predicate on worlds. `μ X. φ` is the least
pre-fixed point of `S ↦ ⟦φ⟧[X ↦ S]`, stated directly as an infimum over pre-fixed points;
`ν X. φ` is the greatest post-fixed point, stated as a supremum over post-fixed points. -/
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

/-- Satisfaction is monotone in the environment: enlarging every variable's denotation can
only enlarge a formula's denotation. -/
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

/-- Monotonicity in the bound variable's denotation, through extending the environment. -/
theorem sat_mono_extend {env : ℕ → World → Prop} {S₁ S₂ : World → Prop} (h : S₁ ≤ S₂)
    (φ : MuFormula Atom) :
    sat M (extendEnv env S₁) φ ≤ sat M (extendEnv env S₂) φ :=
  sat_mono_env M φ (fun n => by cases n with | zero => exact h | succ _ => exact le_rfl)

/-- The least fixed point is a pre-fixed point. -/
theorem mu_pre_fixed (env : ℕ → World → Prop) (φ : MuFormula Atom) :
    sat M (extendEnv env (sat M env (.mu φ))) φ ≤ sat M env (.mu φ) := by
  intro w hw S hS
  apply hS w
  apply sat_mono_extend M _ φ w hw
  intro u hu
  exact hu S hS

/-- The least fixed point is a fixed point (the lower half). -/
theorem mu_le_fixed (env : ℕ → World → Prop) (φ : MuFormula Atom) :
    sat M env (.mu φ) ≤ sat M (extendEnv env (sat M env (.mu φ))) φ := by
  intro w hw
  exact hw _ (sat_mono_extend M (mu_pre_fixed M env φ) φ)

/-- **The μ unfolding**: `μ X. φ ≡ φ[μ X. φ / X]`. -/
theorem sat_mu_unfold (env : ℕ → World → Prop) (φ : MuFormula Atom) :
    sat M env (.mu φ) = sat M (extendEnv env (sat M env (.mu φ))) φ :=
  le_antisymm (mu_le_fixed M env φ) (mu_pre_fixed M env φ)

/-- The greatest fixed point is a post-fixed point (the upper half). -/
theorem nu_post_fixed (env : ℕ → World → Prop) (φ : MuFormula Atom) :
    sat M env (.nu φ) ≤ sat M (extendEnv env (sat M env (.nu φ))) φ := by
  rintro w ⟨S, hS, hwS⟩
  exact sat_mono_extend M (fun u hu => ⟨S, hS, hu⟩) φ w (hS w hwS)

/-- The greatest fixed point is a fixed point (the upper half). -/
theorem nu_le_post_fixed (env : ℕ → World → Prop) (φ : MuFormula Atom) :
    sat M (extendEnv env (sat M env (.nu φ))) φ ≤ sat M env (.nu φ) := by
  intro w hw
  exact ⟨sat M (extendEnv env (sat M env (.nu φ))) φ,
    sat_mono_extend M (nu_post_fixed M env φ) φ, hw⟩

/-- **The ν unfolding**: `ν X. φ ≡ φ[ν X. φ / X]`. -/
theorem sat_nu_unfold (env : ℕ → World → Prop) (φ : MuFormula Atom) :
    sat M env (.nu φ) = sat M (extendEnv env (sat M env (.nu φ))) φ :=
  le_antisymm (nu_post_fixed M env φ) (nu_le_post_fixed M env φ)

/-- **Park induction**: to show `μ X. φ ≤ P`, it suffices that `P` is a pre-fixed point. -/
theorem mu_induction {env : ℕ → World → Prop} {φ : MuFormula Atom} {P : World → Prop}
    (hP : sat M (extendEnv env P) φ ≤ P) : sat M env (.mu φ) ≤ P := by
  intro w hw
  exact hw P hP

/-- **Coinduction**: every post-fixed point is below `ν X. φ`. -/
theorem nu_coinduction {env : ℕ → World → Prop} {φ : MuFormula Atom} {P : World → Prop}
    (hP : P ≤ sat M (extendEnv env P) φ) : P ≤ sat M env (.nu φ) := by
  intro w hw
  exact ⟨P, hP, hw⟩

/-- The μ operator as a monotone operator on predicates. -/
def muOp (env : ℕ → World → Prop) (φ : MuFormula Atom) :
    (World → Prop) →o (World → Prop) :=
  ⟨fun S => sat M (extendEnv env S) φ, fun _ _ hle => sat_mono_extend M hle φ⟩

/-- The μ fixed point is Mathlib's least fixed point of the operator. -/
theorem sat_mu_eq_lfp (env : ℕ → World → Prop) (φ : MuFormula Atom) :
    sat M env (.mu φ) = (muOp M env φ).lfp := by
  apply le_antisymm
  · intro w hw
    exact hw _ (le_of_eq (OrderHom.map_lfp (muOp M env φ)))
  · exact OrderHom.lfp_le (muOp M env φ) (mu_pre_fixed M env φ)

/-- The ν fixed point is Mathlib's greatest fixed point of the operator. -/
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

/-- Complementing an environment commutes with extending it. -/
theorem extendEnv_compl (env : ℕ → World → Prop) (S : World → Prop) :
    (fun n => fun w => ¬ extendEnv env S n w) =
      extendEnv (fun n => fun w => ¬ env n w) (fun w => ¬ S w) := by
  funext n w
  cases n with
  | zero => rfl
  | succ _ => rfl

/-- Complementing a predicate twice returns it. -/
theorem compl_compl (S : World → Prop) :
    (fun w => ¬ ¬ S w) = S := by
  funext w
  exact propext not_not

/-- **Duality**: `⟦¬φ⟧ = (⟦φ⟧)ᶜ` when the environment is complemented. -/
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

/-- `EF p`: some reachable state satisfies `p`. -/
def EF (p : Atom) : MuFormula Atom := .mu (.or (.atom p) (.dia (.var 0)))

/-- `AG p`: every reachable state satisfies `p`. -/
def AG (p : Atom) : MuFormula Atom := .nu (.and (.atom p) (.box (.var 0)))

/-- **The μ-calculus `EF` is reachability. -/
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

/-- **The μ-calculus `AG` is universal reachability. -/
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

/-- **Nested binders shift**: `μ X. μ Y. X` is `⊥`, since the inner binder's `var 1`
refers to the outer binder. Under the old `Function.update env 0` semantics this
was `env 1` instead. -/
theorem mu_mu_var_one_eq_bot (env : ℕ → World → Prop) :
    sat M env (.mu (.mu (.var 1))) = fun _ => False := by
  apply le_antisymm
  · apply mu_induction
    intro w hw
    exact hw _ (fun v hv => hv)
  · intro w hw
    exact False.elim hw

/-- **Nested binders shift**: `ν X. ν Y. X` is `⊤`, the dual of `mu_mu_var_one_eq_bot`. -/
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
