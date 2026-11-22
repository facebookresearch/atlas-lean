/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PCF: computational adequacy
-/
module

public import CSLibExt.Languages.LambdaCalculus.PCF.Soundness

/-!
# Computational adequacy

Plotkin's adequacy theorem for PCF (*LCF considered as a programming language*,
TCS 5, 1977), in the logical-relations proof of Streicher (*Domain-Theoretic
Foundations of Functional Programming*, 2006): a closed term of ground type
evaluates to the numeral `n` exactly when it denotes `n`.

The proof uses the formal-approximation relation `Approx A d t` between
elements of the domain of `A` and closed terms of type `A`: at the ground type,
every value `n` of `d` is the result of evaluating `t`; at `A → B`, related
arguments give related results. The relation contains `⊥`, is closed under
suprema of chains (`approx_ωSup`), and under head expansion (`approx_expand`).
The fundamental lemma (`approx_denote`) relates every term, under a closing
substitution, to its denotation; the fixed-point case climbs the Kleene chain.

* `adequacy`: if `n ∈ ⟦t⟧` then `t ⇓ n`.
* `eval_numeral_iff`: `t ⇓ n ↔ ⟦t⟧ = some n`.
* `terminates_iff_dom`: a closed ground term terminates exactly when its
  denotation is defined.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.PCF

open scoped CslibStlc
open OmegaCompletePartialOrder

namespace Tm

/-- The formal-approximation relation between denotations and closed terms. -/
def Approx : (A : Ty) → Ty.dom A → Tm [] A → Prop
  | .base _, d, t => ∀ n : ℕ, n ∈ (d : Part ℕ) → Eval t (numeral n)
  | .arr A B, f, t => ∀ d s, Approx A d s → Approx B (f d) (.app t s)

/-- `⊥` approximates every term. -/
theorem approx_bot : ∀ (A : Ty) (t : Tm [] A), Approx A ⊥ t
  | .base _, _ => fun n hn => absurd hn (Part.notMem_none n)
  | .arr _ B, _ => fun _ _ _ => approx_bot B _

/-- The approximation relation is closed under suprema of chains. -/
theorem approx_ωSup : ∀ (A : Ty) (t : Tm [] A) (c : Chain (Ty.dom A)),
    (∀ i, Approx A (c i) t) → Approx A (ωSup c) t
  | .base _, t, c, h => by
      intro n hn
      obtain ⟨i, hi⟩ := (Part.mem_ωSup n c).mp hn
      exact h i n (hi ▸ Part.mem_some n)
  | .arr A B, t, c, h => by
      intro d s hds
      change Approx B (ContinuousHom.ωSup c d) (.app t s)
      rw [ContinuousHom.ωSup_apply]
      exact approx_ωSup B _ _ fun i => h i d s hds

/-- Head expansion: a term that evaluates to whatever another term evaluates to
inherits its approximations. -/
theorem approx_expand : ∀ (A : Ty) {t t' : Tm [] A} {d : Ty.dom A},
    (∀ v, Eval t' v → Eval t v) → Approx A d t' → Approx A d t
  | .base _, _, _, _, hexp, h => fun n hn => hexp _ (h n hn)
  | .arr A B, t, t', _, hexp, h => fun d s hds =>
      approx_expand B (fun v hv => by
        cases hv with
        | app hf hb => exact .app (hexp _ hf) hb) (h d s hds)

/-- The fundamental lemma: under a closing substitution whose terms are
approximated by the environment, every term is approximated by its
denotation. -/
theorem approx_denote {Γ : List Ty} {A : Ty} (t : Tm Γ A) (η : Env Γ) (σ : Sub Γ [])
    (hσ : ∀ {B} (x : Var Γ B), Approx B (Env.lookup x η) (σ x)) :
    Approx A (denote t η) (subst σ t) := by
  induction t with
  | var x => exact hσ x
  | @lam Γ A B body ih =>
      intro d s hds
      refine approx_expand B (fun v hv => .app .lam hv) ?_
      rw [instantiate_subst_lift]
      refine ih ((η, d) : Env (A :: Γ)) (Sub.cons s σ) ?_
      intro C x
      cases x with
      | zero => exact hds
      | succ x => exact hσ x
  | app f a ihf iha => exact ihf η σ hσ _ _ (iha η σ hσ)
  | zero =>
      intro n hn
      rw [Part.mem_some_iff.mp hn]
      exact .zero
  | succ t ih =>
      intro n hn
      obtain ⟨m, hm, rfl⟩ := (Part.mem_map_iff Nat.succ).mp hn
      exact .succ (ih η σ hσ m hm)
  | pred t ih =>
      intro n hn
      obtain ⟨m, hm, rfl⟩ := (Part.mem_map_iff Nat.pred).mp hn
      cases m with
      | zero => exact .predZero (ih η σ hσ 0 hm)
      | succ m => exact .predSucc (ih η σ hσ (m + 1) hm)
  | ifz t s₁ s₂ iht ih₁ ih₂ =>
      intro n hn
      obtain ⟨m, hm, hn'⟩ := Part.mem_bind_iff.mp hn
      cases m with
      | zero =>
          simp only [↓reduceIte] at hn'
          exact .ifzZero (iht η σ hσ 0 hm) (ih₁ η σ hσ n hn')
      | succ m =>
          simp only [Nat.add_one_ne_zero, ↓reduceIte] at hn'
          exact .ifzSucc (iht η σ hσ (m + 1) hm) (ih₂ η σ hσ n hn')
  | @fix Γ A t ih =>
      rw [denote_fix, subst_fix, ContinuousHom.lfp_def]
      refine approx_ωSup A _ (fixedPoints.iterateChain (denote t η) ⊥ bot_le) fun k => ?_
      induction k with
      | zero => exact approx_bot A _
      | succ k ihk =>
          change Approx A ((denote t η)^[k + 1] ⊥) _
          rw [Function.iterate_succ_apply']
          exact approx_expand A (fun v hv => .fix hv) (ih η σ hσ _ _ ihk)

/-- Computational adequacy: if a closed term of ground type denotes `n`, it
evaluates to the numeral `n`. -/
theorem adequacy {t : Tm [] .nat} {n : ℕ} (h : n ∈ (denote t PUnit.unit : Part ℕ)) :
    Eval t (numeral n) := by
  have := approx_denote t PUnit.unit Sub.id (fun x => nomatch x) n h
  rwa [subst_id] at this

/-- A closed term of ground type evaluates to the numeral `n` exactly when it
denotes `n`. -/
theorem eval_numeral_iff {t : Tm [] .nat} {n : ℕ} :
    Eval t (numeral n) ↔ denote t PUnit.unit = Part.some n :=
  ⟨fun h => h.denote_numeral PUnit.unit,
    fun h => adequacy (h ▸ Part.mem_some n)⟩

/-- A closed term of ground type terminates exactly when its denotation is
defined. -/
theorem terminates_iff_dom {t : Tm [] .nat} :
    (∃ v, Eval t v) ↔ (denote t PUnit.unit : Part ℕ).Dom := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨n, rfl⟩ := hv.value.eq_numeral
    rw [hv.denote_numeral]
    trivial
  · intro hdom
    exact ⟨_, adequacy (Part.get_mem hdom)⟩

end Tm

end Cslib.Languages.LambdaCalculus.PCF
