/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.MuCalculus

/-!
# Modal μ-calculus: worked examples

Concrete usage of the μ-calculus semantics in
`CSLibExt/Logics/Modal/MuCalculus.lean`, on two tiny models.

* On the chain `false → true` with `p` true only at `true`, `EF p` holds at
  `false` (reachability) while `AG p` fails there.
* On the self-loop model where every world sees itself and `p` holds
  everywhere, `EG p` holds, proved by coinduction (`nu_coinduction`) with
  the post-fixed point `⊤`.
* The nested-binder calculation `μ X. μ Y. X = ⊥` (`mu_mu_var_one_eq_bot`)
  evaluated on a concrete model.
-/

@[expose] public section

namespace Cslib
namespace Modal
namespace MuCalculus
namespace Examples

/-- The chain `false → true`, with `p` true only at `true`. -/
def chain : KripkeModel Bool Unit where
  nonempty_world := ⟨false⟩
  rel := fun w v => w = false ∧ v = true
  valuation := fun w _ => w = true

/-- `EF p` holds at `false` on the chain: `true` is reachable and `p`
holds there. -/
theorem chain_ef_atom_false (env : ℕ → Bool → Prop) :
    sat chain env (EF ()) false := by
  rw [EF_iff_reachable]
  exact ⟨true, Relation.ReflTransGen.single ⟨rfl, rfl⟩, rfl⟩

/-- `AG p` fails at `false` on the chain: `p` already fails at `false`
itself, which is reachable in zero steps. -/
theorem chain_not_ag_atom_false (env : ℕ → Bool → Prop) :
    ¬ sat chain env (AG ()) false := by
  rw [AG_iff_forall_reachable]
  intro h
  exact Bool.false_ne_true (h false Relation.ReflTransGen.refl)

/-- The self-loop model: every world sees itself, `p` holds everywhere. -/
def loop : KripkeModel Bool Unit where
  nonempty_world := ⟨false⟩
  rel := fun w v => w = v
  valuation := fun _ _ => True

/-- `EG p`: `p` holds now and at some successor, forever. -/
def EG (p : Unit) : MuFormula Unit := .nu (.and (.atom p) (.dia (.var 0)))

/-- `EG p` holds at `false` on the loop model: `⊤` is a post-fixed point
of `S ↦ p ∧ ◇S`, since every world satisfies `p` and sees itself. -/
theorem loop_eg_atom_false (env : ℕ → Bool → Prop) :
    sat loop env (EG ()) false :=
  nu_coinduction (M := loop) (env := env)
    (φ := .and (.atom ()) (.dia (.var 0))) (P := fun _ => True)
    (by
      intro w _
      refine ⟨True.intro, ?_⟩
      exact ⟨w, rfl, True.intro⟩) false True.intro

/-- On any model, `μ X. μ Y. X` denotes `⊥`: the inner `var 1` refers to
the outer binder. -/
theorem mu_mu_var_one_false (M : KripkeModel Bool Unit)
    (env : ℕ → Bool → Prop) (w : Bool) :
    ¬ sat M env (.mu (.mu (.var 1))) w := by
  rw [mu_mu_var_one_eq_bot]
  exact id

end Examples
end MuCalculus
end Modal
end Cslib
