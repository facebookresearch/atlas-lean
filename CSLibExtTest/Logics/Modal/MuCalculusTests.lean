/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.MuCalculus

/-!
# Modal μ-calculus tests

Closed checks on the two-world model `0 → 1`, `1 → 1`, with the atom true only at
`1`: `EF p` holds at `0` (via the successor), `AG p` fails at `0` (the world `0`
itself is reachable and does not satisfy `p`), negation is an involution, and the
duality theorem instantiates. Axiom audit follows.
-/

namespace Cslib.Modal.MuCalculus

/-- The two-world model `0 → 1`, `1 → 1`, with the atom true only at `1`. -/
def twoWorld : KripkeModel (Fin 2) Unit :=
  ⟨⟨0⟩, fun w v => (w = 0 ∧ v = 1) ∨ (w = 1 ∧ v = 1), fun w _ => w = 1⟩

example : sat twoWorld (fun _ _ => False) (EF ()) 0 :=
  (EF_iff_reachable twoWorld (fun _ _ => False) () 0).mpr
    ⟨1, Relation.ReflTransGen.single (Or.inl ⟨rfl, rfl⟩), rfl⟩

example : ¬ sat twoWorld (fun _ _ => False) (AG ()) 0 := by
  intro h
  have hall := (AG_iff_forall_reachable twoWorld (fun _ _ => False) () 0).mp h 0
    Relation.ReflTransGen.refl
  exact (by decide : ¬ (0 : Fin 2) = 1) hall

example (φ : MuFormula Unit) : MuFormula.neg (MuFormula.neg φ) = φ :=
  MuFormula.neg_neg φ

-- Nested binders shift: `μ X. μ Y. X = ⊥` and `ν X. ν Y. X = ⊤`. Under the old
-- `Function.update env 0` semantics the first was `env 1` instead.
example (env : ℕ → Fin 2 → Prop) (w : Fin 2) :
    ¬ sat twoWorld env (.mu (.mu (.var 1))) w := by
  rw [mu_mu_var_one_eq_bot]
  exact fun h => h

example (env : ℕ → Fin 2 → Prop) (w : Fin 2) :
    sat twoWorld env (.nu (.nu (.var 1))) w := by
  rw [nu_nu_var_one_eq_top]
  trivial

#print axioms mu_mu_var_one_eq_bot
#print axioms nu_nu_var_one_eq_top

example (φ : MuFormula Unit) (w : Fin 2) :
    sat twoWorld (fun _ _ => ¬ True) (MuFormula.neg φ) w ↔
      ¬ sat twoWorld (fun _ _ => True) φ w :=
  sat_neg twoWorld φ (fun _ _ => True) w

#print axioms sat_neg
#print axioms sat_mu_unfold
#print axioms sat_nu_unfold
#print axioms EF_iff_reachable
#print axioms AG_iff_forall_reachable

end Cslib.Modal.MuCalculus
