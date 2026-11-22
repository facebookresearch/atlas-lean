/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.Filtration

@[expose] public section

/-! # Tests for filtration, the finite model property and decidability of K -/

namespace Cslib.Modal.FiltrationTests

open Formula

inductive Atom where
  | p
  | q
  deriving DecidableEq

/-- The subformulas of `□p → p`. -/
example : (axiomT (atom Atom.p)).sub = {axiomT (atom .p), box (atom .p), atom .p} := by
  decide

/-- `evalFin` on a two-world model: the empty world sees only the world where `p` holds. -/
example : evalFin {∅, {atom Atom.p}} {(∅, {atom Atom.p})} ∅ (box (atom .p)) = true := by
  decide

/-- The decision procedure, run by the kernel through the instance: `⊥` and an atom are not
K-theorems. (Positive cases are far costlier: every theorem has at least two subformulas, so the
procedure checks tens of thousands of relations.) -/
example : ¬Derivable (Axioms.K : Set (Formula Atom)) .bot := by decide +kernel

example : ¬Derivable (Axioms.K : Set (Formula Atom)) (atom .p) := by decide +kernel

/-- K-provability is decidable. -/
example (phi : Formula Atom) : Decidable (Derivable Axioms.K phi) := inferInstance

/-- The successor relation on `ℕ`, with every atom true at even numbers: an infinite model. -/
def succModel : KripkeModel ℕ Atom where
  nonempty_world := ⟨0⟩
  rel n m := m = n + 1
  valuation n _ := n % 2 = 0

/-- Its filtration through the subformulas of `□p → p` is finite, with at most `2 ^ 3` worlds, and
agrees with it on `□p → p` at every world. -/
example : (filtrationWorlds succModel (axiomT (atom Atom.p))).card ≤ 2 ^ 3 := by
  have h := card_filtrationWorlds_le succModel (axiomT (atom Atom.p))
  have hsub : (axiomT (atom Atom.p)).sub.card = 3 := by decide
  rwa [hsub] at h

example (n : ℕ) :
    (filtration succModel (axiomT (atom Atom.p))).Satisfies
        ⟨subType succModel _ n, subType_mem_filtrationWorlds succModel _ n⟩ (axiomT (atom .p)) ↔
      succModel.Satisfies n (axiomT (atom .p)) :=
  satisfies_filtration_iff succModel _ (mem_sub_self _) n

/-- The finite model property: `□p → p` is not a K-theorem, so it has a small countermodel. -/
example : ∃ (W : Type) (_ : Fintype W) (M : KripkeModel W Atom),
    Fintype.card W ≤ 2 ^ (axiomT (atom Atom.p)).sub.card ∧ ¬M.Valid (axiomT (atom .p)) := by
  refine exists_finite_countermodel fun h ↦ ?_
  have := h.valid_K (M := succModel) 1
  simp [axiomT, succModel] at this

end Cslib.Modal.FiltrationTests
