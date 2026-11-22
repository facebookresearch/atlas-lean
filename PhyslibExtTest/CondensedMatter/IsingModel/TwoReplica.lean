/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.TwoReplica

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.TwoReplica`

On the single edge `E = {s(0, 1)}` of `Fin 2`:
* `incidentFlux` and `sources` of the current with one unit on the edge: both endpoints are
  sources; the zero current has no sources;
* `connP` through the odd edges holds between `0` and `1`, so the connectivity hypothesis of the
  switching lemma is satisfiable;
* `ising_switching_lemma_pair` applies with `n₁` one unit on the edge, `n₂ = 0`, `A = ∅`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.TwoReplica

open _root_.StatMech _root_.StatMech.Ising
open scoped symmDiff

/-- The single edge of `Fin 2`. -/
abbrev E : Finset (Sym2 (Fin 2)) := {s(0, 1)}

/-- One unit of current on every pair (only the edge `s(0, 1)` of `E` is seen by `sources E`). -/
def one : Current (Fin 2) := fun _ => 1

-- The unit current has flux one at each endpoint.
example (x : Fin 2) : incidentFlux E one x = 1 := by
  fin_cases x <;> simp [incidentFlux, one, Finset.filter_singleton]

-- Both endpoints are sources of the unit current.
example : sources E one = {0, 1} := by
  ext x; fin_cases x <;> simp [incidentFlux, one, Finset.filter_singleton]

-- The zero current has no sources.
example : sources E (0 : Current (Fin 2)) = ∅ := by
  ext x; simp [incidentFlux]

/-- The odd edges of `one + 0` connect `0` to `1`. -/
lemma connP_one : connP (oddEdges E (fun e => one e + (0 : Current (Fin 2)) e)) 0 1 := by
  refine Relation.ReflTransGen.single ⟨s(0, 1), ?_, by simp, by simp, by decide⟩
  simp [oddEdges, one]

-- The switching lemma with `n₁ = one`, `n₂ = 0`, `A = ∅`: sub-currents of `one` with sources
-- `{0, 1}` and with no sources are equinumerous.
example : Nat.card {n : Current (Fin 2) // (∀ e, n e ≤ one e + (0 : Current (Fin 2)) e) ∧
      sources E n = ∅ ∆ {0, 1}}
    = Nat.card {n : Current (Fin 2) // (∀ e, n e ≤ one e + (0 : Current (Fin 2)) e) ∧
      sources E n = ∅} :=
  ising_switching_lemma_pair E one 0 (by decide) connP_one ∅

end PhyslibExtTest.CondensedMatter.IsingModel.TwoReplica
