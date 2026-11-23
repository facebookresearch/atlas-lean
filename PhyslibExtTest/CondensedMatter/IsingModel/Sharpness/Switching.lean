/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Switching

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Switching`

On the doubled edge (two parallel edges `0 — 1`, indexed by `Fin 2`):
* `sources`: the full current has no sources (both endpoints have degree `2`), a single edge has
  sources `{0, 1}`;
* `connK`: the endpoints are connected through the current;
* `switching_lemma` applies with `m` the full current, `A = ∅`, `u = 0`, `v = 1`, and every
  hypothesis checked by `decide`; both sides have two terms.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Switching

open _root_.StatMech.Sharpness.RandomCurrent
open scoped symmDiff

/-- Two parallel edges between `0` and `1`. -/
def ends : Fin 2 → Sym2 (Fin 2) := fun _ => s(0, 1)

-- The full current has no sources; a single edge has both endpoints as sources.
example : sources ends Finset.univ = ∅ ∧ sources ends {0} = {0, 1} := by decide

-- The endpoints are connected through the current.
example : connK ends Finset.univ 0 1 :=
  Relation.ReflTransGen.single ⟨0, Finset.mem_univ _, by simp [ends], by simp [ends], by decide⟩

open Classical in
-- The switching lemma on the doubled edge.
example (F : Finset (Fin 2) → ℝ) :
    ∑ _K ∈ (Finset.univ : Finset (Fin 2)).powerset.filter
        (fun K => sources ends K = ∅ ∆ {0, 1}), F Finset.univ
      = ∑ _K ∈ (Finset.univ : Finset (Fin 2)).powerset.filter (fun K => sources ends K = ∅),
          F Finset.univ * (if connK ends Finset.univ 0 1 then 1 else 0) :=
  switching_lemma ends Finset.univ (fun _ _ => by simp [ends]) ∅ (by decide)
    (show (0 : Fin 2) ≠ 1 by decide) F

-- Both filters have two elements: the single edges on the left, `∅` and the full current on the
-- right.
example : ((Finset.univ : Finset (Fin 2)).powerset.filter
      (fun K => sources ends K = ∅ ∆ {0, 1})).card = 2 ∧
    ((Finset.univ : Finset (Fin 2)).powerset.filter (fun K => sources ends K = ∅)).card = 2 := by
  decide

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Switching
