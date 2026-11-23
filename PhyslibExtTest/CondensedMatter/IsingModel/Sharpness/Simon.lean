/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Simon

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Simon`

On the triangle `Fin 3` with general couplings `J` and fields:
* `gks_second_J` (GKS II with inhomogeneous couplings) with `J = 1/2` and field `(0, 1, 2)`;
* `griffiths_mono`: adding the edges `{0, 2}` and `{1, 2}` to the single edge `{0, 1}` does not
  decrease `⟨σ_0 σ_1⟩` (all edges of the triangle are non-diagonal, checked by `decide`).
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Simon

open _root_.StatMech _root_.StatMech.Ising _root_.StatMech.Sharpness
open scoped symmDiff

/-- The three edges of the triangle on `Fin 3`. -/
def triangleEdges : Finset (Sym2 (Fin 3)) := {s(0, 1), s(0, 2), s(1, 2)}

/-- The field `h_x = x`. -/
def field : Fin 3 → ℝ := fun x => (x : ℝ)

-- GKS II with inhomogeneous couplings and fields.
example : expJ triangleEdges (fun _ => 1 / 2) field (spinProd {0}) *
      expJ triangleEdges (fun _ => 1 / 2) field (spinProd {1})
    ≤ expJ triangleEdges (fun _ => 1 / 2) field (spinProd ({0} ∆ {1})) :=
  gks_second_J triangleEdges _ field (fun _ _ => by norm_num) (fun _ => Nat.cast_nonneg _) {0} {1}

-- Griffiths monotonicity in the edge set: `⟨σ_0 σ_1⟩` on one edge is at most its value on the
-- triangle.
example : expJ ({s(0, 1)} : Finset (Sym2 (Fin 3))) (fun _ => 1) (fun _ => 0) (spinProd {0, 1})
    ≤ expJ triangleEdges (fun _ => 1) (fun _ => 0) (spinProd {0, 1}) :=
  griffiths_mono {s(0, 1)} triangleEdges (fun _ => 1) (fun _ => 0) (by decide)
    (fun _ _ => zero_le_one) (fun _ => le_rfl) (by decide) {0, 1}

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Simon
