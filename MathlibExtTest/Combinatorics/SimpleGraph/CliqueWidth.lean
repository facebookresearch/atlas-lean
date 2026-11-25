/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.CliqueWidth

@[expose] public section

namespace MathlibExtTest.Combinatorics.SimpleGraph.CliqueWidth

open _root_.SimpleGraph

-- A single vertex has clique-width at most one.
example (G : SimpleGraph Unit) : G.HasCliqueWidthAtMost 1 := hasCliqueWidthAtMost_one_of_unique G

-- Non-vacuity of the joins: the 2-expression η_{0,1}(·₀ ⊕ ·₁) generates the complete graph on two
-- vertices.
example : (⊤ : SimpleGraph (Unit ⊕ Unit)).HasCliqueWidthAtMost 2 := by
  refine Or.inr ⟨Sum.elim (fun _ => 0) (fun _ => 1), ?_⟩
  have h := CWExpressible.join (0 : Fin 2) 1 (by decide)
    (CWExpressible.union (CWExpressible.vertex Unit (0 : Fin 2))
      (CWExpressible.vertex Unit (1 : Fin 2)))
  convert h using 1
  ext x y
  rcases x with ⟨⟩ | ⟨⟩ <;> rcases y with ⟨⟩ | ⟨⟩ <;> simp

-- The graph with no vertices has clique-width at most zero.
example (G : SimpleGraph Empty) : G.HasCliqueWidthAtMost 0 := Or.inl inferInstance

end MathlibExtTest.Combinatorics.SimpleGraph.CliqueWidth
