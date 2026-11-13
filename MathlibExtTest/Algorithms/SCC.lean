/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.SCC

@[expose] public section

/-- Boundary check: reachability in the reversed graph is
reversed reachability, instantiated on one edge. -/
example (E : Fin 2 → Fin 2 → Prop) (h : E 0 1) :
    Reach (RevE E) 1 0 :=
  (reach_rev (E := E) 1 0).mpr (Relation.ReflTransGen.single h)
