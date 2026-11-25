/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.DirectSum.Completion

/-!
# Direct sums of right C-star modules

For a family `E_i` of right pre-Hilbert modules over a nonunital C-star algebra `B`, the
algebraic direct sum consists of finitely supported vectors `(x_i)`. Its coefficient inner
product is `∑ i, ⟨x_i,y_i⟩_B` and its norm is `sqrt ‖∑ i, ⟨x_i,x_i⟩_B‖`.

Completing this space gives the Hilbert-module direct sum. Coordinate inclusions are isometries,
different coordinates are orthogonal, and their complex linear span is dense. The index type may
be arbitrary or empty, and the component modules may be incomplete.
-/
