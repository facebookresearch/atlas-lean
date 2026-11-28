/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Calculus.NewtonMethod

/-!
# Global convergence of Newton's method for increasing convex functions

D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics,
University of Maryland, Section 2.4, Theorem 2.8 and its proof ([author copy][levy]). Levy
states the hypotheses as "monotonically increasing, convex", and his proof uses them as
`f' x > 0` and `f'' x > 0` for every `x`, the form stated here.

The local quadratic convergence near a simple root is
`MetaMathlibExt.newton_method_local_quadratic_convergence`.

[levy]: https://www.math.umd.edu/~dlevy/resources/notes.pdf
-/
