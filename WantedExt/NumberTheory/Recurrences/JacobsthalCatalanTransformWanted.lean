/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Catalan transforms of Jacobsthal-type sequences

Source: B. Sivakumar and S. Vasanthi, "Complex-type
Catalan Transform of k-Jacobsthal and Fourth-Order Jacobsthal
Recurrences", *INTEGERS* 25 (2025), Article A22
(<https://math.colgate.edu/~integers/vol25.html>).

The paper's Theorem 2 is the Cassini identity
`J_{k, n+1}^2 - J_{k, n} J_{k, n+2} = (-2)^n`, stated
there for `n ≥ 1` and `k ≥ 2`, for the `k`-Jacobsthal
numbers (`J_{k, 0} = 0`, `J_{k, 1} = 1`,
`J_{k, n+1} = k J_{k, n} + 2 J_{k, n-1}`). These are the
Lucas sequence `U(k, -2)`. The proved generalization
`MetaMathlibExt.lucasU_cassini`
(`MathlibExt/NumberTheory/LucasSequence.lean`) drops
both restrictions: it covers all Lucas parameters and
all `n`, including `n = 0`. Theorem 2 is its case
`P = k`, `Q = -2`, so it is not re-requested here.

The remaining records of the paper are not formalized
(see the source audit table): Theorem 1 (the generating
function of the complex-type Catalan transform, whose
closed form is garbled in the extraction) and Theorems 3,
4 and Corollaries 1, 2 (spectral-norm bounds for circulant
Jacobsthal matrices, whose bounding fractions are garbled
in the extraction).
-/
module

public import MathlibExt.NumberTheory.LucasSequence

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.JacobsthalCatalanTransformWanted

end MathlibExt.NumberTheory.Recurrences.JacobsthalCatalanTransformWanted
