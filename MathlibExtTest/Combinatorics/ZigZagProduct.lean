/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.ZigZagProduct
public import MathlibExtTest.Combinatorics.RotationMap

@[expose] public section

open MathlibExt.Combinatorics MathlibExt.Combinatorics.RotationMap
open MathlibExtTest.Combinatorics.RotationMap

namespace MathlibExtTest.Combinatorics.ZigZagProduct

/-- The zig-zag theorem applied to the `5`-cycle and the perfect matching on its two labels, both
`(N, D, 1)`-graphs: the hypotheses are satisfiable on non-trivial multigraphs. -/
example : (cycle5.zigzag swap2).IsNDLambdaGraph (1 + 1 + 1 ^ 2) :=
  (isNDLambdaGraph_one cycle5).zigzag (isNDLambdaGraph_one swap2)

/-- The spectral-gap form with `λ₁ = λ₂ = 1`, where it gives the trivial bound `1`. -/
example : (cycle5.zigzag swap2).IsNDLambdaGraph (1 - (1 - 1) * (1 - 1) ^ 2) :=
  (isNDLambdaGraph_one cycle5).zigzag_gap (isNDLambdaGraph_one swap2) le_rfl

/-- Composing the operations of the expander construction: the square of a zig-zag product. -/
example : ((cycle5.zigzag swap2).square).IsNDLambdaGraph ((1 + 1 + 1 ^ 2) ^ 2) :=
  ((isNDLambdaGraph_one cycle5).zigzag (isNDLambdaGraph_one swap2)).square

end MathlibExtTest.Combinatorics.ZigZagProduct
