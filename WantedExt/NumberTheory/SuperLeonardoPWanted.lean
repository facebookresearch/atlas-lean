/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Supergeneralized Leonardo `p`-numbers

Statements from Clemens Schütz and Kristian Kelly, *An Explicit Formula for
Supergeneralized Leonardo `p`-numbers*, Journal of Integer Sequences 28 (2025),
Article 25.8.2 (<https://cs.uwaterloo.ca/journals/JIS/VOL28/Schutz/schutz3.tex>).

The supergeneralized Leonardo `p`-numbers `𝓛_{p,k,x}` take the `p + 1` initial values
`x_0, …, x_p` freely and satisfy `𝓛(n) = 𝓛(n-1) + 𝓛(n-p-1) + k` for `n > p`; they are
`superLeonardoP`. With `x` constantly `1` they are the generalized Leonardo `p`-numbers
`MathlibExt.NumberTheory.LeonardoPWanted.leonardoPK`. The Fibonacci `p`-numbers are the
existing `MetaMathlibExt.fibonacciP`.

The paper's auxiliary vector `y` is printed as `(1, …, p)`, which has only `p` of the
`p + 1` entries a supergeneralized Leonardo `p`-sequence needs; the paper's table of
`q_{p+j}` (`q_{2p+1} = p + 1`) and Theorem 5 at `n = p` both force `y_p = p + 1`, so `y`
is read here as `(1, …, p + 1)`, i.e. `y_i = i + 1`.
-/
module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.Recurrences.SchutzKellyBinomialSum
public import MathlibExt.NumberTheory.Recurrences.SuperLeonardoPBinomial
public import MathlibExt.NumberTheory.Recurrences.SuperLeonardoPFibonacciSum
public import MathlibExt.NumberTheory.SuperLeonardoPSuperLeonardoPEqAddMul

namespace MetaMathlibExt

@[expose] public section

end

end MetaMathlibExt
