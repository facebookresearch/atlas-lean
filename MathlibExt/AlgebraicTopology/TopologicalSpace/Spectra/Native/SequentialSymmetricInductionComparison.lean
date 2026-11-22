/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.Adjunction
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.SymmetricAlgebra
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.FreeAlgebraCoherence
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.CanonicalPair
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.FreeComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.FreeUnitComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.BalancedCarrier

/-!
# The complete original sequential/symmetric induction presentation

The original full tensor algebra, symmetric circle algebra, sphere bimodule,
balancing quotient and relative tensor carrier are compared with the original
weighted-coend Kan adjunction. Both Hom functions, both inverse comparisons,
every source/coefficient map and every actual free-unit generator are retained.

## Source and scope

The algebraic recipe is Hovey–Shipley–Smith, *Symmetric spectra*, §4.4,
“Description of V” ([arXiv:math/9801077v2](https://arxiv.org/abs/math/9801077v2)).
That section constructs `G(X)_n = (Sigma_n)_+ smash X_n` and
`V(X) = S tensor_(T(G_1 S^1)) G(X)` in pointed simplicial sets, using the
monoidal associativity/unit coherence of `G` and the right action on `S`
determined by the original tensor-algebra map. This module proves the
corresponding presentation for the project's actual pointed CGWH
sequential/symmetric enriched operator-index Kan adjunction.
-/
