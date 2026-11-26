/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.Bimodule.TorScalarChangeHeight

/-!
# Scalar restriction and carrier lifting in bimodule Tor comparisons

For ring maps R→R′ and S→S′, coefficient and right-module maps with
the corresponding semilinearity equations give canonical Tor
ring-change maps after lifting to a common source height.
That height contains the acting source rings and the input/coefficient
carriers, while the outer ring worlds remain independent.

The coefficient Tor height comparisons are compatible with
scalar restriction and up/down carrier lifting. Their forward and
inverse components preserve the ring-change maps, including
the canonical source-flattening and output restriction/lift comparisons.
-/
