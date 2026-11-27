/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.Amortized.Framework
public import CSLibExt.Algorithms.Lean.DataStructures.Amortized.Unary
public import CSLibExt.Algorithms.Lean.DataStructures.Amortized.LogLemmas
public import CSLibExt.Algorithms.Lean.DataStructures.Amortized.Examples
public import CSLibExt.Algorithms.Lean.DataStructures.Amortized.ExamplesTablesQueues

/-!
# Amortized analysis

The generic amortized-analysis frameworks and their examples,
ported from the AFP entry `Amortized_Complexity`: the rose-tree
framework (`Amortized.Framework`), the unary sequence framework
(`Amortized.Unary`), logarithm lemmas (`Amortized.LogLemmas`), and
the framework examples (`Amortized.Examples`,
`Amortized.ExamplesTablesQueues`). The skew-heap instantiation
lives in `SkewHeap.Amortized`.

Source: the AFP entry `Amortized Complexity`, as cited in
full in each submodule (`Amortized.Framework`,
`Amortized.Unary`, `Amortized.LogLemmas`, `Amortized.Examples`,
`Amortized.ExamplesTablesQueues`); the skew-heap instantiation
lives in `SkewHeap.Amortized`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace Amortized


end Amortized

end Cslib.Algorithms.Lean
