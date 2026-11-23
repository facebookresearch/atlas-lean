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

Ported from the Chapter 22 Lean conversion in
`converted_proofs/ch22/lean/Chapter22.lean`, itself a conversion of the
Isabelle/HOL sources: the AFP entries `Skew_Heap` (`Skew_Heap.thy`) and
`Amortized_Complexity` (`Skew_Heap_Analysis.thy`,
`Amortized_Framework.thy`, `Priority_Queue_ops_merge.thy`), and
Tobias Nipkow (ed.), *Functional Data Structures and Algorithms: A Proof
Assistant Approach*, Chapter 22 (Skew Heaps, pp. 253-256) with Appendix
B.10. Isabelle-derived names are kept for traceability to those sources.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace Amortized


end Amortized

end Cslib.Algorithms.Lean
