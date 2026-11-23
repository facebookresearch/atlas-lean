/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Archive.Kuratowski

open Set

namespace MathlibExt.Topology.KuratowskiClosureComplement

variable {X : Type*} [TopologicalSpace X]

/--
**Kuratowski's closure-complement theorem.** Let $X$ be a topological space and $s \subseteq X$.
The sets that can be obtained from $s$ by applying closure and complement finitely many times
(including $s$ itself) form a finite family of at most $14$ distinct sets.

Source: Casimir Kuratowski, "Sur l'opération Ā de l'Analysis Situs,"
*Fundamenta Mathematicae* 3 (1922), 182–199, DOI 10.4064/FM-3-1-182-199.
-/
theorem kuratowski_closure_complement (s : Set X) :
    {t : Set X | Topology.ClosureCompl.IsObtainable s t}.Finite ∧
      {t : Set X | Topology.ClosureCompl.IsObtainable s t}.ncard ≤ 14 := by
  have hset : {t : Set X | Topology.ClosureCompl.IsObtainable s t} =
      ↑(Topology.ClosureCompl.theFourteen s).toFinset := by
    ext t
    change Topology.ClosureCompl.IsObtainable s t ↔
      t ∈ (Topology.ClosureCompl.theFourteen s).toFinset
    rw [Multiset.mem_toFinset,
      Topology.ClosureCompl.mem_theFourteen_iff_isObtainable]
  constructor
  · rw [hset]
    exact Finset.finite_toSet _
  · exact Topology.ClosureCompl.ncard_isObtainable_le_fourteen s

end MathlibExt.Topology.KuratowskiClosureComplement
