/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.FiniteCompact
import MathlibExt.AlgebraicTopology.TopologicalSpace.CGWH.FiniteRealization
import Mathlib.Topology.Bases

/-!
# Compact separable finite simplicial realizations

The quotient of the finite family of standard simplices supplies separability.
The CGWH realization has the same finite realization carrier and topology.
-/

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory Limits Topology TopologicalSpace
open scoped Simplicial

namespace SSet

/-- The finite nondegenerate-simplex presentation gives a separable source
for the literal finite simplicial realization. -/
theorem finiteRealization_separable (T : SSet.{v}) [T.Finite] :
    SeparableSpace (SSet.toTop.obj T) := by
  let _ (s : T.N) : SecondCountableTopology
      (Convexity.StdSimplex ℝ (Fin (s.dim + 1))) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).secondCountableTopology
  let _ : SeparableSpace (Σ s : T.N, Convexity.StdSimplex ℝ (Fin (s.dim + 1))) :=
    inferInstance
  exact (SSet.isQuotientMap_sigmaToTop T).separableSpace

/-- Both compactness and separability belong to the actual finite CGWH
realization carrier and topology. -/
theorem finiteCGWHRealization_compactSeparable (T : SSet.{v}) [T.Finite] :
    CompactSpace (SSet.toCGWHOfFinite.{u, v} T) ∧
      SeparableSpace (SSet.toCGWHOfFinite.{u, v} T) := by
  constructor
  · change CompactSpace (SSet.toTop.obj T)
    infer_instance
  · change SeparableSpace (SSet.toTop.obj T)
    exact finiteRealization_separable T


end SSet
