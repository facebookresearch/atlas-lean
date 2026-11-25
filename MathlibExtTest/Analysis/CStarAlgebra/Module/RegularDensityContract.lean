/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.CStarAlgebra.Module.Regular.PartialBridge

/-!
# Dense maximal adjoints and the full double-adjoint graph

These clients use the original partial maps and norm topologies. A named-field
reconstruction consumes the existing two density proofs; the computed adjoint
and double adjoint are then used through the public bridge API. A zero domain
cannot supply the density precondition when the space has a nonzero vector.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set

namespace RegularDensityContract

universe uB uE
variable {B : Type uB} {E : Type uE}
variable [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
variable [CStarModule Bᵐᵒᵖ E] [StarOrderedRing Bᵐᵒᵖ] [CompleteSpace E]

/-- Rebuild the canonical regular operator using named fields and its actual density proofs. -/
private def rebuilt (T : CStarModule.RegularOperator (B := B) (E := E)) :
    CStarModule.RegularOperator (B := B) (E := E) where
  toPartial := T.toPartial
  adjoint := T.adjoint
  dense_domain := T.dense_domain
  dense_adjointDomain := T.dense_adjointDomain
  adjoint_maximal := T.adjoint_maximal
  doubleAdjoint_maximal := T.doubleAdjoint_maximal
  dense_one_add_adjoint_comp_range := T.dense_one_add_adjoint_comp_range

/-- The reconstructed dense operator gives the original full computed adjoint. -/
example (T : CStarModule.RegularOperator (B := B) (E := E)) :
    CStarModule.DenselyDefinedRightPartialOperator.adjoint (rebuilt T).toDenselyDefined =
      T.adjoint :=
  (rebuilt T).computedAdjoint_eq

/-- The full computed double-adjoint graph has the original domain/action membership criterion. -/
example (T : CStarModule.RegularOperator (B := B) (E := E)) (x y : E) :
    (x, y) ∈
      (CStarModule.DenselyDefinedRightPartialOperator.adjoint
        (rebuilt T).toDenselyDefinedAdjoint).graph ↔
      ∃ z : T.toPartial.domain, (z : E) = x ∧ T.toPartial z = y := by
  rw [(rebuilt T).computedDoubleAdjoint_eq]
  exact LinearPMap.mem_graph_iff T.toPartial

/-- A supplied dense-domain proof is required when consuming maximality of a computed adjoint. -/
example (t : CStarModule.DenselyDefinedRightPartialOperator B E E) :
    CStarModule.IsMaximalAdjoint (B := B) t.toPartial
      (CStarModule.DenselyDefinedRightPartialOperator.adjoint t) t.dense_domain :=
  CStarModule.DenselyDefinedRightPartialOperator.adjoint_isMaximal t

/-- A zero-domain partial map fails the required density premise on any genuine nonzero space. -/
example (T : E →ₗ.[ℂ] E) (hzero : T.domain = ⊥) (v : E) (hv : v ≠ 0) :
    ¬ Dense (T.domain : Set E) := by
  intro hdense
  have hsingleton : (T.domain : Set E) = {0} := by
    rw [hzero]
    ext x
    simp
  have hclosure := congrArg (fun s : Set E => v ∈ s) hdense.closure_eq
  rw [hsingleton, closure_singleton] at hclosure
  have hvzero : v = 0 := Set.mem_singleton_iff.mp (hclosure.mpr (Set.mem_univ v))
  exact hv hvzero

end RegularDensityContract
