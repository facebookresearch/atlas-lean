/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.Regular
public import MathlibExt.Analysis.CStarAlgebra.Module.RectangularAdjoint

/-!
# Canonical regular operators and their actual dense partial maps

The canonical maximality fields identify the full computed adjoint and
computed double adjoint. The existing closed-adjoint graph theorem then
proves original closedness. These adapters are prerequisites for preserving
canonical regular operators in the source unbounded-multiplier API.
No converse from a weaker regularity predicate or output certificate is used.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped RightActions

namespace CStarModule
universe uB uE
variable {B : Type uB} [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [StarOrderedRing Bᵐᵒᵖ]

namespace DenselyDefinedRightPartialOperator

/-- The actual full computed adjoint satisfies literal canonical maximality. -/
theorem adjoint_isMaximal (t : DenselyDefinedRightPartialOperator B E E) :
    IsMaximalAdjoint (B := B) t.toPartial (adjoint t) := by
  constructor
  · intro y
    constructor
    · intro hy
      exact existsUnique_adjointWitness t ⟨y, hy⟩
    · rintro ⟨z, hz, _⟩
      exact ⟨z, hz⟩
  · intro y x
    exact adjoint_pairing t x y

/-- A maximal adjoint is the actual unique full witness construction. -/
theorem maximalAdjoint_eq_adjoint (t : DenselyDefinedRightPartialOperator B E E)
    (S : E →ₗ.[ℂ] E) (hS : IsMaximalAdjoint (B := B) t.toPartial S) :
    S = adjoint t := by
  apply LinearPMap.dExt
  · apply Submodule.ext
    intro y
    constructor
    · intro hy
      obtain ⟨z, hz, _⟩ := (hS.1 y).1 hy
      exact ⟨z, hz⟩
    · intro hy
      exact (hS.1 y).2 (existsUnique_adjointWitness t ⟨y, hy⟩)
  · intro y z hyz
    change S y = adjointValue t z
    have hleft : IsAdjointWitness t (y : E) (S y) := hS.2 y
    have hright : IsAdjointWitness t (y : E) (adjointValue t z) := by
      intro x
      calc
        rightInner (B := B) (t.toPartial x) (y : E) =
            rightInner (B := B) (t.toPartial x) (z : E) :=
          congrArg (rightInner (B := B) (t.toPartial x)) hyz
        _ = rightInner (B := B) (x : E) (adjointValue t z) := adjointValue_spec t z x
    exact adjointWitness_unique t hleft hright

end DenselyDefinedRightPartialOperator

namespace RegularOperator
variable [CompleteSpace E]

/-- The canonical carrier supplies its actual dense right-linear partial map. -/
def toDenselyDefined (T : RegularOperator (B := B) (E := E)) :
    DenselyDefinedRightPartialOperator B E E where
  toPartial := T.toPartial
  dense_domain := T.dense_domain
  domain_right_smul _x hx b := T.mem_domain_right_smul hx b
  map_right_smul x b := T.map_right_smul x b

/-- This adapter retains the original partial map and its exact domain. -/
theorem toDenselyDefined_toPartial (T : RegularOperator (B := B) (E := E)) :
    T.toDenselyDefined.toPartial = T.toPartial := rfl

/-- Canonical maximality identifies the entire computed adjoint partial map. -/
theorem computedAdjoint_eq (T : RegularOperator (B := B) (E := E)) :
    DenselyDefinedRightPartialOperator.adjoint T.toDenselyDefined = T.adjoint :=
  (DenselyDefinedRightPartialOperator.maximalAdjoint_eq_adjoint
    T.toDenselyDefined T.adjoint T.adjoint_maximal).symm

/-- The same actual computed adjoint, bundled only with its existing density. -/
def toDenselyDefinedAdjoint (T : RegularOperator (B := B) (E := E)) :
    DenselyDefinedRightPartialOperator B E E where
  toPartial := DenselyDefinedRightPartialOperator.adjoint T.toDenselyDefined
  dense_domain := by
    have hd := congrArg (fun p : E →ₗ.[ℂ] E => p.domain) T.computedAdjoint_eq
    rw [hd]
    exact T.dense_adjointDomain
  domain_right_smul y hy b :=
    DenselyDefinedRightPartialOperator.adjointDomain_right_smul T.toDenselyDefined hy b
  map_right_smul y b :=
    DenselyDefinedRightPartialOperator.adjoint_right_smul T.toDenselyDefined y b

/-- The dense adjoint adapter retains the canonical full adjoint. -/
theorem toDenselyDefinedAdjoint_toPartial (T : RegularOperator (B := B) (E := E)) :
    T.toDenselyDefinedAdjoint.toPartial = T.adjoint := T.computedAdjoint_eq

/-- Canonical mutual maximality identifies the actual computed double adjoint. -/
theorem computedDoubleAdjoint_eq (T : RegularOperator (B := B) (E := E)) :
    DenselyDefinedRightPartialOperator.adjoint T.toDenselyDefinedAdjoint = T.toPartial := by
  have hmax : IsMaximalAdjoint (B := B) T.toDenselyDefinedAdjoint.toPartial T.toPartial :=
    T.toDenselyDefinedAdjoint_toPartial.symm ▸ T.doubleAdjoint_maximal
  exact (DenselyDefinedRightPartialOperator.maximalAdjoint_eq_adjoint
    T.toDenselyDefinedAdjoint T.toPartial hmax).symm

/-- The original canonical graph is closed because it is the full double-adjoint graph. -/
theorem isClosed_graph (T : RegularOperator (B := B) (E := E)) :
    IsClosed (T.toPartial.graph : Set (E × E)) := by
  have h := DenselyDefinedRightPartialOperator.isClosed_adjoint_graph T.toDenselyDefinedAdjoint
  rwa [T.computedDoubleAdjoint_eq] at h

/-- Keeping the original partial map loses no canonical regular-operator DATA. -/
theorem toDenselyDefined_injective :
    Function.Injective (toDenselyDefined (B := B) (E := E)) := by
  intro T U h
  have hp : T.toPartial = U.toPartial :=
    congrArg DenselyDefinedRightPartialOperator.toPartial h
  have ha : T.adjoint = U.adjoint :=
    T.computedAdjoint_eq.symm.trans
      ((congrArg DenselyDefinedRightPartialOperator.adjoint h).trans U.computedAdjoint_eq)
  cases T
  cases U
  cases hp
  cases ha
  rfl

end RegularOperator
end CStarModule
