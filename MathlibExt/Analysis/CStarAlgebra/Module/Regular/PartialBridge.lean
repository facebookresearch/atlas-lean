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
# Partial adjoints and regular-operator graphs

For a densely defined right-linear partial operator `t` on a right C-star module, the adjoint
constructed from pairing witnesses is maximal, and any maximal adjoint equals it as a partial
map.

For a regular operator `T` on a complete module, the associated densely defined right-linear map
has partial map `T.toPartial`. Its adjoint is `T.adjoint` and its double adjoint is
`T.toPartial`. Consequently the graph of `T.toPartial` is closed in `E × E`. The conversion to a
densely defined right-linear operator is injective.
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

/-- **Maximality of the witness adjoint.** For a densely defined right-linear partial operator
`t`, `adjoint t` is maximal for the pairing `⟨t x, y⟩_B = ⟨x, t* y⟩_B`, using the density of
`dom t`. -/
theorem adjoint_isMaximal (t : DenselyDefinedRightPartialOperator B E E) :
    IsMaximalAdjoint (B := B) t.toPartial (adjoint t) t.dense_domain := by
  constructor
  · intro y
    constructor
    · intro hy
      exact existsUnique_adjointWitness t ⟨y, hy⟩
    · rintro ⟨z, hz, _⟩
      exact ⟨z, hz⟩
  · intro y x
    exact adjoint_pairing t x y

/-- **Uniqueness of a maximal partial adjoint.** If `t` is densely defined and `S` is a maximal
adjoint of its complex-linear partial map, then `S = adjoint t`, including equality of domains
and actions. -/
theorem maximalAdjoint_eq_adjoint (t : DenselyDefinedRightPartialOperator B E E)
    (S : E →ₗ.[ℂ] E) (hS : IsMaximalAdjoint (B := B) t.toPartial S t.dense_domain) :
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

/-- **Dense right-linear map of a regular operator.** A regular operator on a complete right
C-star module determines a densely defined right-linear operator with partial map
`T.toPartial` and its same norm-domain. -/
def toDenselyDefined (T : RegularOperator (B := B) (E := E)) :
    DenselyDefinedRightPartialOperator B E E where
  toPartial := T.toPartial
  dense_domain := T.dense_domain
  domain_right_smul _x hx b := T.mem_domain_right_smul hx b
  map_right_smul x b := T.map_right_smul x b

/-- **Underlying partial map of the regular realization.** `T.toDenselyDefined.toPartial =
T.toPartial` for a regular operator `T`. -/
theorem toDenselyDefined_toPartial (T : RegularOperator (B := B) (E := E)) :
    T.toDenselyDefined.toPartial = T.toPartial := rfl

/-- **Adjoint of the regular realization.** For a regular operator,
`DenselyDefinedRightPartialOperator.adjoint T.toDenselyDefined = T.adjoint` as partial maps. -/
theorem computedAdjoint_eq (T : RegularOperator (B := B) (E := E)) :
    DenselyDefinedRightPartialOperator.adjoint T.toDenselyDefined = T.adjoint :=
  (DenselyDefinedRightPartialOperator.maximalAdjoint_eq_adjoint
    T.toDenselyDefined T.adjoint T.adjoint_maximal).symm

/-- **Dense realization of the regular adjoint.** The maximal adjoint of a regular operator is
bundled with its dense domain and right-linearity, giving a densely defined right-linear
partial operator on `E`. -/
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

/-- **Underlying partial map of the adjoint realization.** `T.toDenselyDefinedAdjoint.toPartial =
T.adjoint` for a regular operator `T`. -/
theorem toDenselyDefinedAdjoint_toPartial (T : RegularOperator (B := B) (E := E)) :
    T.toDenselyDefinedAdjoint.toPartial = T.adjoint := T.computedAdjoint_eq

/-- **Double adjoint of a regular operator.** The adjoint of `T.toDenselyDefinedAdjoint` equals
the full partial map `T.toPartial`, by mutual maximality. -/
theorem computedDoubleAdjoint_eq (T : RegularOperator (B := B) (E := E)) :
    DenselyDefinedRightPartialOperator.adjoint T.toDenselyDefinedAdjoint = T.toPartial := by
  have hmax : IsMaximalAdjoint (B := B) T.toDenselyDefinedAdjoint.toPartial T.toPartial
      T.toDenselyDefinedAdjoint.dense_domain := by
    unfold IsMaximalAdjoint
    rw [T.toDenselyDefinedAdjoint_toPartial]
    exact T.doubleAdjoint_maximal
  exact (DenselyDefinedRightPartialOperator.maximalAdjoint_eq_adjoint
    T.toDenselyDefinedAdjoint T.toPartial hmax).symm

/-- **Closed graph of a regular operator.** For a regular operator on a complete right C-star
module, `(T.toPartial.graph : Set (E × E))` is closed in the product norm topology. -/
theorem isClosed_graph (T : RegularOperator (B := B) (E := E)) :
    IsClosed (T.toPartial.graph : Set (E × E)) := by
  have h := DenselyDefinedRightPartialOperator.isClosed_adjoint_graph T.toDenselyDefinedAdjoint
  rwa [T.computedDoubleAdjoint_eq] at h

/-- **Faithfulness of the dense realization.** Two regular operators with the same densely defined
right-linear realization are equal, since their partial maps and maximal adjoints are equal. -/
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
