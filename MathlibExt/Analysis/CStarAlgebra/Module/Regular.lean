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

public import MathlibExt.Analysis.CStarAlgebra.Module.Adjointable
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.LinearAlgebra.LinearPMap

/-!
# Regular operators on right C-star modules

This file defines a domain-aware carrier for regular operators.  A partial
operator and its adjoint are mutually maximal adjoints, both domains are
dense, and the literal partial range of `1 + T* T` is dense.  Mutual
maximality records `T = T**` and therefore closedness; right-module linearity
is deliberately not stored as a field.
-/

@[expose] public section

open Set
open scoped RightActions

namespace CStarModule

universe uB uE

variable {B : Type uB} {E : Type uE}
variable [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E]

/-- A densely-defined complex-linear operator before regularity hypotheses
are imposed. -/
abbrev PartialOperator := E →ₗ.[ℂ] E

/-- `S` is the maximal adjoint of `T`: its domain is exactly the vectors
admitting an adjoint witness, and its action is that unique witness. -/
def IsMaximalAdjoint (T S : PartialOperator (E := E)) : Prop :=
  (∀ y : E, y ∈ S.domain ↔
    ∃! z : E, ∀ x : T.domain,
      rightInner (B := B) (T x) y = rightInner (B := B) (x : E) z) ∧
  ∀ (y : S.domain) (x : T.domain),
    rightInner (B := B) (T x) (y : E) =
      rightInner (B := B) (x : E) (S y)

/-- A closed regular operator with its maximal adjoint.  Mutual maximality is
the domain-aware equality `T = T**`. -/
structure RegularOperator [CompleteSpace E] where
  /-- The original partial operator. -/
  toPartial : PartialOperator (E := E)
  /-- Its maximal adjoint. -/
  adjoint : PartialOperator (E := E)
  /-- The selected partial map is maximal as the adjoint of `toPartial`. -/
  adjoint_maximal : IsMaximalAdjoint (B := B) toPartial adjoint
  /-- The original map is the maximal adjoint of `adjoint`. -/
  doubleAdjoint_maximal : IsMaximalAdjoint (B := B) adjoint toPartial
  /-- The domain of `T` is dense. -/
  dense_domain : Dense (toPartial.domain : Set E)
  /-- The domain of `T*` is dense. -/
  dense_adjointDomain : Dense (adjoint.domain : Set E)
  /-- The partial range of `1 + T* T` is dense. -/
  dense_one_add_adjoint_comp_range : Dense
    {z : E | ∃ (x : E) (hx : x ∈ toPartial.domain)
      (hTx : toPartial ⟨x, hx⟩ ∈ adjoint.domain),
      z = x + adjoint ⟨toPartial ⟨x, hx⟩, hTx⟩}

namespace RegularOperator

variable [CompleteSpace E] [StarOrderedRing Bᵐᵒᵖ]

/-- The domain of a regular operator is stable under the source-order right
coefficient action. -/
theorem mem_domain_right_smul (T : RegularOperator (B := B) (E := E))
    {x : E} (hx : x ∈ T.toPartial.domain) (b : B) :
    x <• b ∈ T.toPartial.domain := by
  apply (T.doubleAdjoint_maximal.1 (x <• b)).2
  have hWitness : ∀ u : T.adjoint.domain,
      rightInner (B := B) (T.adjoint u) (x <• b) =
        rightInner (B := B) (u : E)
          (T.toPartial ⟨x, hx⟩ <• b) := by
    intro u
    have hAdj :
        rightInner (B := B) (T.adjoint u) x =
          rightInner (B := B) (u : E) (T.toPartial ⟨x, hx⟩) := by
      have h := congrArg star (T.adjoint_maximal.2 u ⟨x, hx⟩)
      simpa only [star_rightInner] using h.symm
    calc
      rightInner (B := B) (T.adjoint u) (x <• b) =
          rightInner (B := B) (T.adjoint u) x * b := by simp
      _ = rightInner (B := B) (u : E) (T.toPartial ⟨x, hx⟩) * b :=
        congrArg (· * b) hAdj
      _ = rightInner (B := B) (u : E)
          (T.toPartial ⟨x, hx⟩ <• b) := by simp
  refine ⟨T.toPartial ⟨x, hx⟩ <• b, hWitness, ?_⟩
  intro z hz
  apply CStarModule.ext_rightInner (B := B)
  intro v
  have hContinuous := Continuous.ext_on T.dense_adjointDomain
    (continuous_rightInner_left (B := B) z)
    (continuous_rightInner_left (B := B)
      (T.toPartial ⟨x, hx⟩ <• b))
    (by
      intro u hu
      exact (hz ⟨u, hu⟩).symm.trans (hWitness ⟨u, hu⟩))
  exact congrFun hContinuous v

/-- A regular operator intertwines the source-order right coefficient
action on its domain. -/
theorem map_right_smul (T : RegularOperator (B := B) (E := E))
    (x : T.toPartial.domain) (b : B) :
    T.toPartial
        ⟨(x : E) <• b, T.mem_domain_right_smul x.2 b⟩ =
      T.toPartial x <• b := by
  apply CStarModule.ext_rightInner (B := B)
  intro v
  have hContinuous := Continuous.ext_on T.dense_adjointDomain
    (continuous_rightInner_left (B := B)
      (T.toPartial
        ⟨(x : E) <• b, T.mem_domain_right_smul x.2 b⟩))
    (continuous_rightInner_left (B := B) (T.toPartial x <• b))
    (by
      intro u hu
      let u' : T.adjoint.domain := ⟨u, hu⟩
      have hAdj :
          rightInner (B := B) (T.adjoint u') (x : E) =
            rightInner (B := B) (u' : E) (T.toPartial x) := by
        have h := congrArg star (T.adjoint_maximal.2 u' x)
        simpa only [star_rightInner] using h.symm
      calc
        rightInner (B := B) u
            (T.toPartial
              ⟨(x : E) <• b, T.mem_domain_right_smul x.2 b⟩) =
            rightInner (B := B) (T.adjoint u') ((x : E) <• b) :=
          (T.doubleAdjoint_maximal.2
            ⟨(x : E) <• b, T.mem_domain_right_smul x.2 b⟩ u').symm
        _ = rightInner (B := B) (T.adjoint u') (x : E) * b := by
          simp
        _ = rightInner (B := B) (u' : E) (T.toPartial x) * b :=
          congrArg (· * b) hAdj
        _ = rightInner (B := B) u (T.toPartial x <• b) := by
          simp [u'])
  exact congrFun hContinuous v

/-- Positivity in the canonical spectral order on the adjointable
endomorphism C-star algebra. -/
def IsSpectrallyNonnegative
    (T : AdjointableOperator.End B E) : Prop :=
  @LE.le (AdjointableOperator.End B E)
    (CStarAlgebra.spectralOrder (AdjointableOperator.End B E)).toLE 0 T

/-- Domain-aware bounded-transform data for a regular operator.  The range
clauses make `h⁻¹` and `l⁻¹` partial inverses on their natural domains. -/
structure BoundedTransformData (T : RegularOperator (B := B) (E := E)) where
  /-- The bounded extension of `(1 + T* T)⁻¹/²`. -/
  h : AdjointableOperator.End B E
  /-- The bounded extension of `(1 + T T*)⁻¹/²`. -/
  l : AdjointableOperator.End B E
  /-- The bounded transform extending `T h`. -/
  F : AdjointableOperator.End B E
  h_nonnegative : IsSpectrallyNonnegative h
  l_nonnegative : IsSpectrallyNonnegative l
  h_mem_domain : ∀ x, h x ∈ T.toPartial.domain
  l_mem_adjointDomain : ∀ x, l x ∈ T.adjoint.domain
  h_parametrizes_domain : ∀ (y : E), y ∈ T.toPartial.domain →
    ∃! x : E, h x = y
  l_parametrizes_adjointDomain : ∀ (y : E), y ∈ T.adjoint.domain →
    ∃! x : E, l x = y
  F_extends_Th : ∀ x, T.toPartial ⟨h x, h_mem_domain x⟩ = F x
  Fstar_extends_Tstar_l : ∀ x,
    T.adjoint ⟨l x, l_mem_adjointDomain x⟩ = F.adjointOperator x
  h_squared_inverse : ∀ x,
    ∃ hy : h (h x) ∈ T.toPartial.domain,
      ∃ hTy : T.toPartial ⟨h (h x), hy⟩ ∈ T.adjoint.domain,
        h (h x) + T.adjoint ⟨T.toPartial ⟨h (h x), hy⟩, hTy⟩ = x
  l_squared_inverse : ∀ x,
    ∃ hy : l (l x) ∈ T.adjoint.domain,
      ∃ hTy : T.adjoint ⟨l (l x), hy⟩ ∈ T.toPartial.domain,
        l (l x) + T.toPartial ⟨T.adjoint ⟨l (l x), hy⟩, hTy⟩ = x

end RegularOperator

end CStarModule
