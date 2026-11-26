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

Let `E` be a complete right module over a nonunital C-star algebra `B`. A regular operator
consists of complex-linear partial maps `T,S : E →ₗ.[ℂ] E` with dense domains. They are mutually
maximal adjoints for the pairing `⟨T x, y⟩_B = ⟨x, S y⟩_B`, and the set `{x + S (T x) | x ∈ dom
T, T x ∈ dom S}` is dense in `E`.

For a star-compatible coefficient order, maximality implies stability of `dom T` under right
coefficients and `T (x <• b) = T x <• b`. The bounded-transform record describes positive
adjointable maps `h,l` parametrizing the two domains and a bounded map `F` satisfying `F x = T
(h x)`. Its inverse identities are `(1 + S T) h² = 1` and `(1 + T S) l² = 1`, with all
partial-domain conditions included.
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

/-- **Complex-linear partial operator.** A map `E →ₗ.[ℂ] E` is complex-linear on a complex
submodule of `E`; this carrier imposes no density or regularity condition on that domain. -/
abbrev PartialOperator := E →ₗ.[ℂ] E

/-- **Maximal adjoint of a dense partial operator.** For a complex-linear partial map `T` with
dense norm-domain, `S` is its maximal adjoint when `y ∈ dom S` is equivalent to existence of a
unique `z : E` with `⟨T x, y⟩_B = ⟨x, z⟩_B` for every `x ∈ dom T`, and `S y` is that witness. -/
def IsMaximalAdjoint (T S : PartialOperator (E := E))
    (_hT : Dense (T.domain : Set E)) : Prop :=
  (∀ y : E, y ∈ S.domain ↔
    ∃! z : E, ∀ x : T.domain,
      rightInner (B := B) (T x) y = rightInner (B := B) (x : E) z) ∧
  ∀ (y : S.domain) (x : T.domain),
    rightInner (B := B) (T x) (y : E) =
      rightInner (B := B) (x : E) (S y)

/-- **Regular operator on a right module.** On a complete right C-star module, this record
contains mutually maximal partial adjoints `T,S` with dense domains and dense range of `x ↦ x
+ S (T x)` on `{x ∈ dom T | T x ∈ dom S}`. -/
structure RegularOperator [CompleteSpace E] where
  /-- **Underlying regular partial map.** The complex-linear partial operator `T : dom T → E` of
  the regular-operator record. -/
  toPartial : PartialOperator (E := E)
  /-- **Maximal partial adjoint.** The partial operator `S` characterized by `⟨T x, y⟩_B = ⟨x, S
  y⟩_B` on the two domains. -/
  adjoint : PartialOperator (E := E)
  /-- **Density of the operator domain.** `dom T` is dense in the norm topology of `E`. -/
  dense_domain : Dense (toPartial.domain : Set E)
  /-- **Density of the adjoint domain.** `dom S` is dense in the norm topology of `E`. -/
  dense_adjointDomain : Dense (adjoint.domain : Set E)
  /-- **Maximality of the adjoint.** The domain of `S` consists of all adjoint witnesses for `T`,
  and `S` evaluates those witnesses. -/
  adjoint_maximal : IsMaximalAdjoint (B := B) toPartial adjoint dense_domain
  /-- **Double-adjoint maximality.** The partial map `T` is the maximal adjoint of `S`, including
  equality of their full witness domains. -/
  doubleAdjoint_maximal : IsMaximalAdjoint (B := B) adjoint toPartial dense_adjointDomain
  /-- **Dense range of one plus the adjoint square.** The vectors `x + S (T x)`, for `x ∈ dom T`
  with `T x ∈ dom S`, form a dense subset of `E`. -/
  dense_one_add_adjoint_comp_range : Dense
    {z : E | ∃ (x : E) (hx : x ∈ toPartial.domain)
      (hTx : toPartial ⟨x, hx⟩ ∈ adjoint.domain),
      z = x + adjoint ⟨toPartial ⟨x, hx⟩, hTx⟩}

namespace RegularOperator

variable [CompleteSpace E] [StarOrderedRing Bᵐᵒᵖ]

/-- **Right invariance of a regular domain.** For a regular operator on a complete right C-star
module with star-compatible coefficient order, `x ∈ dom T` implies `x <• b ∈ dom T` for every
`b : B`. -/
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

/-- **Right linearity of a regular operator.** Under the regular-operator and coefficient-order
hypotheses, `T (x <• b) = T x <• b` for every `x ∈ dom T` and `b : B`. -/
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

/-- **Spectral positivity of an adjointable endomorphism.** For `A ∈ End_B(E)`, this predicate is
`0 ≤ A` in the canonical C-star spectral order on the adjointable endomorphism algebra. -/
def IsSpectrallyNonnegative
    (T : AdjointableOperator.End B E) : Prop :=
  @LE.le (AdjointableOperator.End B E)
    (CStarAlgebra.spectralOrder (AdjointableOperator.End B E)).toLE 0 T

/-- **Bounded-transform data for a regular operator.** This record supplies positive adjointable
`h,l`, bijective parametrizations of `dom T` and `dom T*`, and an adjointable `F` with `F x =
T (h x)` and `F* x = T* (l x)`. It includes the domain conditions and identities `(1 + T* T)
h² x = x` and `(1 + T T*) l² x = x`. -/
structure BoundedTransformData (T : RegularOperator (B := B) (E := E)) where
  /-- **Positive parametrization of the operator domain.** The adjointable map `h` parametrizes
  `dom T` and satisfies `(1 + T* T) h² x = x` with the stated partial-domain conditions. -/
  h : AdjointableOperator.End B E
  /-- **Positive parametrization of the adjoint domain.** The adjointable map `l` parametrizes
  `dom T*` and satisfies `(1 + T T*) l² x = x` with the stated partial-domain conditions. -/
  l : AdjointableOperator.End B E
  /-- **Bounded transform of the regular operator.** The adjointable map `F` satisfies `F x = T (h
  x)` on every vector of `E`. -/
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
