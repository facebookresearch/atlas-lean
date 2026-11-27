/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.Adjointable.Contractive
public import MathlibExt.Analysis.CStarAlgebra.Module.ContinuousMap
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Tactic.Linarith

/-!
# Strong-adjoint families on continuous-function modules

Primal and adjoint vector orbits are continuous. A uniformly bounded family
acts pointwise on the actual supremum-norm function modules, with its actual
pointwise adjoint. The general constructor does not assume completeness of
the module carriers. On a compact parameter space and a complete source
carrier, Banach--Steinhaus derives the bound.

A family of coefficient representations has the sharper bound supplied by
star-homomorphism contractivity. No norm-continuity of the operator family,
countable generation, tensor fibre, homotopy relation or KK quotient is
constructed. Blackadar's standard homotopies (17.2.2) and strong-* warning
(20.1.1--20.1.2) are the source use; arbitrary interval fibres remain separate.
-/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter
open scoped CStarAlgebra RightActions

universe uX uA uB uE uF uU uV

private theorem continuous_family_diagonal
    {X : Type uX} [TopologicalSpace X]
    {U : Type uU} [NormedAddCommGroup U] [NormedSpace ℂ U]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (T : X → U →L[ℂ] V)
    (hT : ∀ x : U, Continuous fun t => T t x)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ t, ‖T t‖ ≤ C)
    (f : X → U) (hf : Continuous f) :
    Continuous fun t => T t (f t) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hden : 0 < 2 * (C + 1) := by nlinarith
  filter_upwards
    [(Metric.tendsto_nhds.mp hf.continuousAt)
      (ε / (2 * (C + 1))) (div_pos hε hden),
      (Metric.tendsto_nhds.mp (hT (f t₀)).continuousAt)
        (ε / 2) (half_pos hε)] with t hft hTt
  have hsmall : C * dist (f t) (f t₀) < ε / 2 := by
    have hmul := (lt_div_iff₀ hden).mp hft
    have hd : 0 ≤ dist (f t) (f t₀) := dist_nonneg
    nlinarith
  calc
    dist (T t (f t)) (T t₀ (f t₀)) ≤
        dist (T t (f t)) (T t (f t₀)) +
          dist (T t (f t₀)) (T t₀ (f t₀)) :=
      dist_triangle _ _ _
    _ ≤ C * dist (f t) (f t₀) +
          dist (T t (f t₀)) (T t₀ (f t₀)) :=
      add_le_add
        ((T t).dist_le_opNorm (f t) (f t₀) |>.trans
          (mul_le_mul_of_nonneg_right (hC t) dist_nonneg)) le_rfl
    _ < ε := by linarith

private def familyCLMOfBound
    (X : Type uX) [TopologicalSpace X] [CompactSpace X]
    {U : Type uU} [NormedAddCommGroup U] [NormedSpace ℂ U]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (T : X → U →L[ℂ] V)
    (hT : ∀ x : U, Continuous fun t => T t x)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ t, ‖T t‖ ≤ C) :
    C(X, U) →L[ℂ] C(X, V) := by
  let L : C(X, U) →ₗ[ℂ] C(X, V) :=
    { toFun := fun f =>
        { toFun := fun t => T t (f t)
          continuous_toFun :=
            continuous_family_diagonal T hT C hC0 hC f f.continuous }
      map_add' := by
        intro f g
        apply _root_.ContinuousMap.ext
        intro t
        exact map_add (T t) (f t) (g t)
      map_smul' := by
        intro c f
        apply _root_.ContinuousMap.ext
        intro t
        exact map_smul (T t) c (f t) }
  exact L.mkContinuous C fun f => by
    change ‖(L f : C(X, V))‖ ≤ C * ‖f‖
    apply (_root_.ContinuousMap.norm_le _ (mul_nonneg hC0 (norm_nonneg f))).2
    intro t
    change ‖T t (f t)‖ ≤ C * ‖f‖
    calc
      _ ≤ ‖T t‖ * ‖f t‖ := (T t).le_opNorm (f t)
      _ ≤ C * ‖f t‖ :=
        mul_le_mul_of_nonneg_right (hC t) (norm_nonneg (f t))
      _ ≤ C * ‖f‖ :=
        mul_le_mul_of_nonneg_left (f.norm_coe_le_norm t) hC0

namespace CStarModule.AdjointableOperator

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E and F be normed right inner-product modules over B, with
compatible complex normed-space structures. Let X be a compact topological space, and equip C(X,
B)ᵐᵒᵖ with a star-compatible partial order. Let T(t) : E → F be adjointable maps such that every
orbit t ↦ T(t)x and every adjoint orbit t ↦ T(t)*y is continuous.

If C ≥ 0 and ‖T(t)‖ ≤ C for all t ∈ X, then pointwise application defines an adjointable map
C(X, E) → C(X, F) over C(X, B).
-/
def continuousMapOfBound
    (X : Type uX) [TopologicalSpace X] [CompactSpace X]
    [PartialOrder (C(X, B))ᵐᵒᵖ] [StarOrderedRing (C(X, B))ᵐᵒᵖ]
    (T : X → AdjointableOperator B E F)
    (hT : ∀ x : E, Continuous fun t => T t x)
    (hTstar : ∀ y : F, Continuous fun t => (T t).adjoint y)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ t, ‖T t‖ ≤ C) :
    (letI : SMul (C(X, B))ᵐᵒᵖ C(X, E) :=
       CStarModule.ContinuousMap.rightAction (B := B) (E := E) X
     letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, E) :=
       CStarModule.ContinuousMap.cstarModule (B := B) (E := E) X
     letI : SMul (C(X, B))ᵐᵒᵖ C(X, F) :=
       CStarModule.ContinuousMap.rightAction (B := B) (E := F) X
     letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, F) :=
       CStarModule.ContinuousMap.cstarModule (B := B) (E := F) X
     AdjointableOperator C(X, B) C(X, E) C(X, F)) := by
  letI : SMul (C(X, B))ᵐᵒᵖ C(X, E) :=
    CStarModule.ContinuousMap.rightAction (B := B) (E := E) X
  letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, E) :=
    CStarModule.ContinuousMap.cstarModule (B := B) (E := E) X
  letI : SMul (C(X, B))ᵐᵒᵖ C(X, F) :=
    CStarModule.ContinuousMap.rightAction (B := B) (E := F) X
  letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, F) :=
    CStarModule.ContinuousMap.cstarModule (B := B) (E := F) X
  have hForward : ∀ t, ‖(T t).toContinuousLinearMap‖ ≤ C := by
    intro t
    simpa only [AdjointableOperator.norm_eq] using hC t
  have hAdjoint : ∀ t, ‖(T t).adjoint‖ ≤ C := by
    intro t
    exact (T t).norm_adjoint_le.trans (hC t)
  let L := familyCLMOfBound X (fun t => (T t).toContinuousLinearMap)
    hT C hC0 hForward
  let Lstar := familyCLMOfBound X (fun t => (T t).adjoint)
    hTstar C hC0 hAdjoint
  exact
    { toContinuousLinearMap := L
      adjoint := Lstar
      isAdjointPair' :=
        (AdjointableOperator.isAdjointPair_iff_adjoint_inner
          (B := C(X, B)) L Lstar).2 <| by
          intro f g
          apply _root_.ContinuousMap.ext
          intro t
          rw [CStarModule.ContinuousMap.rightInner_apply,
            CStarModule.ContinuousMap.rightInner_apply]
          change CStarModule.rightInner (B := B) (T t (f t)) (g t) =
            CStarModule.rightInner (B := B) (f t) ((T t).adjoint (g t))
          exact (T t).adjoint_inner (f t) (g t) }

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E and F be normed right inner-product modules over B, with
compatible complex normed-space structures. Let X be a compact topological space, and equip C(X,
B)ᵐᵒᵖ with a star-compatible partial order. Let T(t) : E → F be adjointable maps such that every
orbit t ↦ T(t)x and every adjoint orbit t ↦ T(t)*y is continuous.

If C ≥ 0 uniformly bounds ‖T(t)‖, the induced operator satisfies (T_X f)(t) = T(t)(f(t)) for f ∈
C(X, E).
-/
@[simp]
theorem continuousMapOfBound_apply
    (X : Type uX) [TopologicalSpace X] [CompactSpace X]
    [PartialOrder (C(X, B))ᵐᵒᵖ] [StarOrderedRing (C(X, B))ᵐᵒᵖ]
    (T : X → AdjointableOperator B E F)
    (hT : ∀ x : E, Continuous fun t => T t x)
    (hTstar : ∀ y : F, Continuous fun t => (T t).adjoint y)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ t, ‖T t‖ ≤ C)
    (f : C(X, E)) (t : X) :
    (letI : SMul (C(X, B))ᵐᵒᵖ C(X, E) :=
       CStarModule.ContinuousMap.rightAction (B := B) (E := E) X
     letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, E) :=
       CStarModule.ContinuousMap.cstarModule (B := B) (E := E) X
     letI : SMul (C(X, B))ᵐᵒᵖ C(X, F) :=
       CStarModule.ContinuousMap.rightAction (B := B) (E := F) X
     letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, F) :=
       CStarModule.ContinuousMap.cstarModule (B := B) (E := F) X
     continuousMapOfBound X T hT hTstar C hC0 hC f t = T t (f t)) := by
  rfl

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E and F be normed right inner-product modules over B, with
compatible complex normed-space structures. Let X be a compact topological space, and equip C(X,
B)ᵐᵒᵖ with a star-compatible partial order. Let T(t) : E → F be adjointable maps such that every
orbit t ↦ T(t)x and every adjoint orbit t ↦ T(t)*y is continuous.

If C ≥ 0 uniformly bounds ‖T(t)‖, the adjoint of the induced operator satisfies (T_X* g)(t) =
T(t)*(g(t)) for g ∈ C(X, F).
-/
@[simp]
theorem continuousMapOfBound_adjoint_apply
    (X : Type uX) [TopologicalSpace X] [CompactSpace X]
    [PartialOrder (C(X, B))ᵐᵒᵖ] [StarOrderedRing (C(X, B))ᵐᵒᵖ]
    (T : X → AdjointableOperator B E F)
    (hT : ∀ x : E, Continuous fun t => T t x)
    (hTstar : ∀ y : F, Continuous fun t => (T t).adjoint y)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ t, ‖T t‖ ≤ C)
    (g : C(X, F)) (t : X) :
    (letI : SMul (C(X, B))ᵐᵒᵖ C(X, E) :=
       CStarModule.ContinuousMap.rightAction (B := B) (E := E) X
     letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, E) :=
       CStarModule.ContinuousMap.cstarModule (B := B) (E := E) X
     letI : SMul (C(X, B))ᵐᵒᵖ C(X, F) :=
       CStarModule.ContinuousMap.rightAction (B := B) (E := F) X
     letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, F) :=
       CStarModule.ContinuousMap.cstarModule (B := B) (E := F) X
     (continuousMapOfBound X T hT hTstar C hC0 hC).adjoint g t =
       (T t).adjoint (g t)) := by
  rfl

omit [StarOrderedRing Bᵐᵒᵖ] in
private theorem compactFamily_bound
    (X : Type uX) [TopologicalSpace X] [CompactSpace X]
    [CompleteSpace E]
    (T : X → AdjointableOperator B E F)
    (hT : ∀ x : E, Continuous fun t => T t x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖T t‖ ≤ C := by
  have hPointwise : ∀ x : E, ∃ C : ℝ, ∀ t, ‖(T t).toContinuousLinearMap x‖ ≤ C := by
    intro x
    let orbit : C(X, F) := ⟨fun t => T t x, hT x⟩
    exact ⟨‖orbit‖, fun t => orbit.norm_coe_le_norm t⟩
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun t => (T t).toContinuousLinearMap)
    hPointwise
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  have ht : ‖T t‖ ≤ C := by
    simpa only [AdjointableOperator.norm_eq] using hC t
  exact ht.trans (le_max_left _ _)

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E and F be normed right inner-product modules over B, with
compatible complex normed-space structures. Let X be a compact topological space, and equip C(X,
B)ᵐᵒᵖ with a star-compatible partial order. Let T(t) : E → F be adjointable maps such that every
orbit t ↦ T(t)x and every adjoint orbit t ↦ T(t)*y is continuous.

If E is complete, pointwise application of the family defines an adjointable operator C(X, E) →
C(X, F) over C(X, B).
-/
def continuousMap
    (X : Type uX) [TopologicalSpace X] [CompactSpace X]
    [PartialOrder (C(X, B))ᵐᵒᵖ] [StarOrderedRing (C(X, B))ᵐᵒᵖ]
    [CompleteSpace E]
    (T : X → AdjointableOperator B E F)
    (hT : ∀ x : E, Continuous fun t => T t x)
    (hTstar : ∀ y : F, Continuous fun t => (T t).adjoint y) :
    (letI : SMul (C(X, B))ᵐᵒᵖ C(X, E) :=
       CStarModule.ContinuousMap.rightAction (B := B) (E := E) X
     letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, E) :=
       CStarModule.ContinuousMap.cstarModule (B := B) (E := E) X
     letI : SMul (C(X, B))ᵐᵒᵖ C(X, F) :=
       CStarModule.ContinuousMap.rightAction (B := B) (E := F) X
     letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, F) :=
       CStarModule.ContinuousMap.cstarModule (B := B) (E := F) X
     AdjointableOperator C(X, B) C(X, E) C(X, F)) :=
  continuousMapOfBound X T hT hTstar
    (Classical.choose (compactFamily_bound X T hT))
    (Classical.choose_spec (compactFamily_bound X T hT)).1
    (Classical.choose_spec (compactFamily_bound X T hT)).2

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E and F be normed right inner-product modules over B, with
compatible complex normed-space structures. Let X be a compact topological space, and equip C(X,
B)ᵐᵒᵖ with a star-compatible partial order. Let T(t) : E → F be adjointable maps such that every
orbit t ↦ T(t)x and every adjoint orbit t ↦ T(t)*y is continuous.

If E is complete, the induced operator satisfies (T_X f)(t) = T(t)(f(t)) for f ∈ C(X, E) and t ∈
X.
-/
@[simp]
theorem continuousMap_apply
    (X : Type uX) [TopologicalSpace X] [CompactSpace X]
    [PartialOrder (C(X, B))ᵐᵒᵖ] [StarOrderedRing (C(X, B))ᵐᵒᵖ]
    [CompleteSpace E]
    (T : X → AdjointableOperator B E F)
    (hT : ∀ x : E, Continuous fun t => T t x)
    (hTstar : ∀ y : F, Continuous fun t => (T t).adjoint y)
    (f : C(X, E)) (t : X) :
    (letI : SMul (C(X, B))ᵐᵒᵖ C(X, E) :=
       CStarModule.ContinuousMap.rightAction (B := B) (E := E) X
     letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, E) :=
       CStarModule.ContinuousMap.cstarModule (B := B) (E := E) X
     letI : SMul (C(X, B))ᵐᵒᵖ C(X, F) :=
       CStarModule.ContinuousMap.rightAction (B := B) (E := F) X
     letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, F) :=
       CStarModule.ContinuousMap.cstarModule (B := B) (E := F) X
     continuousMap X T hT hTstar f t = T t (f t)) := by
  simpa only [continuousMap] using
    continuousMapOfBound_apply X T hT hTstar
      (Classical.choose (compactFamily_bound X T hT))
      (Classical.choose_spec (compactFamily_bound X T hT)).1
      (Classical.choose_spec (compactFamily_bound X T hT)).2 f t

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E and F be normed right inner-product modules over B, with
compatible complex normed-space structures. Let X be a compact topological space, and equip C(X,
B)ᵐᵒᵖ with a star-compatible partial order. Let T(t) : E → F be adjointable maps such that every
orbit t ↦ T(t)x and every adjoint orbit t ↦ T(t)*y is continuous.

If E is complete, the adjoint of the induced operator satisfies (T_X* g)(t) = T(t)*(g(t)) for g
∈ C(X, F) and t ∈ X.
-/
@[simp]
theorem continuousMap_adjoint_apply
    (X : Type uX) [TopologicalSpace X] [CompactSpace X]
    [PartialOrder (C(X, B))ᵐᵒᵖ] [StarOrderedRing (C(X, B))ᵐᵒᵖ]
    [CompleteSpace E]
    (T : X → AdjointableOperator B E F)
    (hT : ∀ x : E, Continuous fun t => T t x)
    (hTstar : ∀ y : F, Continuous fun t => (T t).adjoint y)
    (g : C(X, F)) (t : X) :
    (letI : SMul (C(X, B))ᵐᵒᵖ C(X, E) :=
       CStarModule.ContinuousMap.rightAction (B := B) (E := E) X
     letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, E) :=
       CStarModule.ContinuousMap.cstarModule (B := B) (E := E) X
     letI : SMul (C(X, B))ᵐᵒᵖ C(X, F) :=
       CStarModule.ContinuousMap.rightAction (B := B) (E := F) X
     letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, F) :=
       CStarModule.ContinuousMap.cstarModule (B := B) (E := F) X
     (continuousMap X T hT hTstar).adjoint g t = (T t).adjoint (g t)) := by
  simpa only [continuousMap] using
    continuousMapOfBound_adjoint_apply X T hT hTstar
      (Classical.choose (compactFamily_bound X T hT))
      (Classical.choose_spec (compactFamily_bound X T hT)).1
      (Classical.choose_spec (compactFamily_bound X T hT)).2 g t


section Representation

variable {A : Type uA} [NonUnitalCStarAlgebra A]

/--
Let A and B be possibly nonunital complex C*-algebras, with a star-compatible partial order on
Bᵐᵒᵖ. Let E be a normed right inner-product B-module with a compatible complex normed-space
structure. Let X be a compact topological space, equip C(X, B)ᵐᵒᵖ with a star-compatible partial
order, and let φ(t) be nonunital complex star representations of A on E. Assume t ↦ φ(t)(a)x is
continuous for every a ∈ A and x ∈ E.

Pointwise action gives a nonunital complex star representation of A on the right C(X, B)-module
C(X, E).
-/
def continuousMapRepresentation
    (X : Type uX) [TopologicalSpace X] [CompactSpace X]
    [PartialOrder (C(X, B))ᵐᵒᵖ] [StarOrderedRing (C(X, B))ᵐᵒᵖ]
    (φ : X → A →⋆ₙₐ[ℂ] AdjointableOperator.End B E)
    (hφ : ∀ (a : A) (x : E), Continuous fun t => φ t a x) :
    (letI : SMul (C(X, B))ᵐᵒᵖ C(X, E) :=
       CStarModule.ContinuousMap.rightAction (B := B) (E := E) X
     letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, E) :=
       CStarModule.ContinuousMap.cstarModule (B := B) (E := E) X
     A →⋆ₙₐ[ℂ] AdjointableOperator.End C(X, B) C(X, E)) := by
  letI : SMul (C(X, B))ᵐᵒᵖ C(X, E) :=
    CStarModule.ContinuousMap.rightAction (B := B) (E := E) X
  letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, E) :=
    CStarModule.ContinuousMap.cstarModule (B := B) (E := E) X
  have hstar (a : A) (x : E) :
      Continuous fun t => (φ t a).adjoint x := by
    simpa only [map_star, AdjointableOperator.star_apply] using hφ (star a) x
  let lift : A → AdjointableOperator.End C(X, B) C(X, E) := fun a =>
    continuousMapOfBound X (fun t => φ t a) (hφ a) (hstar a)
      ‖a‖ (norm_nonneg a) (fun t => norm_nonUnitalStarAlgHom_apply_le (φ t) a)
  have hLift (a : A) (f : C(X, E)) (t : X) :
      lift a f t = φ t a (f t) :=
    continuousMapOfBound_apply X (fun s => φ s a) (hφ a) (hstar a)
      ‖a‖ (norm_nonneg a) (fun s => norm_nonUnitalStarAlgHom_apply_le (φ s) a) f t
  have hLiftStar (a : A) (f : C(X, E)) (t : X) :
      (lift a).adjoint f t = (φ t a).adjoint (f t) :=
    continuousMapOfBound_adjoint_apply X (fun s => φ s a) (hφ a) (hstar a)
      ‖a‖ (norm_nonneg a) (fun s => norm_nonUnitalStarAlgHom_apply_le (φ s) a) f t
  exact
    { toFun := lift
      map_zero' := by
        apply AdjointableOperator.ext
        intro f
        apply _root_.ContinuousMap.ext
        intro t
        simp only [hLift, map_zero, AdjointableOperator.zero_apply,
          _root_.ContinuousMap.zero_apply]
      map_add' := by
        intro a b
        apply AdjointableOperator.ext
        intro f
        apply _root_.ContinuousMap.ext
        intro t
        simp only [hLift, map_add, AdjointableOperator.add_apply,
          _root_.ContinuousMap.add_apply]
      map_mul' := by
        intro a b
        apply AdjointableOperator.ext
        intro f
        apply _root_.ContinuousMap.ext
        intro t
        simp only [hLift, map_mul, AdjointableOperator.mul_apply]
      map_smul' := by
        intro c a
        apply AdjointableOperator.ext
        intro f
        apply _root_.ContinuousMap.ext
        intro t
        simp only [hLift, map_smul, AdjointableOperator.smul_apply,
          _root_.ContinuousMap.smul_apply, MonoidHom.id_apply]
      map_star' := by
        intro a
        apply AdjointableOperator.ext
        intro f
        apply _root_.ContinuousMap.ext
        intro t
        simp only [hLift, map_star, AdjointableOperator.star_apply, hLiftStar] }

/--
Let A and B be possibly nonunital complex C*-algebras, with a star-compatible partial order on
Bᵐᵒᵖ. Let E be a normed right inner-product B-module with a compatible complex normed-space
structure. Let X be a compact topological space, equip C(X, B)ᵐᵒᵖ with a star-compatible partial
order, and let φ(t) be nonunital complex star representations of A on E. Assume t ↦ φ(t)(a)x is
continuous for every a ∈ A and x ∈ E.

The induced representation acts by (φ_X(a)f)(t) = φ(t)(a)(f(t)) for a ∈ A, f ∈ C(X, E) and t ∈
X.
-/
@[simp]
theorem continuousMapRepresentation_apply
    (X : Type uX) [TopologicalSpace X] [CompactSpace X]
    [PartialOrder (C(X, B))ᵐᵒᵖ] [StarOrderedRing (C(X, B))ᵐᵒᵖ]
    (φ : X → A →⋆ₙₐ[ℂ] AdjointableOperator.End B E)
    (hφ : ∀ (a : A) (x : E), Continuous fun t => φ t a x)
    (a : A) (f : C(X, E)) (t : X) :
    (letI : SMul (C(X, B))ᵐᵒᵖ C(X, E) :=
       CStarModule.ContinuousMap.rightAction (B := B) (E := E) X
     letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, E) :=
       CStarModule.ContinuousMap.cstarModule (B := B) (E := E) X
     continuousMapRepresentation X φ hφ a f t = φ t a (f t)) := by
  simp only [continuousMapRepresentation, NonUnitalStarAlgHom.coe_mk,
    continuousMapOfBound_apply]

end Representation

end CStarModule.AdjointableOperator
