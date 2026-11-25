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

public import MathlibExt.Analysis.CStarAlgebra.Module.ContinuousMap
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct
public import MathlibExt.Analysis.CStarAlgebra.Module.Compact
import MathlibExt.Analysis.CStarAlgebra.Module.Factorization
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Analysis.Complex.Basic

/-!
# The constant-family coefficient-extension tensor model

The coefficient extension is the literal constant-function map from B to
C(X,B). The computed model is C(X,E), with pure e b evaluated as e <• b(t).
The coefficient self-module and the existing function-module factories keep
their existing norms and their explicitly selected opposite-order dictionaries.

The result concerns only this constant-family model. It does not construct
the evaluation fibre of an arbitrary Hilbert C(X,B)-module, countable
generation, a homotopy relation or a KK quotient.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped RightActions

namespace CStarModule.InternalTensorProduct

universe uX uB uE

variable {B : Type uB} [NonUnitalCStarAlgebra B]

section Pure

variable [PartialOrder Bᵐᵒᵖ]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E be a normed
right inner-product module over B, with compatible complex normed-space structures. Let X be a
topological space.

For e ∈ E and b ∈ C(X, B), the pure vector is the continuous function t ↦ e b(t).
-/
def continuousMapPure (X : Type uX) [TopologicalSpace X]
    (e : E) (b : C(X, B)) : C(X, E) where
  toFun t := e <• b t
  continuous_toFun :=
    (CStarModule.continuous_const_right_smul (B := B) e).comp b.continuous

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E be a normed
right inner-product module over B, with compatible complex normed-space structures. Let X be a
topological space.

For e ∈ E, b ∈ C(X, B) and t ∈ X, the pure vector evaluates to e b(t).
-/
@[simp]
theorem continuousMapPure_apply (X : Type uX) [TopologicalSpace X]
    (e : E) (b : C(X, B)) (t : X) :
    continuousMapPure (B := B) X e b t = e <• b t :=
  rfl

end Pure

section Coefficients

/--
Let B be a possibly nonunital complex C*-algebra. Let X be a compact topological space and equip
C(X, B)ᵐᵒᵖ with a star-compatible partial order.

Constant B-valued functions acting by left multiplication define a nonunital complex star
representation of B on the right coefficient self-module C(X, B).
-/
def continuousMapCoefficientRepresentation (X : Type uX)
    [TopologicalSpace X] [CompactSpace X]
    [PartialOrder (C(X, B))ᵐᵒᵖ] [StarOrderedRing (C(X, B))ᵐᵒᵖ] :
    (letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, B) :=
       CStarModule.Right.selfModule
     B →⋆ₙₐ[ℂ] CStarModule.AdjointableOperator.End C(X, B) C(X, B)) := by
  letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, B) :=
    CStarModule.Right.selfModule
  let κ : B →⋆ₙₐ[ℂ] C(X, B) :=
    { toFun := _root_.ContinuousMap.const X
      map_zero' := _root_.ContinuousMap.ext fun _ => rfl
      map_add' := fun _ _ => _root_.ContinuousMap.ext fun _ => rfl
      map_mul' := fun _ _ => _root_.ContinuousMap.ext fun _ => rfl
      map_smul' := fun _ _ => _root_.ContinuousMap.ext fun _ => rfl
      map_star' := fun _ => _root_.ContinuousMap.ext fun _ => rfl }
  exact (CStarModule.AdjointableOperator.leftRegular (B := C(X, B))).comp κ

/--
Let B be a possibly nonunital complex C*-algebra. Let X be a compact topological space and equip
C(X, B)ᵐᵒᵖ with a star-compatible partial order.

For b ∈ B, f ∈ C(X, B) and t ∈ X, the constant coefficient representation evaluates to b f(t).
-/
@[simp]
theorem continuousMapCoefficientRepresentation_apply (X : Type uX)
    [TopologicalSpace X] [CompactSpace X]
    [PartialOrder (C(X, B))ᵐᵒᵖ] [StarOrderedRing (C(X, B))ᵐᵒᵖ]
    (a : B) (b : C(X, B)) (t : X) :
    (letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, B) :=
       CStarModule.Right.selfModule
     continuousMapCoefficientRepresentation (B := B) X a b t = a * b t) := by
  let : CStarModule (C(X, B))ᵐᵒᵖ C(X, B) :=
    CStarModule.Right.selfModule
  simp only [continuousMapCoefficientRepresentation, NonUnitalStarAlgHom.comp_apply,
    CStarModule.AdjointableOperator.leftRegular_apply, _root_.ContinuousMap.mul_apply]
  change (_root_.ContinuousMap.const X a) t * b t = a * b t
  rw [_root_.ContinuousMap.const_apply]

end Coefficients

section Model

variable [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- Finite scalar-weight approximation on the compact image in E, followed
by nonunital factorization, derives density of actual pure vectors.
No separation assumption on the compact parameter space is needed. -/
private theorem continuousMapPure_dense (X : Type uX)
    [TopologicalSpace X] [CompactSpace X] :
    Dense (Submodule.span ℂ
      (Set.range fun p : E × C(X, B) =>
        continuousMapPure (B := B) X p.1 p.2) : Set C(X, E)) := by
  classical
  intro f
  apply Metric.mem_closure_iff.2
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := half_pos hε
  let K : Set E := Set.range f
  have hK : IsCompact K := isCompact_range f.continuous
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun e : E => Metric.ball e δ) (fun _ => Metric.isOpen_ball)
    (by
      intro e he
      exact Set.mem_iUnion.mpr ⟨e, by
        simpa only [Metric.mem_ball, dist_self] using hδ⟩)
  let ι : Type uE := ↥s
  let U : ι → Set E := fun i => Metric.ball i.1 δ
  have hU : K ⊆ ⋃ i : ι, U i := by
    intro e he
    obtain ⟨i, hi, hie⟩ := Set.mem_iUnion₂.mp (hs he)
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hie⟩
  obtain ⟨ρ, hρ⟩ :=
    PartitionOfUnity.exists_isSubordinate_of_locallyFinite hK.isClosed U
      (fun _ => Metric.isOpen_ball) (locallyFinite_of_finite U) hU
  choose y a hy using fun i : ι =>
    CStarModule.exists_right_factor_of_starOrderedRing (B := B) (E := E) i.1
  let b : ι → C(X, B) := fun i =>
    { toFun := fun t => (ρ i (f t) : ℂ) • a i
      continuous_toFun :=
        (Complex.continuous_ofReal.comp ((ρ i).continuous.comp f.continuous)).smul
          continuous_const }
  let g : C(X, E) := ∑ i : ι, continuousMapPure (B := B) X (y i) (b i)
  have hg : g ∈ Submodule.span ℂ
      (Set.range fun p : E × C(X, B) =>
        continuousMapPure (B := B) X p.1 p.2) :=
    Submodule.sum_mem _ fun i hi =>
      Submodule.subset_span ⟨(y i, b i), rfl⟩
  have hsum (t : X) : ∑ i : ι, ρ i (f t) = 1 := by
    rw [← finsum_eq_sum_of_fintype]
    exact ρ.sum_eq_one (show f t ∈ K from ⟨t, rfl⟩)
  have hsumC (t : X) : ∑ i : ι, (ρ i (f t) : ℂ) = 1 := by
    calc
      _ = Complex.ofRealCLM (∑ i : ι, ρ i (f t)) := by
        simpa only [Complex.ofRealCLM_apply] using
          (map_sum Complex.ofRealCLM (fun i : ι => ρ i (f t)) Finset.univ).symm
      _ = 1 := by rw [hsum]; rfl
  have hgsum (t : X) :
      g t = ∑ i : ι, (ρ i (f t) : ℂ) • i.1 := by
    simp only [g, _root_.ContinuousMap.sum_apply, continuousMapPure_apply, b]
    apply Finset.sum_congr rfl
    intro i hi
    change y i <• ((ρ i (f t) : ℂ) • a i) = (ρ i (f t) : ℂ) • i.1
    rw [CStarModule.right_smul_smul, ← hy i]
  have hpoint (t : X) : ‖f t - g t‖ ≤ δ := by
    have hdecomp : f t - g t =
        ∑ i : ι, (ρ i (f t) : ℂ) • (f t - i.1) := by
      rw [hgsum t]
      simp only [smul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_smul, hsumC t, one_smul]
    rw [hdecomp]
    calc
      _ ≤ ∑ i : ι, ‖(ρ i (f t) : ℂ) • (f t - i.1)‖ :=
        _root_.norm_sum_le Finset.univ _
      _ ≤ ∑ i : ι, ρ i (f t) * δ := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hzero : ρ i (f t) = 0
        · simp only [hzero, Complex.ofReal_zero, zero_smul, norm_zero, zero_mul, le_refl]
        · have hball : f t ∈ U i :=
            hρ i (subset_closure (show f t ∈ Function.support (ρ i) from hzero))
          have hnear : ‖f t - i.1‖ < δ := by
            simpa only [U, Metric.mem_ball, dist_eq_norm] using hball
          rw [_root_.norm_smul, Complex.norm_of_nonneg (ρ.nonneg i (f t))]
          exact mul_le_mul_of_nonneg_left hnear.le (ρ.nonneg i (f t))
      _ = δ := by rw [← Finset.sum_mul, hsum t, one_mul]
  have hnorm : ‖f - g‖ ≤ δ := by
    apply (_root_.ContinuousMap.norm_le (f - g) hδ.le).2
    intro t
    simpa only [_root_.ContinuousMap.sub_apply] using hpoint t
  refine ⟨g, hg, ?_⟩
  rw [dist_eq_norm]
  exact hnorm.trans_lt (half_lt_self hε)

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E be a complete normed right inner-product module over B,
with compatible complex normed-space structures. Let X be a compact topological space, and equip
C(X, B)ᵐᵒᵖ with a star-compatible partial order.

The right C(X, B)-module C(X, E), with pure vectors t ↦ e b(t), satisfies the defining
inner-product, balancing, linearity and dense-span properties of the internal tensor product for
extension by constant coefficients.
-/
theorem continuousMap_isModel (X : Type uX)
    [TopologicalSpace X] [CompactSpace X]
    [PartialOrder (C(X, B))ᵐᵒᵖ] [StarOrderedRing (C(X, B))ᵐᵒᵖ] :
    (letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, B) :=
       CStarModule.Right.selfModule
     letI : SMul (C(X, B))ᵐᵒᵖ C(X, E) :=
       CStarModule.ContinuousMap.rightAction (B := B) (E := E) X
     letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, E) :=
       CStarModule.ContinuousMap.cstarModule (B := B) (E := E) X
     IsModel (continuousMapCoefficientRepresentation (B := B) X)
       (continuousMapPure (B := B) (E := E) X)) := by
  let : CStarModule (C(X, B))ᵐᵒᵖ C(X, B) :=
    CStarModule.Right.selfModule
  let : SMul (C(X, B))ᵐᵒᵖ C(X, E) :=
    CStarModule.ContinuousMap.rightAction (B := B) (E := E) X
  let : CStarModule (C(X, B))ᵐᵒᵖ C(X, E) :=
    CStarModule.ContinuousMap.cstarModule (B := B) (E := E) X
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, continuousMapPure_dense (B := B) (E := E) X⟩
  · intro x y b
    apply _root_.ContinuousMap.ext
    intro t
    simp only [continuousMapPure_apply, _root_.ContinuousMap.add_apply,
      CStarModule.add_right_smul]
  · intro x b c
    apply _root_.ContinuousMap.ext
    intro t
    simp only [continuousMapPure_apply, _root_.ContinuousMap.add_apply,
      CStarModule.right_smul_add]
  · intro c x b
    apply _root_.ContinuousMap.ext
    intro t
    simp only [continuousMapPure_apply, _root_.ContinuousMap.smul_apply,
      CStarModule.smul_right_smul]
  · intro c x b
    apply _root_.ContinuousMap.ext
    intro t
    simp only [continuousMapPure_apply, _root_.ContinuousMap.smul_apply,
      CStarModule.right_smul_smul]
  · intro x a b
    apply _root_.ContinuousMap.ext
    intro t
    simp only [continuousMapPure_apply, continuousMapCoefficientRepresentation_apply,
      CStarModule.right_smul_mul]
  · intro x b c
    apply _root_.ContinuousMap.ext
    intro t
    simp only [continuousMapPure_apply, CStarModule.Right.right_smul_self,
      _root_.ContinuousMap.mul_apply, CStarModule.ContinuousMap.right_smul_apply,
      CStarModule.right_smul_mul]
  · intro x y b c
    apply _root_.ContinuousMap.ext
    intro t
    simp only [CStarModule.ContinuousMap.rightInner_apply, continuousMapPure_apply,
      CStarModule.Right.rightInner_self, _root_.ContinuousMap.mul_apply,
      _root_.ContinuousMap.star_apply, continuousMapCoefficientRepresentation_apply,
      CStarModule.rightInner_left_smul, CStarModule.rightInner_right_smul, mul_assoc]

end Model

end CStarModule.InternalTensorProduct
