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

public import MathlibExt.Analysis.CStarAlgebra.IdealQuotient
public import MathlibExt.Analysis.CStarAlgebra.Module.Adjointable.OfPair
public import Mathlib.Analysis.Normed.Operator.Mul

import Mathlib.Analysis.CStarAlgebra.ApproximateUnit

/-!
# Rank-one and compact operators on right C-star modules

This file defines the canonical rank-one adjointable map

`theta(x,y)(z) = x <• rightInner y z`,

then forms finite-rank maps as its complex linear span and compact module maps
as the operator-norm closure of that span.  These are Hilbert C-star-module
compact maps, not Banach-space `IsCompactOperator`s.

Coefficient, source, and target universes are independent.  No completeness
or fullness hypothesis is required for the rank-one or closure carriers.
-/

@[expose] public section

noncomputable section

open Set
open Filter
open scoped CStarAlgebra RightActions

namespace CStarModule

namespace AdjointableOperator

universe uB uE uF uG

variable {B : Type uB} {E : Type uE} {F : Type uF} {G : Type uG}
variable [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F]
variable [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G]
  [CStarModule Bᵐᵒᵖ G]

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

For x ∈ F and y ∈ E, the rank-one module operator is the bounded complex-linear map z ↦ x⟨y, z⟩
from E to F.
-/
def rankOneCLM (x : F) (y : E) : E →L[ℂ] F :=
  LinearMap.mkContinuous
    { toFun := fun z ↦ x <• rightInner (B := B) y z
      map_add' := by
        intro z w
        rw [rightInner_add_right, right_smul_add]
      map_smul' := by
        intro c z
        rw [rightInner_smul_right, right_smul_smul]
        change c • (x <• rightInner (B := B) y z) =
          c • (x <• rightInner (B := B) y z)
        rfl }
    (4 * ‖x‖ * ‖y‖) fun z ↦ by
      calc
        ‖x <• rightInner (B := B) y z‖ ≤
            ‖x‖ * ‖rightInner (B := B) y z‖ :=
          CStarModule.norm_right_smul_le x _
        _ ≤ ‖x‖ * (4 * ‖y‖ * ‖z‖) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg x)
          exact CStarModule.norm_rightInner_le_four_mul y z
        _ = (4 * ‖x‖ * ‖y‖) * ‖z‖ := by ring

@[simp]
theorem rankOneCLM_apply (x : F) (y z : E) :
    rankOneCLM (B := B) x y z = x <• rightInner (B := B) y z :=
  rfl

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

For x ∈ F and y ∈ E, the rank-one module map z ↦ x⟨y, z⟩ is adjointable; its adjoint is w ↦ y⟨x,
w⟩.
-/
def rankOne (x : F) (y : E) : AdjointableOperator B E F :=
  ofAdjointPair
    (rankOneCLM (B := B) x y)
    (rankOneCLM (B := B) y x) <| by
      intro z w
      rw [rankOneCLM_apply, rankOneCLM_apply,
        rightInner_left_smul, rightInner_right_smul,
        star_rightInner]

@[simp]
theorem rankOne_apply (x : F) (y z : E) :
    rankOne (B := B) x y z = x <• rightInner (B := B) y z :=
  by
    change (rankOne (B := B) x y).toContinuousLinearMap z = _
    rfl

@[simp]
theorem rankOne_adjoint (x : F) (y : E) :
    (rankOne (B := B) x y).adjoint = rankOneCLM (B := B) y x :=
  rfl

@[simp]
theorem rankOne_adjointOperator (x : F) (y : E) :
    (rankOne (B := B) x y).adjointOperator = rankOne (B := B) y x := by
  ext z
  change rankOneCLM (B := B) y x z = rankOneCLM (B := B) y x z
  rfl

theorem norm_rankOne_le [StarOrderedRing Bᵐᵒᵖ] (x : F) (y : E) :
    ‖rankOne (B := B) x y‖ ≤ ‖x‖ * ‖y‖ := by
  rw [AdjointableOperator.norm_eq]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  change ‖x <• rightInner (B := B) y z‖ ≤
    (‖x‖ * ‖y‖) * ‖z‖
  calc
    ‖x <• rightInner (B := B) y z‖ ≤
        ‖x‖ * ‖rightInner (B := B) y z‖ :=
      CStarModule.norm_right_smul_le x _
    _ ≤ ‖x‖ * (‖y‖ * ‖z‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg x)
      rw [rightInner, MulOpposite.norm_unop]
      exact CStarModule.norm_inner_le E
    _ = (‖x‖ * ‖y‖) * ‖z‖ := by ring

@[simp]
theorem comp_rankOne (T : AdjointableOperator B F G)
    (x : F) (y : E) :
    T.comp (rankOne (B := B) x y) = rankOne (B := B) (T x) y := by
  ext z
  change T.toContinuousLinearMap (rankOneCLM (B := B) x y z) =
    rankOneCLM (B := B) (T x) y z
  rw [rankOneCLM_apply, rankOneCLM_apply]
  change T (x <• rightInner (B := B) y z) =
    T x <• rightInner (B := B) y z
  exact T.map_right_smul x _

@[simp]
theorem rankOne_comp (x : F) (y : E)
    (T : AdjointableOperator B G E) :
    (rankOne (B := B) x y).comp T =
      rankOne (B := B) x (T.adjointOperator y) := by
  ext z
  change rankOneCLM (B := B) x y (T z) =
    rankOneCLM (B := B) x (T.adjointOperator y) z
  simp only [rankOneCLM_apply]
  have hinner : rightInner (B := B) y (T z) =
      rightInner (B := B) (T.adjointOperator y) z := by
    simpa only [star_rightInner, adjointOperator_apply] using
      congrArg star (T.adjoint_inner z y)
  rw [hinner]

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

The rank-one module operators E → F are the maps z ↦ x⟨y, z⟩ as x ∈ F and y ∈ E vary.
-/
def rankOneSet : Set (AdjointableOperator B E F) :=
  Set.range fun p : F × E ↦ rankOne p.1 p.2

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

The finite-rank module operators E → F form the complex-linear span of the rank-one module
operators.
-/
def finiteRankSubmodule : Submodule ℂ (AdjointableOperator B E F) :=
  Submodule.span ℂ (rankOneSet (B := B) (E := E) (F := F))

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

The compact module operators E → F form the operator-norm closure of the complex span of the
rank-one module operators.
-/
def compactSubmodule : Submodule ℂ (AdjointableOperator B E F) :=
  (finiteRankSubmodule (B := B) (E := E) (F := F)).topologicalClosure

theorem rankOne_mem_finiteRank (x : F) (y : E) :
    rankOne (B := B) x y ∈
      finiteRankSubmodule (B := B) (E := E) (F := F) :=
  Submodule.subset_span ⟨(x, y), rfl⟩

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E, F and G be
normed right inner-product modules over B, with compatible complex normed-space structures.

For adjointable S : F → G and finite-rank module T : E → F, the composite S ∘ T is finite-rank.
-/
theorem comp_mem_finiteRank_right (S : AdjointableOperator B F G)
    {T : AdjointableOperator B E F}
    (hT : T ∈ finiteRankSubmodule (B := B) (E := E) (F := F)) :
    S.comp T ∈ finiteRankSubmodule (B := B) (E := E) (F := G) := by
  refine Submodule.span_induction (p := fun T _ ↦
    S.comp T ∈ finiteRankSubmodule (B := B) (E := E) (F := G))
    ?_ ?_ ?_ ?_ hT
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    rw [comp_rankOne]
    exact rankOne_mem_finiteRank (B := B) (E := E) (F := G) (S x) y
  · change postcompCLM (B := B) (E := E) S 0 ∈
      finiteRankSubmodule (B := B) (E := E) (F := G)
    simpa only [map_zero] using
      (Submodule.zero_mem (finiteRankSubmodule
        (B := B) (E := E) (F := G)))
  · intro T U _ _ hT hU
    change postcompCLM (B := B) (E := E) S (T + U) ∈
      finiteRankSubmodule (B := B) (E := E) (F := G)
    change postcompCLM (B := B) (E := E) S T ∈
      finiteRankSubmodule (B := B) (E := E) (F := G) at hT
    change postcompCLM (B := B) (E := E) S U ∈
      finiteRankSubmodule (B := B) (E := E) (F := G) at hU
    simpa only [map_add] using
      (Submodule.add_mem _ hT hU)
  · intro c T _ hT
    change postcompCLM (B := B) (E := E) S (c • T) ∈
      finiteRankSubmodule (B := B) (E := E) (F := G)
    change postcompCLM (B := B) (E := E) S T ∈
      finiteRankSubmodule (B := B) (E := E) (F := G) at hT
    simpa only [map_smul] using
      (Submodule.smul_mem _ c hT)

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E, F and G be
normed right inner-product modules over B, with compatible complex normed-space structures.

For finite-rank module S : F → G and adjointable T : E → F, the composite S ∘ T is finite-rank.
-/
theorem comp_mem_finiteRank_left {S : AdjointableOperator B F G}
    (hS : S ∈ finiteRankSubmodule (B := B) (E := F) (F := G))
    (T : AdjointableOperator B E F) :
    S.comp T ∈ finiteRankSubmodule (B := B) (E := E) (F := G) := by
  refine Submodule.span_induction (p := fun S _ ↦
    S.comp T ∈ finiteRankSubmodule (B := B) (E := E) (F := G))
    ?_ ?_ ?_ ?_ hS
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    rw [rankOne_comp]
    exact rankOne_mem_finiteRank (B := B) (E := E) (F := G)
      x (T.adjointOperator y)
  · change precompCLM (B := B) (G := G) T 0 ∈
      finiteRankSubmodule (B := B) (E := E) (F := G)
    simpa only [map_zero] using
      (Submodule.zero_mem (finiteRankSubmodule
        (B := B) (E := E) (F := G)))
  · intro S U _ _ hS hU
    change precompCLM (B := B) (G := G) T (S + U) ∈
      finiteRankSubmodule (B := B) (E := E) (F := G)
    change precompCLM (B := B) (G := G) T S ∈
      finiteRankSubmodule (B := B) (E := E) (F := G) at hS
    change precompCLM (B := B) (G := G) T U ∈
      finiteRankSubmodule (B := B) (E := E) (F := G) at hU
    simpa only [map_add] using
      (Submodule.add_mem _ hS hU)
  · intro c S _ hS
    change precompCLM (B := B) (G := G) T (c • S) ∈
      finiteRankSubmodule (B := B) (E := E) (F := G)
    change precompCLM (B := B) (G := G) T S ∈
      finiteRankSubmodule (B := B) (E := E) (F := G) at hS
    simpa only [map_smul] using
      (Submodule.smul_mem _ c hS)

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

The adjoint of a finite-rank module map E → F is a finite-rank module map F → E.
-/
theorem adjointOperator_mem_finiteRank {T : AdjointableOperator B E F}
    (hT : T ∈ finiteRankSubmodule (B := B) (E := E) (F := F)) :
    T.adjointOperator ∈
      finiteRankSubmodule (B := B) (E := F) (F := E) := by
  refine Submodule.span_induction (p := fun T _ ↦
    T.adjointOperator ∈
      finiteRankSubmodule (B := B) (E := F) (F := E))
    ?_ ?_ ?_ ?_ hT
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    rw [rankOne_adjointOperator]
    exact rankOne_mem_finiteRank (B := B) (E := F) (F := E) y x
  · simpa only [zero_adjointOperator] using
      (Submodule.zero_mem (finiteRankSubmodule
        (B := B) (E := F) (F := E)))
  · intro T U _ _ hT hU
    rw [add_adjointOperator]
    exact Submodule.add_mem _ hT hU
  · intro c T _ hT
    rw [smul_adjointOperator]
    exact Submodule.smul_mem _ (star c) hT

theorem finiteRank_le_compact :
    finiteRankSubmodule (B := B) (E := E) (F := F) ≤
      compactSubmodule (B := B) (E := E) (F := F) :=
  (finiteRankSubmodule (B := B) (E := E) (F := F)).le_topologicalClosure

theorem rankOne_mem_compact (x : F) (y : E) :
    rankOne (B := B) x y ∈
      compactSubmodule (B := B) (E := E) (F := F) :=
  finiteRank_le_compact (rankOne_mem_finiteRank x y)

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E, F and G be
normed right inner-product modules over B, with compatible complex normed-space structures.

For adjointable S : F → G and compact module T : E → F, the composite S ∘ T is compact.
-/
theorem comp_mem_compact_right (S : AdjointableOperator B F G)
    {T : AdjointableOperator B E F}
    (hT : T ∈ compactSubmodule (B := B) (E := E) (F := F)) :
    S.comp T ∈ compactSubmodule (B := B) (E := E) (F := G) := by
  change T ∈ closure
    (finiteRankSubmodule (B := B) (E := E) (F := F) :
      Set (AdjointableOperator B E F)) at hT
  change S.comp T ∈ closure
    (finiteRankSubmodule (B := B) (E := E) (F := G) :
      Set (AdjointableOperator B E G))
  exact map_mem_closure (f := fun T ↦ S.comp T)
    (postcompCLM (B := B) (E := E) S).continuous hT
    (fun _ h ↦ comp_mem_finiteRank_right S h)

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E, F and G be
normed right inner-product modules over B, with compatible complex normed-space structures.

For compact module S : F → G and adjointable T : E → F, the composite S ∘ T is compact.
-/
theorem comp_mem_compact_left {S : AdjointableOperator B F G}
    (hS : S ∈ compactSubmodule (B := B) (E := F) (F := G))
    (T : AdjointableOperator B E F) :
    S.comp T ∈ compactSubmodule (B := B) (E := E) (F := G) := by
  change S ∈ closure
    (finiteRankSubmodule (B := B) (E := F) (F := G) :
      Set (AdjointableOperator B F G)) at hS
  change S.comp T ∈ closure
    (finiteRankSubmodule (B := B) (E := E) (F := G) :
      Set (AdjointableOperator B E G))
  exact map_mem_closure (f := fun S ↦ S.comp T)
    (precompCLM (B := B) (G := G) T).continuous hS
    (fun _ h ↦ comp_mem_finiteRank_left h T)

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E and F be normed right inner-product modules over B, with
compatible complex normed-space structures.

The adjoint of a compact module map E → F is a compact module map F → E.
-/
theorem adjointOperator_mem_compact [StarOrderedRing Bᵐᵒᵖ]
    {T : AdjointableOperator B E F}
    (hT : T ∈ compactSubmodule (B := B) (E := E) (F := F)) :
    T.adjointOperator ∈
      compactSubmodule (B := B) (E := F) (F := E) := by
  change T ∈ closure
    (finiteRankSubmodule (B := B) (E := E) (F := F) :
      Set (AdjointableOperator B E F)) at hT
  change T.adjointOperator ∈ closure
    (finiteRankSubmodule (B := B) (E := F) (F := E) :
      Set (AdjointableOperator B F E))
  exact map_mem_closure (f := fun T ↦ T.adjointOperator)
    (continuous_adjointOperator (B := B) (E := E) (F := F)) hT
    (fun _ h ↦ adjointOperator_mem_finiteRank h)

theorem isClosed_compactSubmodule :
    IsClosed (compactSubmodule (B := B) (E := E) (F := F) :
      Set (AdjointableOperator B E F)) :=
  (finiteRankSubmodule (B := B) (E := E) (F := F)).isClosed_topologicalClosure

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E be a normed
right inner-product module over B, with compatible complex normed-space structures.

The finite-rank module endomorphisms of E form a nonunital complex star subalgebra of the
adjointable endomorphisms.
-/
noncomputable def finiteRankStarSubalgebra :
    NonUnitalStarSubalgebra ℂ (End B E) where
  carrier := finiteRankSubmodule (B := B) (E := E) (F := E)
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  smul_mem' := fun c _ hT ↦ Submodule.smul_mem _ c hT
  mul_mem' := by
    intro S T _hS hT
    change S.comp T ∈ finiteRankSubmodule (B := B) (E := E) (F := E)
    exact comp_mem_finiteRank_right S hT
  star_mem' := by
    intro T hT
    change T.adjointOperator ∈
      finiteRankSubmodule (B := B) (E := E) (F := E)
    exact adjointOperator_mem_finiteRank hT

@[simp]
theorem mem_finiteRankStarSubalgebra (T : End B E) :
    T ∈ finiteRankStarSubalgebra (B := B) (E := E) ↔
      T ∈ finiteRankSubmodule (B := B) (E := E) (F := E) :=
  Iff.rfl

theorem finiteRankStarSubalgebra_toSubmodule :
    (finiteRankStarSubalgebra (B := B) (E := E)).toNonUnitalSubalgebra.toSubmodule =
      finiteRankSubmodule (B := B) (E := E) (F := E) :=
  rfl

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E be a normed right inner-product module over B, with
compatible complex normed-space structures.

The compact module endomorphisms of E form a nonunital complex star subalgebra of the
adjointable endomorphisms.
-/
noncomputable def compactStarSubalgebra [StarOrderedRing Bᵐᵒᵖ] :
    NonUnitalStarSubalgebra ℂ (End B E) where
  carrier := compactSubmodule (B := B) (E := E) (F := E)
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  smul_mem' := fun c _ hT ↦ Submodule.smul_mem _ c hT
  mul_mem' := by
    intro S T _hS hT
    change S.comp T ∈ compactSubmodule (B := B) (E := E) (F := E)
    exact comp_mem_compact_right S hT
  star_mem' := by
    intro T hT
    change T.adjointOperator ∈
      compactSubmodule (B := B) (E := E) (F := E)
    exact adjointOperator_mem_compact hT

@[simp]
theorem mem_compactStarSubalgebra [StarOrderedRing Bᵐᵒᵖ] (T : End B E) :
    T ∈ compactStarSubalgebra (B := B) (E := E) ↔
      T ∈ compactSubmodule (B := B) (E := E) (F := E) :=
  Iff.rfl

theorem compactStarSubalgebra_toSubmodule [StarOrderedRing Bᵐᵒᵖ] :
    (compactStarSubalgebra (B := B) (E := E)).toNonUnitalSubalgebra.toSubmodule =
      compactSubmodule (B := B) (E := E) (F := E) :=
  rfl

instance compactStarSubalgebra_isClosed [StarOrderedRing Bᵐᵒᵖ] :
    IsClosed (compactStarSubalgebra (B := B) (E := E) : Set (End B E)) :=
  isClosed_compactSubmodule

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E be a normed right inner-product module over B, with
compatible complex normed-space structures.

The compact endomorphisms of E are the adjointable endomorphisms lying in the operator-norm
closure of the rank-one span.
-/
abbrev CompactEnd (B : Type uB) (E : Type uE)
    [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
    [StarOrderedRing Bᵐᵒᵖ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
    [CStarModule Bᵐᵒᵖ E] :=
  compactStarSubalgebra (B := B) (E := E)

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E be a complete normed right inner-product module over B,
with compatible complex normed-space structures.

The compact endomorphisms of E form a closed two-sided star ideal in the C*-algebra of
adjointable endomorphisms.
-/
noncomputable def compactClosedStarIdeal [StarOrderedRing Bᵐᵒᵖ]
    [CompleteSpace E] :
    ClosedStarIdeal (End B E) where
  carrier := compactStarSubalgebra (B := B) (E := E)
  isTwoSided := by
    constructor
    · intro S T hT
      change S.comp T ∈ compactSubmodule (B := B) (E := E) (F := E)
      exact comp_mem_compact_right S hT
    · intro T hT S
      change T.comp S ∈ compactSubmodule (B := B) (E := E) (F := E)
      exact comp_mem_compact_left hT S
  isClosed := isClosed_compactSubmodule

@[simp]
theorem mem_compactClosedStarIdeal [StarOrderedRing Bᵐᵒᵖ]
    [CompleteSpace E] (T : End B E) :
    T ∈ compactClosedStarIdeal (B := B) (E := E) ↔
      T ∈ compactSubmodule (B := B) (E := E) (F := E) :=
  Iff.rfl

/-! ## The coefficient self module -/

section Self

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]

/-- The canonical right self-module dictionary for the coefficient algebra. -/
local instance : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra has a star-compatible
partial order.

On the coefficient self-module B, with right multiplication and inner product ⟨x, y⟩ = star(x)y,
left multiplication by b ∈ B is adjointable, with adjoint left multiplication by star(b).
-/
def leftMul (b : B) : End B B where
  toContinuousLinearMap := ContinuousLinearMap.mul ℂ B b
  adjoint := ContinuousLinearMap.mul ℂ B (star b)
  isAdjointPair' := (isAdjointPair_iff_adjoint_inner _ _).2 <| by
    intro x y
    simp [CStarModule.Right.rightInner_self, mul_assoc]

@[simp]
theorem leftMul_apply (b x : B) : leftMul (B := B) b x = b * x :=
  rfl

@[simp]
theorem leftMul_adjointOperator (b : B) :
    (leftMul (B := B) b).adjointOperator = leftMul (B := B) (star b) := by
  ext x
  rfl

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra has a star-compatible
partial order.

On the right coefficient self-module B with inner product ⟨x, y⟩ = star(x)y, left multiplication
defines a nonunital complex star homomorphism from B to its adjointable endomorphisms.
-/
def leftRegular : B →⋆ₙₐ[ℂ] End B B where
  toFun := leftMul (B := B)
  map_zero' := by
    ext x
    simp
  map_add' b c := by
    ext x
    simp [add_mul]
  map_mul' b c := by
    ext x
    simp [mul_assoc]
  map_smul' c b := by
    ext x
    simp [smul_mul_assoc]
  map_star' b := by
    change leftMul (B := B) (star b) =
      (leftMul (B := B) b).adjointOperator
    exact (leftMul_adjointOperator b).symm

@[simp]
theorem leftRegular_apply (b x : B) :
    leftRegular (B := B) b x = b * x :=
  rfl

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra has a star-compatible
partial order.

The left multiplication representation of B on its right coefficient self-module is injective.
-/
theorem leftRegular_injective :
    Function.Injective (leftRegular (B := B)) := by
  intro b c hbc
  have happ := congrArg
    (fun T : End B B ↦ T (star (b - c))) hbc
  have hzero : (b - c) * star (b - c) = 0 := by
    change b * star (b - c) = c * star (b - c) at happ
    rw [sub_mul, happ, sub_self]
  exact sub_eq_zero.mp (mul_star_self_eq_zero.mp hzero)

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra has a star-compatible
partial order.

On the right coefficient self-module B, the rank-one operator determined by x and y is left
multiplication by x star(y).
-/
theorem rankOne_self_eq_leftMul (x y : B) :
    rankOne (B := B) x y = leftMul (B := B) (x * star y) := by
  ext z
  simp [CStarModule.Right.rightInner_self,
    mul_assoc]

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra has a star-compatible
partial order.

Left multiplication by every b ∈ B is a compact endomorphism of the right coefficient
self-module B.
-/
theorem leftMul_mem_compact (b : B) :
    leftMul (B := B) b ∈
      compactSubmodule (B := B) (E := B) (F := B) := by
  let _ : PartialOrder B := CStarAlgebra.spectralOrder B
  let _ : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  have hmul : Tendsto (fun u : B ↦ b * u)
      (CStarAlgebra.approximateUnit B) (nhds b) :=
    (CStarAlgebra.increasingApproximateUnit (A := B)).tendsto_mul_left b
  have hcoef : Tendsto (fun u : B ↦ b * star u)
      (CStarAlgebra.approximateUnit B) (nhds b) := by
    apply hmul.congr'
    filter_upwards
      [(CStarAlgebra.increasingApproximateUnit
        (A := B)).eventually_star_eq] with u hu
    rw [hu]
  have hleft : Tendsto
      (fun u : B ↦ leftRegular (B := B) (b * star u))
      (CStarAlgebra.approximateUnit B)
      (nhds (leftMul (B := B) b)) :=
    ((map_continuous (leftRegular (B := B))).tendsto b).comp hcoef
  have hrank : Tendsto (fun u : B ↦ rankOne (B := B) b u)
      (CStarAlgebra.approximateUnit B)
      (nhds (leftMul (B := B) b)) := by
    apply hleft.congr'
    exact Eventually.of_forall fun u ↦ (rankOne_self_eq_leftMul b u).symm
  change leftMul (B := B) b ∈ closure
    (finiteRankSubmodule (B := B) (E := B) (F := B) : Set (End B B))
  exact mem_closure_of_tendsto hrank <|
    Eventually.of_forall fun u ↦ rankOne_mem_finiteRank b u

private def leftRegularLinearMap : B →ₗ[ℂ] End B B where
  toFun := leftRegular (B := B)
  map_add' := map_add (leftRegular (B := B))
  map_smul' := map_smul (leftRegular (B := B))

private noncomputable def leftRegularRangeSubmodule :
    Submodule ℂ (End B B) :=
  LinearMap.range (leftRegularLinearMap (B := B))

private theorem finiteRank_le_leftRegularRange :
    finiteRankSubmodule (B := B) (E := B) (F := B) ≤
      leftRegularRangeSubmodule (B := B) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨x, y⟩, rfl⟩
  exact ⟨x * star y, (rankOne_self_eq_leftMul x y).symm⟩

private theorem isClosed_leftRegularRange :
    IsClosed (leftRegularRangeSubmodule (B := B) : Set (End B B)) := by
  have hset : (leftRegularRangeSubmodule (B := B) : Set (End B B)) =
      Set.range (leftRegular (B := B)) := by
    ext T
    constructor
    · intro hT
      change T ∈ LinearMap.range (leftRegularLinearMap (B := B)) at hT
      obtain ⟨b, hb⟩ := hT
      exact ⟨b, hb⟩
    · rintro ⟨b, hb⟩
      change T ∈ LinearMap.range (leftRegularLinearMap (B := B))
      exact ⟨b, hb⟩
  rw [hset]
  exact NonUnitalStarAlgHom.isClosed_range (leftRegular (B := B))

private theorem compact_le_leftRegularRange :
    compactSubmodule (B := B) (E := B) (F := B) ≤
      leftRegularRangeSubmodule (B := B) :=
  (finiteRankSubmodule (B := B) (E := B) (F := B)).topologicalClosure_minimal
    finiteRank_le_leftRegularRange isClosed_leftRegularRange

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra has a star-compatible
partial order.

Left multiplication gives a nonunital complex star homomorphism from B to the compact
endomorphisms of its right coefficient self-module.
-/
noncomputable def leftRegularCompact :
    B →⋆ₙₐ[ℂ] compactStarSubalgebra (B := B) (E := B) :=
  NonUnitalStarAlgHom.codRestrict (leftRegular (B := B))
    (compactStarSubalgebra (B := B) (E := B)) fun b ↦ by
      change leftMul (B := B) b ∈
        compactSubmodule (B := B) (E := B) (F := B)
      exact leftMul_mem_compact b

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra has a star-compatible
partial order.

Left multiplication gives a bijection from B onto the compact endomorphisms of its right
coefficient self-module.
-/
theorem leftRegularCompact_bijective :
    Function.Bijective (leftRegularCompact (B := B)) := by
  constructor
  · exact (NonUnitalStarAlgHom.injective_codRestrict _ _ _).2
      leftRegular_injective
  · intro T
    obtain ⟨b, hb⟩ := compact_le_leftRegularRange T.property
    exact ⟨b, Subtype.ext hb⟩

end Self

section SelfUnital

variable {B : Type uB} [CStarAlgebra B]
variable [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]

/-- The canonical right self-module dictionary for the unital coefficient algebra. -/
local instance : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule

/--
Let B be a unital complex C*-algebra whose opposite algebra has a star-compatible partial order.

Every adjointable endomorphism of the right coefficient self-module B is left multiplication by
an element of B.
-/
theorem leftRegular_surjective :
    Function.Surjective (leftRegular (B := B)) := by
  intro T
  refine ⟨T 1, ?_⟩
  apply AdjointableOperator.ext
  intro x
  simpa [CStarModule.Right.right_smul_self] using
    (T.map_right_smul (1 : B) x).symm

/--
Let B be a unital complex C*-algebra whose opposite algebra has a star-compatible partial order.

Left multiplication is a bijection from B onto all adjointable endomorphisms of its right
coefficient self-module.
-/
theorem leftRegular_bijective :
    Function.Bijective (leftRegular (B := B)) :=
  ⟨leftRegular_injective, leftRegular_surjective⟩

end SelfUnital

end AdjointableOperator

end CStarModule
