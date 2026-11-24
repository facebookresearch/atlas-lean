/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Algebra.ContinuousSMulDiscrete
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Instances.Real.Lemmas

-- `exactSource` consumer with the original binders: the class is built
-- directly from openness of every fibre.
example {G M : Type*} [TopologicalSpace G] [SMul G M]
    (h : ∀ x y : M, IsOpen {g : G | g • x = y}) : ContinuousSMulDiscrete G M :=
  ⟨h⟩

-- The fibre condition is recovered from the class.
example {G M : Type*} [TopologicalSpace G] [SMul G M] [ContinuousSMulDiscrete G M]
    (x y : M) : IsOpen {g : G | g • x = y} :=
  ContinuousSMulDiscrete.isOpen_smul_eq G x y

-- With a discrete topology on the target, the class gives joint continuity.
example {G M : Type*} [TopologicalSpace G] [SMul G M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMulDiscrete G M] : ContinuousSMul G M :=
  inferInstance

-- Joint continuity conversely gives the class.
example {G M : Type*} [TopologicalSpace G] [SMul G M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul G M] : ContinuousSMulDiscrete G M :=
  ContinuousSMulDiscrete.of_continuousSMul

-- Stabilizers are open for a group action satisfying the class.
example {G M : Type*} [TopologicalSpace G] [Group G] [MulAction G M]
    [ContinuousSMulDiscrete G M] (x : M) :
    IsOpen (MulAction.stabilizer G x : Set G) :=
  ContinuousSMulDiscrete.isOpen_stabilizer G x

-- The stabilizer characterization also constructs the class.
example {G M : Type*} [TopologicalSpace G] [Group G] [ContinuousMul G]
    [MulAction G M] (h : ∀ x : M, IsOpen (MulAction.stabilizer G x : Set G)) :
    ContinuousSMulDiscrete G M :=
  continuousSMulDiscrete_iff_isOpen_stabilizer.mpr h

-- Higher-universe consumer: the same statement over `Type 1` types.
example {G M : Type 1} [TopologicalSpace G] [SMul G M] [TopologicalSpace M]
    [DiscreteTopology M] : ContinuousSMulDiscrete G M ↔ ContinuousSMul G M :=
  continuousSMulDiscrete_iff

-- Boundary example: a discrete acting space satisfies the fibre condition
-- for any action, since every subset of a discrete space is open.
example : ContinuousSMulDiscrete (Fin 2) (Fin 2) := by
  refine ⟨fun x y ↦ ?_⟩
  exact isOpen_discrete _
