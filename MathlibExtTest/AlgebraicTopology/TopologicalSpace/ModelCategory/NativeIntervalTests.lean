/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.NativeInterval
public import Batteries.Tactic.Lint
import Lean

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Simplicial

namespace MathlibExtTest.NativeInterval

open PointedCGWH.IntervalCoefficient

example : SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) ≅ CGWH.point.{u, v} :=
  zeroSimplexIsoPoint

example : (𝟙_ PointedCGWH.{u, v}) ⟶ interval.{u, v} := endpoint 0

example : (𝟙_ PointedCGWH.{u, v}) ⟶ interval.{u, v} := endpoint 1

example : interval.{u, v} ⟶ (𝟙_ PointedCGWH.{u, v}) := augmentation

example : endpoint.{u, v} 0 ≫ augmentation = 𝟙 (𝟙_ PointedCGWH.{u, v}) :=
  endpoint_augmentation 0

example : endpoint.{u, v} 1 ≫ augmentation = 𝟙 (𝟙_ PointedCGWH.{u, v}) :=
  endpoint_augmentation 1

example (F : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v})
    [F.IsWellOrderContinuous]
    (hF : ∀ ⦃a b⦄ (φ : a ⟶ b),
      Topology.IsClosedEmbedding (ConcreteCategory.hom (F.map φ).right)) :
    PreservesColimit F (coyoneda.obj (Opposite.op interval.{u, v})) :=
  source_preservesClosedColimit F hF

#print axioms PointedCGWH.IntervalCoefficient.zeroSimplexIsoPoint
#print axioms PointedCGWH.IntervalCoefficient.interval
#print axioms PointedCGWH.IntervalCoefficient.endpoint
#print axioms PointedCGWH.IntervalCoefficient.augmentation
#print axioms PointedCGWH.IntervalCoefficient.endpoint_eq
#print axioms PointedCGWH.IntervalCoefficient.augmentation_eq
#print axioms PointedCGWH.IntervalCoefficient.endpoint_augmentation
#print axioms PointedCGWH.IntervalCoefficient.source_preservesClosedColimit

/-- The exact eight public roots of the actual native interval producer. -/
def expectedProducerRoots : Array Lean.Name := #[
  `PointedCGWH.IntervalCoefficient.zeroSimplexIsoPoint,
  `PointedCGWH.IntervalCoefficient.interval,
  `PointedCGWH.IntervalCoefficient.endpoint,
  `PointedCGWH.IntervalCoefficient.augmentation,
  `PointedCGWH.IntervalCoefficient.endpoint_eq,
  `PointedCGWH.IntervalCoefficient.augmentation_eq,
  `PointedCGWH.IntervalCoefficient.endpoint_augmentation,
  `PointedCGWH.IntervalCoefficient.source_preservesClosedColimit
]

run_cmd do
  let env ← Lean.getEnv
  let producer := `MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.NativeInterval
  let roots := expectedProducerRoots
  let idx ← match env.getModuleIdx? producer with
    | some idx => pure idx
    | none => throwError "producer module absent: {producer}"
  let mut count : Nat := 0
  for (name, _) in env.constants do
    if env.getModuleIdxFor? name == some idx then count := count + 1
  unless count > 0 do throwError "zero producer declarations: {producer}"
  for root in roots do
    unless (env.find? root).isSome do throwError "public root absent: {root}"
    unless env.getModuleIdxFor? root == some idx do
      throwError "public root has wrong defining module: {root}"
    Lean.logInfo m!"SOURCE_ROOT_MODULE {producer} {root}"
  Lean.logInfo m!"SOURCE_MODULE_COUNT {producer} {count} EXPECTED_ROOTS {roots.size}"

#lint only unusedArguments in MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.NativeInterval

end MathlibExtTest.NativeInterval
