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

public import Mathlib.Topology.ContinuousMap.ZeroAtInftyUnitization
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import MathlibExt.Topology.Compactification.OnePoint.SecondCountable
public import Mathlib.Topology.MetricSpace.Isometry

import Mathlib.Topology.UniformSpace.Cauchy

/-!
# One-point extension and separability of C0 functions

On an R1 topological domain `X`, extending a function vanishing at infinity
by zero to the one-point compactification preserves its uniform distance.
The target may be a pseudometric space with zero. For a normed additive
target this gives equality of the original supremum norms, including an
empty original domain; no target completeness is required.

If `X` is locally compact, Hausdorff and second-countable, and the target
is a separable pseudometric space with zero, then `C₀(X,E)` is separable
for its uniform pseudometric topology. Domain and target universes remain
independent, and an empty domain is permitted.
-/

@[expose] public section

open TopologicalSpace
open scoped ZeroAtInfty

universe uX uE

namespace ZeroAtInftyContinuousMap

variable {X : Type uX} {E : Type uE} [TopologicalSpace X] [R1Space X]

/-- Zero extension to the one-point compactification preserves uniform distance for a pseudometric
target with zero.

`X` is R1 and `E` is a pseudometric space with zero, in independent universes.

```lean
theorem isometry_toOnePoint [PseudoMetricSpace E] [Zero E] :
    Isometry (toOnePoint : C₀(X, E) → C(OnePoint X, E))
``` -/
theorem isometry_toOnePoint [PseudoMetricSpace E] [Zero E] :
    Isometry (toOnePoint : C₀(X, E) → C(OnePoint X, E)) := by
  apply Isometry.of_dist_eq
  intro f g
  apply le_antisymm
  · apply (ContinuousMap.dist_le (dist_nonneg : 0 ≤ dist f g)).2
    intro x
    induction x using OnePoint.rec with
    | infty =>
        simpa only [toOnePoint_infty, dist_self] using (dist_nonneg : 0 ≤ dist f g)
    | coe x =>
        simpa only [toOnePoint_coe, toBCF_apply, dist_toBCF_eq_dist] using
          (BoundedContinuousFunction.dist_coe_le_dist (f := f.toBCF) (g := g.toBCF) x)
  · change dist f.toBCF g.toBCF ≤ dist f.toOnePoint g.toOnePoint
    apply (BoundedContinuousFunction.dist_le (dist_nonneg : 0 ≤ dist f.toOnePoint g.toOnePoint)).2
    intro x
    simpa only [toOnePoint_coe, toBCF_apply] using
      (ContinuousMap.dist_apply_le_dist (f := f.toOnePoint) (g := g.toOnePoint)
        (x : OnePoint X))

/-- Zero extension to the one-point compactification preserves the original C0 supremum norm.

`X` is R1 and `E` is a normed additive commutative group, in independent universes.

```lean
theorem norm_toOnePoint [NormedAddCommGroup E] (f : C₀(X, E)) :
    ‖f.toOnePoint‖ = ‖f‖
``` -/
theorem norm_toOnePoint [NormedAddCommGroup E] (f : C₀(X, E)) :
    ‖f.toOnePoint‖ = ‖f‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
    intro x
    induction x using OnePoint.rec with
    | infty => simpa only [toOnePoint_infty, norm_zero] using norm_nonneg f
    | coe x =>
        simpa only [toOnePoint_coe, toBCF_apply, norm_toBCF_eq_norm]
            using f.toBCF.norm_coe_le_norm x
  · change ‖f.toBCF‖ ≤ ‖f.toOnePoint‖
    apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).2
    intro x
    simpa only [toOnePoint_coe, toBCF_apply] using f.toOnePoint.norm_coe_le_norm (x : OnePoint X)

end ZeroAtInftyContinuousMap

namespace ZeroAtInftyContinuousMap

/-- C0 functions form a separable uniform pseudometric space when the domain is locally compact
Hausdorff second-countable and the target is separable pseudometric with zero.

```lean
theorem separableSpace (X : Type uX) (E : Type uE) [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [PseudoMetricSpace E] [Zero E] [SeparableSpace E] : SeparableSpace C₀(X, E)
``` -/
theorem separableSpace (X : Type uX) (E : Type uE) [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [PseudoMetricSpace E] [Zero E] [SeparableSpace E] : SeparableSpace C₀(X, E) := by
  let : SecondCountableTopology (OnePoint X) := OnePoint.secondCountableTopology X
  let : SecondCountableTopology E := UniformSpace.secondCountable_of_separable E
  let : SecondCountableTopology C₀(X, E) :=
    (isometry_toOnePoint (X := X) (E := E)).isUniformInducing.isInducing.secondCountableTopology
  infer_instance

end ZeroAtInftyContinuousMap
