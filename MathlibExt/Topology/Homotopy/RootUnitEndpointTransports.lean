/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.RootUnitContraction

/-!
# Original middle and joint-unit endpoint transports

The actual middle homotopy and the same joint contraction respect the
source, joining-point and target equality casts of the original roots.
Only endpoint proofs are transported; their original values and clocks
remain unchanged at every time.
-/

public section

noncomputable section

open unitInterval
open scoped Topology

universe u

namespace ContinuousMap

variable {Y : Type u} [TopologicalSpace Y]
  {a b c a' b' c' : Y}

private theorem actualMiddleEndpointTransportComputed
    (p : Path a b) (q : Path b c) (ha : a' = a) (hb : b' = b) (hc : c' = c)
    (t : I) (gamma : LoopSpace Y a) :
    (loopBasepointChangeTransHomotopy p q (t, gamma)).cast
        (x' := c') (y' := c') hc hc =
      loopBasepointChangeTransHomotopy
        (p.cast (x' := a') (y' := b') ha hb) (q.cast (x' := b') (y' := c') hb hc)
        (t, gamma.cast (x' := a') (y' := a') ha ha) := by
  cases ha
  cases hb
  cases hc
  rfl

/-- The actual original middle value transports the same source,
joining-point and target casts without altering its original clock branches. -/
theorem loopBasepointChangeTransHomotopy_cast
    (p : Path a b) (q : Path b c) (ha : a' = a) (hb : b' = b) (hc : c' = c)
    (t : I) (gamma : LoopSpace Y a) :
    (loopBasepointChangeTransHomotopy p q (t, gamma)).cast
        (x' := c') (y' := c') hc hc =
      loopBasepointChangeTransHomotopy
        (p.cast (x' := a') (y' := b') ha hb) (q.cast (x' := b') (y' := c') hb hc)
        (t, gamma.cast (x' := a') (y' := a') ha ha) :=
  actualMiddleEndpointTransportComputed p q ha hb hc t gamma

private theorem actualJointUnitEndpointTransportComputed
    (p : Path a b) (ha : a' = a) (hb : b' = b) (t : I) :
    (rootUnitContraction (fun r : Path a b => r) continuous_eval (t, p)).cast
        (x' := b') (y' := b') hb hb =
      rootUnitContraction (fun r : Path a' b' => r) continuous_eval
        (t, p.cast (x' := a') (y' := b') ha hb) := by
  cases ha
  cases hb
  rfl

/-- Every whole loop of the same path-space joint contraction respects
the original root endpoint casts, retaining both actual time coordinates. -/
theorem rootUnitContraction_pathSpace_cast
    (p : Path a b) (ha : a' = a) (hb : b' = b) (t : I) :
    (rootUnitContraction (fun r : Path a b => r) continuous_eval (t, p)).cast
        (x' := b') (y' := b') hb hb =
      rootUnitContraction (fun r : Path a' b' => r) continuous_eval
        (t, p.cast (x' := a') (y' := b') ha hb) :=
  actualJointUnitEndpointTransportComputed p ha hb t

end ContinuousMap

end
