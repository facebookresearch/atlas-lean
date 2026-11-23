/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.RootUnitContractionMap
public import MathlibExt.Topology.Homotopy.RootUnitEndpointTransports

/-!
# Mapping the actual roots with their endpoint transports

The original middle homotopy and the same joint contraction map the
actual roots and then carry their derived source, joining and target
equality casts. Every original time and whole loop value is retained.
-/

public section

noncomputable section

open unitInterval
open scoped Topology ContinuousMap

universe u v

namespace ContinuousMap

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {x y z : X} {a b c : Y}

private theorem actualMappedMiddleTransportComputed (f : C(X, Y))
    (p : Path x y) (q : Path y z) (ha : a = f x) (hb : b = f y) (hc : c = f z)
    (t : I) (gamma : LoopSpace X x) :
    ((loopBasepointChangeTransHomotopy p q (t, gamma)).map f.continuous).cast
        (x' := c) (y' := c) hc hc =
      loopBasepointChangeTransHomotopy
        ((p.map f.continuous).cast (x' := a) (y' := b) ha hb)
        ((q.map f.continuous).cast (x' := b) (y' := c) hb hc)
        (t, (gamma.map f.continuous).cast (x' := a) (y' := a) ha ha) :=
  (congrArg (fun r : LoopSpace Y (f z) => r.cast (x' := c) (y' := c) hc hc)
    (loopBasepointChangeTransHomotopy_map f p q t gamma)).trans
      (loopBasepointChangeTransHomotopy_cast (p.map f.continuous)
        (q.map f.continuous) ha hb hc t (gamma.map f.continuous))

/-- Mapping the actual whole middle value and transporting all three
root endpoints retains the same original middle homotopy and clocks. -/
theorem loopBasepointChangeTransHomotopy_mappedRoots_cast (f : C(X, Y))
    (p : Path x y) (q : Path y z) (ha : a = f x) (hb : b = f y) (hc : c = f z)
    (t : I) (gamma : LoopSpace X x) :
    ((loopBasepointChangeTransHomotopy p q (t, gamma)).map f.continuous).cast
        (x' := c) (y' := c) hc hc =
      loopBasepointChangeTransHomotopy
        ((p.map f.continuous).cast (x' := a) (y' := b) ha hb)
        ((q.map f.continuous).cast (x' := b) (y' := c) hb hc)
        (t, (gamma.map f.continuous).cast (x' := a) (y' := a) ha ha) :=
  actualMappedMiddleTransportComputed f p q ha hb hc t gamma

private theorem actualMappedJointUnitTransportComputed (f : C(X, Y))
    (p : Path x y) (ha : a = f x) (hb : b = f y) (t : I) :
    ((rootUnitContraction (fun r : Path x y => r) continuous_eval (t, p)).map
      f.continuous).cast (x' := b) (y' := b) hb hb =
      rootUnitContraction (fun r : Path a b => r) continuous_eval
        (t, (p.map f.continuous).cast (x' := a) (y' := b) ha hb) := by
  let A := Path x y
  let B := Path (f x) (f y)
  let topX : TopologicalSpace X := inferInstance
  let topY : TopologicalSpace Y := inferInstance
  let topA : TopologicalSpace A := inferInstance
  let topB : TopologicalSpace B := inferInstance
  let pFamily : ∀ r : A, Path x y := fun r => r
  let hpFamily : Continuous (fun z : A × I => pFamily z.1 z.2) := continuous_eval
  let mappedFamily : ∀ r : A, Path (f x) (f y) :=
    fun r => r.map (f := fun z : X => f z) f.continuous
  let hm : Continuous (fun z : A × I => mappedFamily z.1 z.2) :=
    @rootUnitMappedFamily_continuous A X Y topA topX topY
      (fun _ : A => x) y pFamily hpFamily f
  have hMap := @rootUnitContraction_map A X Y topA topX topY
    (fun _ : A => x) y pFamily hpFamily f t p
  have hEval :
      @rootUnitContraction A Y topA topY (fun _ : A => f x) (f y)
        mappedFamily hm (t, p) =
      @rootUnitContraction B Y topB topY (fun _ : B => f x) (f y)
        (fun r : B => r) continuous_eval
          (t, p.map (f := fun z : X => f z) f.continuous) := by
    apply Path.ext
    funext s
    exact (@rootUnitContraction_apply A Y topA topY (fun _ : A => f x) (f y)
      mappedFamily hm t p s).trans
        (@rootUnitContraction_apply B Y topB topY (fun _ : B => f x) (f y)
          (fun r : B => r) continuous_eval t
            (p.map (f := fun z : X => f z) f.continuous) s).symm
  exact (congrArg (fun r : LoopSpace Y (f y) => r.cast (x' := b) (y' := b) hb hb)
    (hMap.trans hEval)).trans
      (rootUnitContraction_pathSpace_cast
        (p.map (f := fun z : X => f z) f.continuous) ha hb t)

/-- Every mapped whole-loop value of the same joint contraction carries
the original root endpoint casts and retains the same time coordinate. -/
theorem rootUnitContraction_mappedPath_cast (f : C(X, Y))
    (p : Path x y) (ha : a = f x) (hb : b = f y) (t : I) :
    ((rootUnitContraction (fun r : Path x y => r) continuous_eval (t, p)).map
      f.continuous).cast (x' := b) (y' := b) hb hb =
      rootUnitContraction (fun r : Path a b => r) continuous_eval
        (t, (p.map f.continuous).cast (x' := a) (y' := b) ha hb) :=
  actualMappedJointUnitTransportComputed f p ha hb t

end ContinuousMap

end
