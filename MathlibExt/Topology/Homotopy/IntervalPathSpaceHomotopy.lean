/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Topology.Homotopy.Path

/-!
# Original interval path-space root comparison

Pointwise interval convex combination gives a fixed-endpoint homotopy
between two paths in an original interval path space. All three original
parameters are retained. For original loop-root comparisons the interval
path space is the ordinary loop carrier at an interval endpoint.
-/

public section

noncomputable section

open unitInterval
open scoped ContinuousMap

namespace Path

private def originalIntervalPathSpaceHomotopyComputed
    {a b : ℝ} {x y : Set.Icc a b} {p q : Path x y} (P Q : Path p q) :
    P.Homotopy Q where
  toFun z :=
    { toFun := fun s => Set.Icc.convexComb (P z.2 s) (Q z.2 s) z.1
      continuous_toFun := Set.Icc.continuous_convexComb_prod.comp
        ((P z.2).continuous.prodMk ((Q z.2).continuous.prodMk continuous_const))
      source' := by
        rw [(P z.2).source, (Q z.2).source, Set.Icc.convexComb_eq]
      target' := by
        rw [(P z.2).target, (Q z.2).target, Set.Icc.convexComb_eq] }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (I × I) × I =>
      Set.Icc.convexComb (P z.1.2 z.2) (Q z.1.2 z.2) z.1.1)
    have hP : Continuous (fun z : (I × I) × I => P z.1.2 z.2) :=
      continuous_eval.comp
        ((P.continuous.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd)
    have hQ : Continuous (fun z : (I × I) × I => Q z.1.2 z.2) :=
      continuous_eval.comp
        ((Q.continuous.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd)
    exact Set.Icc.continuous_convexComb_prod.comp
      (hP.prodMk (hQ.prodMk (continuous_fst.comp continuous_fst)))
  map_zero_left r := by
    apply Path.ext
    funext s
    exact Set.Icc.convexComb_zero (P r s) (Q r s)
  map_one_left r := by
    apply Path.ext
    funext s
    exact Set.Icc.convexComb_one (P r s) (Q r s)
  prop' t r hr := by
    rcases hr with rfl | rfl
    · apply Path.ext
      funext s
      change Set.Icc.convexComb (P 0 s) (Q 0 s) t = P 0 s
      rw [P.source, Q.source, Set.Icc.convexComb_eq]
    · apply Path.ext
      funext s
      change Set.Icc.convexComb (P 1 s) (Q 1 s) t = P 1 s
      rw [P.target, Q.target, Set.Icc.convexComb_eq]

/-- ONE continuous fixed-endpoint homotopy of the two original paths in
an original interval path space, with every coordinate left free. -/
def intervalPathSpaceHomotopy
    {a b : ℝ} {x y : Set.Icc a b} {p q : Path x y} (P Q : Path p q) :
    P.Homotopy Q := originalIntervalPathSpaceHomotopyComputed P Q

private theorem originalIntervalPathSpaceHomotopyValueComputed
    {a b : ℝ} {x y : Set.Icc a b} {p q : Path x y} (P Q : Path p q)
    (t r s : I) :
    intervalPathSpaceHomotopy P Q (t, r) s =
      Set.Icc.convexComb (P r s) (Q r s) t := rfl

/-- ALL THREE original coordinates of the root comparison are the actual
pointwise interval convex-combination coordinates. -/
theorem intervalPathSpaceHomotopy_apply
    {a b : ℝ} {x y : Set.Icc a b} {p q : Path x y} (P Q : Path p q)
    (t r s : I) :
    intervalPathSpaceHomotopy P Q (t, r) s =
      Set.Icc.convexComb (P r s) (Q r s) t :=
  originalIntervalPathSpaceHomotopyValueComputed P Q t r s

end Path

end
