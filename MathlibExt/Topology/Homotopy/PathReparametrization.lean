/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.Path
public import Mathlib.Topology.Homotopy.Basic

/-!
# Continuous reparameterization of a full path space

An endpoint-preserving continuous interval map acts on the whole compact-open
space of paths between any two points. The affine parameter
`Set.Icc.convexComb (r t) t s` gives a jointly continuous homotopy from that
reparameterization to the identity.

The two constructions are the generic implementation extracted from
`LoopBasepointChange`. They retain arbitrary path endpoints and use the
existing interval combination, continuity and endpoint lemmas directly.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open unitInterval
open scoped Topology ContinuousMap

universe u

namespace ContinuousMap

variable {X : Type u} [TopologicalSpace X]

/-- Reparameterize every path between the specified endpoints continuously. -/
def pathReparamMap {a b : X} (r : I → I) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1) : C(Path a b, Path a b) where
  toFun q := q.reparam r hr hr0 hr1
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact continuous_eval.comp
      (continuous_fst.prodMk (hr.comp continuous_snd))

/-- The shared action evaluates the original path at the specified parameter. -/
@[simp]
theorem pathReparamMap_apply {a b : X} (r : I → I) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1) (q : Path a b) (t : I) :
    pathReparamMap r hr hr0 hr1 q t = q (r t) := rfl

/-- The original affine reparameterization family is a jointly continuous
homotopy to the identity on the entire path space. -/
def pathReparamMapHomotopy {a b : X} (r : I → I)
    (hr : Continuous r) (hr0 : r 0 = 0) (hr1 : r 1 = 1) :
    (pathReparamMap r hr hr0 hr1).Homotopy
      (ContinuousMap.id (Path a b)) where
  toFun sq := sq.2.reparam
    (fun t => Set.Icc.convexComb (r t) t sq.1)
    (Set.Icc.continuous_convexComb_prod.comp
      (hr.prodMk (continuous_id.prodMk continuous_const)))
    (by simp only [hr0, Set.Icc.convexComb_eq])
    (by simp only [hr1, Set.Icc.convexComb_eq])
  map_zero_left q := by
    apply Path.ext
    funext t
    change q (Set.Icc.convexComb (r t) t 0) = q (r t)
    rw [Set.Icc.convexComb_zero]
  map_one_left q := by
    apply Path.ext
    funext t
    change q (Set.Icc.convexComb (r t) t 1) = q t
    rw [Set.Icc.convexComb_one]
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact continuous_eval.comp
      ((continuous_snd.comp continuous_fst).prodMk
        (Set.Icc.continuous_convexComb_prod.comp
          ((hr.comp continuous_snd).prodMk
            (continuous_snd.prodMk (continuous_fst.comp continuous_fst)))))

/-- Every time of the shared homotopy has the advertised affine path value. -/
@[simp]
theorem pathReparamMapHomotopy_apply {a b : X} (r : I → I) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1) (q : Path a b) (s t : I) :
    pathReparamMapHomotopy r hr hr0 hr1 (s, q) t =
      q (Set.Icc.convexComb (r t) t s) := rfl

end ContinuousMap

end
