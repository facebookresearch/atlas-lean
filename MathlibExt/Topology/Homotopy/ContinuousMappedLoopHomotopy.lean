/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.WeaklyPointedHomotopyRel

/-!
# Jointly continuous transport of all based loops through a relative homotopy

The existing relative homotopy of maps gives one continuous family over
both homotopy time and the entire based loop space. Its values are the
original pointwise mapped-loop homotopies, with the actual endpoint cast.
This constructs the continuous family explicitly; a collection of separate
path-homotopy witnesses is not an input.
-/

public section

open scoped Topology

universe u v

namespace ContinuousMap.HomotopyRel

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {f g : C(X, Y)}

/-- All mapped based loops, continuously parameterized by the same original
relative homotopy and by the whole source loop space. -/
def mappedLoopFamily (H : ContinuousMap.HomotopyRel f g {x}) :
    C(unitInterval × LoopSpace X x, LoopSpace Y (f x)) where
  toFun p :=
    { toFun := fun s => H (p.1, p.2 s)
      continuous_toFun :=
        H.continuous.comp (continuous_const.prodMk p.2.continuous)
      source' := by
        rw [p.2.source]
        exact H.eq_fst p.1 (by simp)
      target' := by
        rw [p.2.target]
        exact H.eq_fst p.1 (by simp) }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun q : (unitInterval × LoopSpace X x) × unitInterval =>
      H (q.1.1, q.1.2 q.2))
    exact H.continuous.comp
      ((continuous_fst.comp continuous_fst).prodMk
        (continuous_eval.comp
          ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))

/-- The first endpoint is the original loop mapped through the first map. -/
theorem mappedLoopFamily_zero (H : ContinuousMap.HomotopyRel f g {x})
    (gamma : LoopSpace X x) :
    mappedLoopFamily H (0, gamma) = gamma.map f.continuous := by
  apply Path.ext
  funext s
  exact H.map_zero_left (gamma s)

/-- The second endpoint is the original loop mapped through the second map,
cast along the equality of the two maps at the fixed source point. -/
theorem mappedLoopFamily_one (H : ContinuousMap.HomotopyRel f g {x})
    (gamma : LoopSpace X x) :
    mappedLoopFamily H (1, gamma) =
      (gamma.map g.continuous).cast
        (H.fst_eq_snd (by simp)) (H.fst_eq_snd (by simp)) := by
  apply Path.ext
  funext s
  exact H.map_one_left (gamma s)

/-- The actual joint family, bundled as a homotopy of its two continuous
endpoint maps on the whole source loop space. -/
def mappedLoopFamilyHomotopy (H : ContinuousMap.HomotopyRel f g {x}) :
    ContinuousMap.Homotopy
      ((mappedLoopFamily H).comp
        ⟨fun gamma => ((0 : unitInterval), gamma),
          continuous_const.prodMk continuous_id⟩)
      ((mappedLoopFamily H).comp
        ⟨fun gamma => ((1 : unitInterval), gamma),
          continuous_const.prodMk continuous_id⟩) where
  toContinuousMap := mappedLoopFamily H
  map_zero_left _ := rfl
  map_one_left _ := rfl

end ContinuousMap.HomotopyRel

namespace ContinuousMap.HomotopyRel

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {f g : C(X, Y)}

private theorem mappedLoopFamily_apply_computed (H : ContinuousMap.HomotopyRel f g {x})
    (t : unitInterval) (γ : LoopSpace X x) (s : unitInterval) :
    (mappedLoopFamily H (t, γ)) s = H (t, γ s) := rfl

/-- Every time and whole input loop of the same joint family retain the original relative homotopy value. -/
theorem mappedLoopFamily_apply (H : ContinuousMap.HomotopyRel f g {x})
    (t : unitInterval) (γ : LoopSpace X x) (s : unitInterval) :
    (mappedLoopFamily H (t, γ)) s = H (t, γ s) :=
  mappedLoopFamily_apply_computed H t γ s

end ContinuousMap.HomotopyRel
