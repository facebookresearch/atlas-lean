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

public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Components of a loop space

The path components of the loop space at `x` are canonically equivalent to
the fundamental group at `x`.  Both quotients have loops as representatives:
a path between loops is the same as an endpoint-fixed homotopy after
uncurrying, and conversely an endpoint-fixed homotopy curries to a path in
the loop space.

This file only constructs the underlying equivalence and its representative
computation.  It installs no group structure on path components and makes no
realization, model-category, or K-theory claim.
-/

@[expose] public section

noncomputable section

open scoped unitInterval

universe u

variable {X : Type u} [TopologicalSpace X] {x : X}

/-- The path components of the loop space at `x` are canonically equivalent
to the fundamental group at `x`. -/
noncomputable def loopComponentsEquivFundamentalGroup (X : Type u)
    [TopologicalSpace X] (x : X) :
    ZerothHomotopy (LoopSpace X x) ≃ FundamentalGroup X x := by
  refine Equiv.trans ?_ CategoryTheory.End.homEquiv.symm
  exact Quotient.congr (Equiv.refl (LoopSpace X x))
    (by
      intro p q
      constructor
      · rintro ⟨r⟩
        refine ⟨{
          toFun := fun t => r t.1 t.2
          continuous_toFun := by
            exact Path.continuous_uncurry_iff.mpr r.continuous
          map_zero_left := fun t => congrArg (fun s : Path x x => s t) r.source
          map_one_left := fun t => congrArg (fun s : Path x x => s t) r.target
          prop' := ?_ }⟩
        intro t y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact (r t).source.trans p.source.symm
        · exact (r t).target.trans p.target.symm
      · rintro ⟨H⟩
        refine ⟨{
          toFun := fun t => H.eval t
          continuous_toFun := ?_
          source' := H.eval_zero
          target' := H.eval_one }⟩
        apply Path.continuous_uncurry_iff.mp
        exact H.continuous)

/-- The loop-component equivalence sends the component of a loop to its
endpoint-fixed homotopy class. -/
@[simp]
theorem loopComponentsEquivFundamentalGroup_mk (p : LoopSpace X x) :
    loopComponentsEquivFundamentalGroup X x (ZerothHomotopy.mk p) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) :=
  rfl

end
