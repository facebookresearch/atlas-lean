/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.P3Domain

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.P3Domain`

* `shb_P3_support_iff_domainResummation` for `H = G`: the support `ρ` is monotone in the trivial
  inclusion, so `shb_P3DomainResummation G G le_rfl β J p` holds (the predicate is satisfiable);
* `shb_P3_support_of_domainResummation` and `shb_P3_support_of_fiber_partition_bounds` applied.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.P3Domain

open _root_.StatMech.Sharpness

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _

/-- Mapping a walk along `G ≤ G` is the identity. -/
theorem walk_mapLe_refl {V : Type*} (G : SimpleGraph V) {x y : V} (w : G.Walk x y) :
    w.mapLe (le_refl G) = w := by
  induction w with
  | nil => rfl
  | cons h p ih => simpa [SimpleGraph.Walk.mapLe] using ih

-- The domain resummation holds for the trivial inclusion.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : SimpleGraph V) (β : ℝ)
    (J : Sym2 V → ℝ) (x y : V) (p : G.Path x y) : shb_P3DomainResummation G G le_rfl β J p :=
  (shb_P3_support_iff_domainResummation G G le_rfl β J p).mp <| by
    have h : shb_pathMapLe (le_refl G) p = p := Subtype.ext (walk_mapLe_refl G p.1)
    rw [h]

-- P3 from the domain resummation.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (H G : SimpleGraph V)
    (hHG : H ≤ G) (β : ℝ) (J : Sym2 V → ℝ) (x y : V) (p : H.Path x y)
    (h : shb_P3DomainResummation H G hHG β J p) :
    shb_rhoSupport G β J x y (shb_pathMapLe hHG p) ≤ shb_rhoSupport H β J x y p :=
  shb_P3_support_of_domainResummation H G hHG β J p h

-- P3 from fiber and partition-function bounds.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (H G : SimpleGraph V)
    (hHG : H ≤ G) (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (x y : V)
    (p : H.Path x y) (c : ℝ)
    (hnum : shb_backboneNumSupport G β J x y (shb_pathMapLe hHG p) ≤
      c * shb_backboneNumSupport H β J x y p)
    (hZ : c * currentSum H β J ∅ ≤ currentSum G β J ∅) :
    shb_rhoSupport G β J x y (shb_pathMapLe hHG p) ≤ shb_rhoSupport H β J x y p :=
  shb_P3_support_of_fiber_partition_bounds H G hHG β J hβ hJ p c hnum hZ

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.P3Domain
