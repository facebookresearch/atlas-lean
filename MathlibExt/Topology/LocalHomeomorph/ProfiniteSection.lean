/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Separation.DisjointCover

/-!
# Continuous right inverses of local homeomorphisms over profinite spaces

A surjective local homeomorphism `f : E → X` has a continuous right inverse when `X` is compact,
Hausdorff and totally disconnected.

Local inverses glue along a finite disjoint clopen refinement. The source `E` is an arbitrary
topological space; no compactness or separation of `E` is required.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set Topology

universe u v

namespace IsLocalHomeomorph

/-- **Continuous section of a surjective local homeomorphism over a profinite space.** Let `E`
be any topological space, `X` compact Hausdorff and totally disconnected, and `f : E → X`
a surjective local homeomorphism. There exists `s∈C(X,E)` with `f∘s=id_X`; no compactness
or Hausdorff assumption on `E` is imposed. -/
theorem exists_continuous_rightInverse_of_profinite
    {E : Type u} {X : Type v}
    [TopologicalSpace E] [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    {f : E → X} (hf : IsLocalHomeomorph f)
    (hsurj : Function.Surjective f) :
    ∃ s : C(X, E), Function.RightInverse s f := by
  choose e he using hsurj
  let U : X → TopologicalSpace.Opens X := fun x =>
    ⟨(hf.localInverseAt (e x)).source,
      (hf.localInverseAt (e x)).open_source⟩
  have hU : TopologicalSpace.IsOpenCover U :=
    TopologicalSpace.IsOpenCover.of_sets
      (fun x => (hf.localInverseAt (e x)).open_source) (by
        ext x
        simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
        refine ⟨x, ?_⟩
        simpa only [he x] using
          (hf.apply_self_mem_localInverseAt_source (x := e x)))
  obtain ⟨n, W, hWdata, hWcover, hWdisj⟩ :=
    hU.exists_finite_nonempty_disjoint_clopen_cover
  choose i hi using fun j => (hWdata j).2
  have hmem (x : X) : ∃ j : Fin n, x ∈ (W j : Set X) := by
    simpa only [Set.mem_iUnion] using hWcover (Set.mem_univ x)
  let pick : X → Fin n := fun x => Classical.choose (hmem x)
  have pick_mem (x : X) : x ∈ (W (pick x) : Set X) :=
    Classical.choose_spec (hmem x)
  have pick_eq_of_mem (x : X) (j : Fin n)
      (hx : x ∈ (W j : Set X)) : pick x = j := by
    by_contra hne
    have hd := hWdisj hne
    exact Set.disjoint_left.1
      (show Disjoint (W (pick x) : Set X) (W j : Set X) from
        TopologicalSpace.Clopens.coe_disjoint.mpr hd)
      (pick_mem x) hx
  let s : X → E := fun x => hf.localInverseAt (e (i (pick x))) x
  have hscont : Continuous s := by
    rw [continuous_iff_continuousAt]
    intro x
    let j := pick x
    have hxW : x ∈ (W j : Set X) := pick_mem x
    have hWsource : (W j : Set X) ⊆
        (hf.localInverseAt (e (i j))).source := hi j
    have hxsource : x ∈ (hf.localInverseAt (e (i j))).source :=
      hWsource hxW
    have hlocal : ContinuousAt
        (fun y => hf.localInverseAt (e (i j)) y) x :=
      (hf.localInverseAt (e (i j))).continuousOn.continuousAt
        ((hf.localInverseAt (e (i j))).open_source.mem_nhds hxsource)
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [(W j).isOpen.mem_nhds hxW] with y hy
    change hf.localInverseAt (e (i (pick y))) y =
      hf.localInverseAt (e (i j)) y
    rw [show pick y = j from pick_eq_of_mem y j hy]
  refine ⟨⟨s, hscont⟩, ?_⟩
  intro x
  let j := pick x
  have hxW : x ∈ (W j : Set X) := pick_mem x
  have hxsource : x ∈ (hf.localInverseAt (e (i j))).source :=
    hi j hxW
  change f (hf.localInverseAt (e (i j)) x) = x
  exact hf.apply_localInverseAt_of_mem hxsource

end IsLocalHomeomorph

end
