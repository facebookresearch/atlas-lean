/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.HomotopyGroupLoopShift
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Positive homotopy groups from actual based inverse maps

The existing equality-aware homotopy-group map is invariant under a homotopy
fixed at the actual source basepoint. Two continuous maps with strict point
equations and both relative inverse homotopies therefore give a group
equivalence with those exact induced maps.

Projection from a product with a discrete factor also gives a group
equivalence at any chosen pair point. Its inverse is the actual section with
constant first coordinate. A positive-dimensional based cube has constant discrete
coordinate, so no connectedness assumption on the other factor is needed.
The spaces may have independent carrier universes.
-/

noncomputable section

open scoped unitInterval Topology Topology.Homotopy

universe u v

namespace HomotopyGroup

section BasedMaps

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- The equality-aware map postcomposes the actual cube representative,
with its original boundary equation transported to the target basepoint. -/
public theorem mapHomOfEq_mk (n : ℕ) (f : C(X, Y)) (hf : f x = y)
    (p : GenLoop (Fin (n + 1)) X x) :
    mapHomOfEq f hf n (mk p) =
      mk (⟨f.comp p.1,
        fun t ht => (congrArg f (GenLoop.boundary p t ht)).trans hf⟩ :
          GenLoop (Fin (n + 1)) Y y) := by
  subst y
  simp only [mapHomOfEq_apply, map_mk]
  rfl

/-- A whole homotopy fixed at the source basepoint gives the same map on
every positive homotopy group, using the specified target point equations. -/
public theorem mapHomOfEq_homotopyRel (n : ℕ) (f g : C(X, Y))
    (hf : f x = y) (hg : g x = y)
    (H : ContinuousMap.HomotopyRel f g {x}) :
    mapHomOfEq f hf n = mapHomOfEq g hg n := by
  ext a
  obtain ⟨p, rfl⟩ := mk_surjective a
  rw [mapHomOfEq_mk, mapHomOfEq_mk]
  apply Quotient.sound
  refine ⟨{ toHomotopy := H.toHomotopy.compContinuousMap p.1, prop' := ?_ }⟩
  intro t s hs
  have hpoint : p s ∈ ({x} : Set X) :=
    Set.mem_singleton_iff.mpr (GenLoop.boundary p s hs)
  exact H.eq_fst t hpoint

/-- Actual based inverse maps and both whole relative inverse families
induce a group equivalence in every positive degree. -/
public def mulEquivOfBasedInverse (n : ℕ) (f : C(X, Y)) (g : C(Y, X))
    (hf : f x = y) (hg : g y = x)
    (L : ContinuousMap.HomotopyRel (g.comp f) (ContinuousMap.id X) {x})
    (R : ContinuousMap.HomotopyRel (f.comp g) (ContinuousMap.id Y) {y}) :
    Pi (n + 1) X x ≃* Pi (n + 1) Y y where
  toFun := mapHomOfEq f hf n
  invFun := mapHomOfEq g hg n
  left_inv a := by
    let hgf : (g.comp f) x = x := (congrArg g hf).trans hg
    have hSame : mapHomOfEq (x := x) (y := x) (g.comp f) hgf n =
        mapHomOfEq (x := x) (y := x) (ContinuousMap.id X) rfl n :=
      mapHomOfEq_homotopyRel (x := x) (y := x) n
        (g.comp f) (ContinuousMap.id X) hgf rfl L
    have h1 : mapHomOfEq (x := y) (y := x) g hg n
        (mapHomOfEq (x := x) (y := y) f hf n a) =
        mapHomOfEq (x := x) (y := x) (g.comp f) hgf n a :=
      (mapHomOfEq_comp (x := x) (y := y) (z := x) f g hf hg hgf n a).symm
    have h2 : mapHomOfEq (x := x) (y := x) (g.comp f) hgf n a =
        mapHomOfEq (x := x) (y := x) (ContinuousMap.id X) rfl n a :=
      DFunLike.congr_fun hSame a
    have h3 : mapHomOfEq (x := x) (y := x) (ContinuousMap.id X) rfl n a = a :=
      mapHomOfEq_id x n a
    exact h1.trans (h2.trans h3)
  right_inv a := by
    let hfg : (f.comp g) y = y := (congrArg f hg).trans hf
    have hSame : mapHomOfEq (x := y) (y := y) (f.comp g) hfg n =
        mapHomOfEq (x := y) (y := y) (ContinuousMap.id Y) rfl n :=
      mapHomOfEq_homotopyRel (x := y) (y := y) n
        (f.comp g) (ContinuousMap.id Y) hfg rfl R
    have h1 : mapHomOfEq (x := x) (y := y) f hf n
        (mapHomOfEq (x := y) (y := x) g hg n a) =
        mapHomOfEq (x := y) (y := y) (f.comp g) hfg n a :=
      (mapHomOfEq_comp (x := y) (y := x) (z := y) g f hg hf hfg n a).symm
    have h2 : mapHomOfEq (x := y) (y := y) (f.comp g) hfg n a =
        mapHomOfEq (x := y) (y := y) (ContinuousMap.id Y) rfl n a :=
      DFunLike.congr_fun hSame a
    have h3 : mapHomOfEq (x := y) (y := y) (ContinuousMap.id Y) rfl n a = a :=
      mapHomOfEq_id y n a
    exact h1.trans (h2.trans h3)
  map_mul' := (mapHomOfEq f hf n).map_mul

private theorem mulEquivOfBasedInverse_apply_computed (n : ℕ)
    (f : C(X, Y)) (g : C(Y, X)) (hf : f x = y) (hg : g y = x)
    (L : ContinuousMap.HomotopyRel (g.comp f) (ContinuousMap.id X) {x})
    (R : ContinuousMap.HomotopyRel (f.comp g) (ContinuousMap.id Y) {y})
    (a : Pi (n + 1) X x) :
    mulEquivOfBasedInverse n f g hf hg L R a = mapHomOfEq f hf n a := rfl

/-- The forward group map is exactly the map induced by the given continuous map. -/
public theorem mulEquivOfBasedInverse_apply (n : ℕ)
    (f : C(X, Y)) (g : C(Y, X)) (hf : f x = y) (hg : g y = x)
    (L : ContinuousMap.HomotopyRel (g.comp f) (ContinuousMap.id X) {x})
    (R : ContinuousMap.HomotopyRel (f.comp g) (ContinuousMap.id Y) {y})
    (a : Pi (n + 1) X x) :
    mulEquivOfBasedInverse n f g hf hg L R a = mapHomOfEq f hf n a :=
  mulEquivOfBasedInverse_apply_computed n f g hf hg L R a

private theorem mulEquivOfBasedInverse_symm_apply_computed (n : ℕ)
    (f : C(X, Y)) (g : C(Y, X)) (hf : f x = y) (hg : g y = x)
    (L : ContinuousMap.HomotopyRel (g.comp f) (ContinuousMap.id X) {x})
    (R : ContinuousMap.HomotopyRel (f.comp g) (ContinuousMap.id Y) {y})
    (a : Pi (n + 1) Y y) :
    (mulEquivOfBasedInverse n f g hf hg L R).symm a = mapHomOfEq g hg n a := rfl

/-- The inverse group map is exactly the map induced by the given based inverse. -/
public theorem mulEquivOfBasedInverse_symm_apply (n : ℕ)
    (f : C(X, Y)) (g : C(Y, X)) (hf : f x = y) (hg : g y = x)
    (L : ContinuousMap.HomotopyRel (g.comp f) (ContinuousMap.id X) {x})
    (R : ContinuousMap.HomotopyRel (f.comp g) (ContinuousMap.id Y) {y})
    (a : Pi (n + 1) Y y) :
    (mulEquivOfBasedInverse n f g hf hg L R).symm a = mapHomOfEq g hg n a :=
  mulEquivOfBasedInverse_symm_apply_computed n f g hf hg L R a

end BasedMaps

section DiscreteProduct

variable {D : Type u} {Y : Type v}
  [TopologicalSpace D] [DiscreteTopology D] [TopologicalSpace Y]

private theorem discreteCube_first_eq (n : ℕ) (d : D) (y : Y)
    (p : GenLoop (Fin (n + 1)) (D × Y) (d, y)) (t : I^(Fin (n + 1))) :
    (p t).1 = d := by
  have hContinuous : Continuous (fun s : I^(Fin (n + 1)) => (p s).1) :=
    continuous_fst.comp p.1.continuous
  have hLocally : IsLocallyConstant (fun s : I^(Fin (n + 1)) => (p s).1) :=
    (IsLocallyConstant.iff_continuous _).mpr hContinuous
  have hSame : (p t).1 = (p 0).1 := hLocally.apply_eq_of_preconnectedSpace t 0
  have hBoundary : p 0 = (d, y) := GenLoop.boundary p 0 ⟨0, Or.inl rfl⟩
  exact hSame.trans (congrArg Prod.fst hBoundary)

/-- Projection to the second factor gives the positive homotopy-group
equivalence at the chosen pair point when the first factor is discrete. -/
public def discreteProductSndMulEquiv (n : ℕ) (d : D) (y : Y) :
    Pi (n + 1) (D × Y) (d, y) ≃* Pi (n + 1) Y y := by
  let f : C(D × Y, Y) := ContinuousMap.snd
  let g : C(Y, D × Y) := (ContinuousMap.const Y d).prodMk (ContinuousMap.id Y)
  let hf : f (d, y) = y := rfl
  let hg : g y = (d, y) := rfl
  refine
    { toFun := mapHomOfEq f hf n
      invFun := mapHomOfEq g hg n
      left_inv := ?_
      right_inv := ?_
      map_mul' := (mapHomOfEq f hf n).map_mul }
  · intro a
    obtain ⟨p, rfl⟩ := mk_surjective a
    rw [mapHomOfEq_mk, mapHomOfEq_mk]
    apply congrArg mk
    apply GenLoop.ext
    intro t
    apply Prod.ext
    · exact (discreteCube_first_eq n d y p t).symm
    · rfl
  · intro a
    obtain ⟨p, rfl⟩ := mk_surjective a
    rw [mapHomOfEq_mk, mapHomOfEq_mk]
    apply congrArg mk
    apply GenLoop.ext
    intro t
    rfl

private theorem discreteProductSndMulEquiv_apply_computed (n : ℕ) (d : D) (y : Y)
    (a : Pi (n + 1) (D × Y) (d, y)) :
    discreteProductSndMulEquiv n d y a =
      mapHomOfEq (ContinuousMap.snd : C(D × Y, Y)) rfl n a := rfl

/-- The projection equivalence has exactly the original second-projection map. -/
public theorem discreteProductSndMulEquiv_apply (n : ℕ) (d : D) (y : Y)
    (a : Pi (n + 1) (D × Y) (d, y)) :
    discreteProductSndMulEquiv n d y a =
      mapHomOfEq (ContinuousMap.snd : C(D × Y, Y)) rfl n a :=
  discreteProductSndMulEquiv_apply_computed n d y a

private theorem discreteProductSndMulEquiv_symm_apply_computed (n : ℕ) (d : D) (y : Y)
    (a : Pi (n + 1) Y y) :
    (discreteProductSndMulEquiv n d y).symm a =
      mapHomOfEq ((ContinuousMap.const Y d).prodMk (ContinuousMap.id Y)) rfl n a := rfl

/-- The inverse uses the actual section with constant first coordinate. -/
public theorem discreteProductSndMulEquiv_symm_apply (n : ℕ) (d : D) (y : Y)
    (a : Pi (n + 1) Y y) :
    (discreteProductSndMulEquiv n d y).symm a =
      mapHomOfEq ((ContinuousMap.const Y d).prodMk (ContinuousMap.id Y)) rfl n a :=
  discreteProductSndMulEquiv_symm_apply_computed n d y a

end DiscreteProduct

end HomotopyGroup

end
