/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_Scheme_Hom_exists_isClosed_irreducible_
subset_fiber_of_not_quasiFiniteAt_monoidalV2.lean`
and
`P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_exists_isClosed_irreducible_
subset_fiber_of_not_quasiFiniteAt_monoidalV2.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Topology.NoetherianSpace

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

private theorem exists_isClosed_isIrreducible_ne_singleton {T : Type*}
    [TopologicalSpace T] [TopologicalSpace.NoetherianSpace T]
    (p : T) (hp : ¬ IsOpen ({p} : Set T)) :
    ∃ W : Set T, IsClosed W ∧ IsIrreducible W ∧ p ∈ W ∧ W ≠ {p} := by
  by_contra h
  push Not at h
  apply hp
  set S : Set (Set T) := {C ∈ irreducibleComponents T | p ∉ C} with hS
  have hSfin : S.Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset (Set.sep_subset _ _)
  have hC0 : IsClosed (⋃ C ∈ S, C) :=
    hSfin.isClosed_biUnion fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  have heq : ({p} : Set T) = (⋃ C ∈ S, C)ᶜ := by
    ext q
    simp only [Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion, exists_prop,
      not_exists, not_and]
    constructor
    · rintro rfl C hC
      exact hC.2
    · intro hq
      have hpD : p ∈ irreducibleComponent q := by
        by_contra hpD
        exact hq _ ⟨irreducibleComponent_mem_irreducibleComponents q, hpD⟩
          mem_irreducibleComponent
      have hD := h _ isClosed_irreducibleComponent isIrreducible_irreducibleComponent hpD
      have hmem : q ∈ irreducibleComponent q := mem_irreducibleComponent
      rw [hD] at hmem
      exact hmem
  rw [heq]
  exact hC0.isOpen_compl

/-- A point at which a locally finite type morphism of schemes is not
quasi-finite lies on a nontrivial irreducible closed subset of the source
that maps into the closure of the image point. The subset is only asserted
to lie over `closure {f x}`, not over the set-theoretic fibre of `f x`. -/
public theorem Scheme.Hom.exists_isClosed_isIrreducible_subset_preimage_closure_of_not_quasiFiniteAt
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X)
    (hx : ¬ f.QuasiFiniteAt x) :
    ∃ Z : Set X, IsClosed Z ∧ IsIrreducible Z ∧ x ∈ Z ∧ Z ≠ {x} ∧
      Z ⊆ f.base ⁻¹' closure {f.base x} := by
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber] at hx
  set y := f.base x with hy
  set F := f.fiber y with hF
  set x₀ : F := f.asFiber x with hx₀
  haveI : IsLocallyNoetherian F :=
    inferInstanceAs (IsLocallyNoetherian (Limits.pullback f (Y.fromSpecResidueField y)))
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := F) (x := x₀)
    (U := ⊤) trivial
  haveI : IsAffine U := hU
  haveI : IsNoetherian (U : Scheme.{u}) := { }
  set u₀ : (U : Scheme.{u}) := ⟨x₀, hxU⟩ with hu₀
  have hu₀open : ¬ IsOpen ({u₀} : Set (U : Scheme.{u})) := by
    intro ho
    apply hx
    have himg := (U.isOpen.isOpenMap_subtype_val) _ ho
    have heq : Subtype.val '' ({u₀} : Set (U : Scheme.{u})) = ({x₀} : Set F) := by
      apply Set.Subset.antisymm
      · rintro _ ⟨w, hw, rfl⟩
        have hw' : w = u₀ := Set.eq_of_mem_singleton hw
        rw [hw']
        exact Set.mem_singleton _
      · intro z hz
        have hz' : z = x₀ := Set.eq_of_mem_singleton hz
        exact ⟨u₀, Set.mem_singleton _, by rw [hz']⟩
    exact heq ▸ himg
  obtain ⟨W, hWc, hWi, hu₀W, hWne⟩ := exists_isClosed_isIrreducible_ne_singleton u₀ hu₀open
  set g : (U : Scheme.{u}) ⟶ X := U.ι ≫ f.fiberι y with hg
  have hginj : Function.Injective g.base := by
    intro a b hab
    have h1 : (f.fiberι y).base (U.ι.base a) = (f.fiberι y).base (U.ι.base b) := hab
    rw [← Scheme.Hom.fiberHomeo_apply, ← Scheme.Hom.fiberHomeo_apply] at h1
    have h2 := (f.fiberHomeo y).injective (Subtype.ext h1)
    exact U.ι.injective h2
  have hgx : g.base u₀ = x := by
    change (f.fiberι y).base (U.ι.base u₀) = x
    have hι : U.ι.base u₀ = x₀ := rfl
    rw [hι]
    exact Scheme.Hom.fiberι_asFiber f x
  have hgf : ∀ a, f.base (g.base a) = y := by
    intro a
    have hmem : g.base a ∈ Set.range (f.fiberι y).base := ⟨U.ι.base a, rfl⟩
    rw [Scheme.Hom.range_fiberι] at hmem
    exact hmem
  refine ⟨closure (g.base '' W), isClosed_closure,
    (hWi.image g.base g.continuous.continuousOn).closure,
    subset_closure ⟨u₀, hu₀W, hgx⟩, ?_, ?_⟩
  · intro hZ
    obtain ⟨w, hwW, hwne⟩ : ∃ w ∈ W, w ≠ u₀ := by
      by_contra hall
      push Not at hall
      apply hWne
      exact Set.Subset.antisymm (fun w hw => hall w hw) (Set.singleton_subset_iff.mpr hu₀W)
    have hmem : g.base w ∈ closure (g.base '' W) := subset_closure ⟨w, hwW, rfl⟩
    rw [hZ, Set.mem_singleton_iff, ← hgx] at hmem
    exact hwne (hginj hmem)
  · refine closure_minimal ?_ (isClosed_closure.preimage f.continuous)
    rintro _ ⟨a, -, rfl⟩
    change f.base (g.base a) ∈ closure {f.base x}
    rw [hgf]
    exact subset_closure rfl

end AlgebraicGeometry
