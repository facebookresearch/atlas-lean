/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit.lean`
and
`P2M/Sol/S_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit.lean`
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

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.Finset.Order
public import Mathlib.Order.Directed
public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.RingTheory.Extension.Presentation.Core
import Mathlib.RingTheory.Extension.Presentation.Basic

@[expose] public section

open scoped TensorProduct

universe u v w w'

/-- A directed system `G` with maps `f` has direct limit `P` via `g` if
every element of `P` comes from some stage, elements identified at a
later stage whenever they agree in `P`, and the maps are compatible. -/
@[mk_iff]
public class IsDirectLimit {ι : Type*} [Preorder ι] {M : ι → Type*} {P : Type*}
    (f : (i j : ι) → (h : i ≤ j) → M i → M j) (g : ∀ i, M i → P)
    [DirectedSystem M f] : Prop where
  surj : ∀ m : P, ∃ i, ∃ mi : M i, g i mi = m
  inj : ∀ i j, ∀ mi : M i, ∀ mj : M j, g i mi = g j mj →
    ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k), f i k hik mi = f j k hjk mj
  compatibility : ∀ i j hij x, g j (f i j hij x) = g i x

namespace Algebra

private theorem range_mono_of_isDirectLimit {ι : Type u} [Preorder ι]
    {G : ι → Type v} [∀ i, CommRing (G i)]
    (f : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(f i j h)]
    {R : Type w} [CommRing R] [∀ i, Algebra (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    {i j : ι} (hij : i ≤ j) :
    Set.range (algebraMap (G i) R) ⊆ Set.range (algebraMap (G j) R) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f i j hij x, hR.compatibility i j hij x⟩

private theorem exists_subset_range_of_finite_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    {G : ι → Type v} [∀ i, CommRing (G i)]
    (f : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(f i j h)]
    {R : Type w} [CommRing R] [∀ i, Algebra (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    {s : Set R} (hs : s.Finite) :
    ∃ i : ι, s ⊆ Set.range (algebraMap (G i) R) := by
  classical
  let idx : R → ι := fun r => (hR.surj r).choose
  have hidx : ∀ r : R, r ∈ Set.range (algebraMap (G (idx r)) R) := fun r =>
    let ⟨x, hx⟩ := (hR.surj r).choose_spec
    ⟨x, hx⟩
  obtain ⟨M, hM⟩ := Finset.exists_le (hs.toFinset.image idx)
  refine ⟨M, fun r hr => ?_⟩
  have hle : idx r ≤ M :=
    hM _ (Finset.mem_image_of_mem idx (hs.mem_toFinset.mpr hr))
  exact range_mono_of_isDirectLimit f hR hle (hidx r)

/-- A finitely presented algebra over a directed colimit of rings descends
to a finite stage: some stage already carries a finitely presented model
whose base change is the given algebra. -/
public theorem exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (G : ι → Type v) [∀ i, CommRing (G i)]
    (f : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(f i j h)]
    (R : Type w) [CommRing R] [∀ i, Algebra (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    (A : Type w') [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A] :
    ∃ (i : ι) (A₀ : Type v) (_ : CommRing A₀) (_ : Algebra (G i) A₀)
      (_ : Algebra.FinitePresentation (G i) A₀),
      Nonempty ((R ⊗[G i] A₀) ≃ₐ[R] A) := by
  classical
  let P := Algebra.Presentation.ofFinitePresentation R A
  obtain ⟨i, hi⟩ := exists_subset_range_of_finite_of_isDirectLimit f hR
    (s := P.coeffs) Algebra.Presentation.finite_coeffs
  letI : Algebra (G i) A :=
    ((algebraMap R A).comp (algebraMap (G i) R)).toAlgebra
  haveI : IsScalarTower (G i) R A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : P.HasCoeffs (G i) := ⟨hi⟩
  exact ⟨i, P.ModelOfHasCoeffs (G i), inferInstance, inferInstance, inferInstance,
    ⟨P.tensorModelOfHasCoeffsEquiv (G i)⟩⟩

end Algebra
