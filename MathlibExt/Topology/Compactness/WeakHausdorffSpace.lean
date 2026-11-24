/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace

/-!
# Weak Hausdorff spaces

A topological space is weak Hausdorff when every continuous image of a
compact Hausdorff space is closed.  We use an explicit universe parameter
for the compact Hausdorff probes, parallel to `UCompactlyGeneratedSpace`.

For compactly generated spaces, weak Hausdorffness is equivalently detected
by closed equalizers of pairs of maps from compact Hausdorff probes.  This
formulation does not use the ordinary product diagonal, which would impose
the strictly stronger Hausdorff condition.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open Set TopologicalSpace Filter
open scoped Topology

/-- A space is `u`-weak Hausdorff when every continuous image of a compact
Hausdorff space in universe `u` is closed. -/
@[univ_out_params]
class UWeakHausdorffSpace (X : Type v) [TopologicalSpace X] : Prop where
  /-- Continuous images of compact Hausdorff probes are closed. -/
  isClosed_range :
    ∀ (K : CompHaus.{u}) (f : C(K, X)), IsClosed (Set.range f)

/-- The same-universe weak-Hausdorff predicate. -/
abbrev WeakHausdorffSpace (X : Type u) [TopologicalSpace X] : Prop :=
  UWeakHausdorffSpace.{u} X

/-- Every Hausdorff space is weak Hausdorff. -/
theorem uWeakHausdorffSpaceOfT2
    (X : Type v) [TopologicalSpace X] [T2Space X] :
    UWeakHausdorffSpace.{u} X where
  isClosed_range _ f := (isCompact_range f.continuous).isClosed

variable {X : Type v}

instance (priority := 100) [TopologicalSpace X] [T2Space X] :
    UWeakHausdorffSpace.{u} X :=
  uWeakHausdorffSpaceOfT2 X

namespace UWeakHausdorffSpace

/-- Every weak-Hausdorff space is T1.  This is a named value, rather than a
global instance, because the compact-probe universe is not determined by a
bare `T1Space X` goal. -/
theorem toT1Space (X : Type v) [TopologicalSpace X]
    [UWeakHausdorffSpace.{u} X] : T1Space X where
  t1 x := by
    let K : CompHaus.{u} := CompHaus.of (ULift.{u} (Fin 1))
    let c : C(K, X) := ContinuousMap.const K x
    have hc : IsClosed (Set.range c) :=
      UWeakHausdorffSpace.isClosed_range K c
    have hRange : Set.range c = {x} := by
      apply Set.Subset.antisymm
      · exact Set.range_const_subset
      · intro y hy
        simp only [Set.mem_singleton_iff] at hy
        subst y
        exact ⟨ULift.up (0 : Fin 1), rfl⟩
    exact hRange ▸ hc

end UWeakHausdorffSpace

private theorem isClosed_equalizer_of_uWeakHausdorffSpace
    {X : Type v} [TopologicalSpace X]
    [UWeakHausdorffSpace.{u} X]
    (K : CompHaus.{u}) (f g : C(K, X)) :
    IsClosed {k | f k = g k} := by
  let _ : T1Space X := UWeakHausdorffSpace.toT1Space X
  let E : Set K := {k | f k = g k}
  rw [show {k | f k = g k} = E from rfl]
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro a ha
  have hfa : f a ≠ g a := by simpa [E] using ha
  let U : Set K := f ⁻¹' ({g a}ᶜ)
  have hUOpen : IsOpen U :=
    isOpen_compl_singleton.preimage f.continuous
  have hU : U ∈ 𝓝ˢ ({a} : Set K) :=
    hUOpen.mem_nhdsSet.2 (by simpa [U] using hfa)
  obtain ⟨V, hVOpen, hSingletonV, hClosureVU⟩ :=
    isCompact_singleton.exists_isOpen_closure_subset hU
  have haV : a ∈ V := hSingletonV (Set.mem_singleton a)
  let _ : CompactSpace (closure V) :=
    isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  let KV : CompHaus.{u} := CompHaus.of (closure V)
  let fV : C(KV, X) :=
    f.comp (ContinuousMap.subtypeVal (closure V))
  have hRangeClosed : IsClosed (Set.range fV) :=
    UWeakHausdorffSpace.isClosed_range KV fV
  have hRange : Set.range fV = f '' closure V := by
    ext x
    simp [fV, KV, Set.range_comp]
  have hImageClosed : IsClosed (f '' closure V) :=
    hRange ▸ hRangeClosed
  let W : Set K := V ∩ g ⁻¹' (f '' closure V)ᶜ
  have hWOpen : IsOpen W :=
    hVOpen.inter (hImageClosed.isOpen_compl.preimage g.continuous)
  have haW : a ∈ W := by
    refine ⟨haV, ?_⟩
    rintro ⟨b, hb, hba⟩
    exact (hClosureVU hb) hba
  have hWE : W ⊆ Eᶜ := by
    rintro k ⟨hkV, hkImage⟩ hkE
    apply hkImage
    exact ⟨k, subset_closure hkV, hkE⟩
  exact ⟨W, hWE, hWOpen, haW⟩

private theorem uWeakHausdorffSpace_of_isClosed_equalizer
    {X : Type v} [TopologicalSpace X]
    [UCompactlyGeneratedSpace.{u} X]
    (h : ∀ (K : CompHaus.{u}) (f g : C(K, X)),
      IsClosed {k | f k = g k}) :
    UWeakHausdorffSpace.{u} X where
  isClosed_range K f := by
    apply UCompactlyGeneratedSpace.isClosed
    intro L g
    let A : Set (K × L) := {p | f p.1 = g p.2}
    have hA : IsClosed A := by
      simpa [A] using h (CompHaus.of (K × L))
        (f.comp ContinuousMap.fst) (g.comp ContinuousMap.snd)
    have hImageCompact : IsCompact (Prod.snd '' A) :=
      hA.isCompact.image continuous_snd
    have hImageClosed : IsClosed (Prod.snd '' A) :=
      hImageCompact.isClosed
    have hImage : Prod.snd '' A = g ⁻¹' Set.range f := by
      ext l
      constructor
      · rintro ⟨⟨k, l'⟩, hEq, rfl⟩
        exact ⟨k, hEq⟩
      · rintro ⟨k, hk⟩
        exact ⟨(k, l), hk, rfl⟩
    rw [← hImage]
    exact hImageClosed

/-- In a compactly generated space, weak Hausdorffness is equivalent to
closedness of every equalizer of two maps from a compact Hausdorff probe. -/
theorem uWeakHausdorffSpace_iff_isClosed_equalizer
    {X : Type v} [TopologicalSpace X]
    [UCompactlyGeneratedSpace.{u} X] :
    UWeakHausdorffSpace.{u} X ↔
      ∀ (K : CompHaus.{u}) (f g : C(K, X)),
        IsClosed {k | f k = g k} :=
  ⟨fun _ ↦ isClosed_equalizer_of_uWeakHausdorffSpace,
    uWeakHausdorffSpace_of_isClosed_equalizer⟩
