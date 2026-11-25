/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsNoetherianRing_exists_completeOrthogonalIdempotents_forall_
connectedSpace_primeSpectrum.lean`
and
`P2M/Sol/S_IsNoetherianRing_exists_completeOrthogonalIdempotents_forall_
connectedSpace_primeSpectrum.lean`
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

public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Basic
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.NoetherianSpace

@[expose] public section

open TopologicalSpace PrimeSpectrum Topology

private theorem finite_connectedComponents_aux {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] : Finite (ConnectedComponents X) := by
  classical
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  have : Finite (irreducibleComponents X) := hfin.to_subtype
  have hirr : ∀ Z ∈ irreducibleComponents X, IsIrreducible Z := fun Z hZ => hZ.1
  let φ : irreducibleComponents X → ConnectedComponents X := fun Z =>
    ConnectedComponents.mk (hirr Z.1 Z.2).nonempty.some
  refine Finite.of_surjective φ fun c => ?_
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  refine ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
  simp only [φ]
  rw [ConnectedComponents.coe_eq_coe']
  exact (isIrreducible_irreducibleComponent.isConnected.isPreconnected.subset_connectedComponent
    mem_irreducibleComponent)
    (hirr _ (irreducibleComponent_mem_irreducibleComponents x)).nonempty.some_mem

private theorem isClopen_connectedComponent_aux {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] (x : X) : IsClopen (connectedComponent x) := by
  classical
  have : Finite (ConnectedComponents X) := finite_connectedComponents_aux
  refine ⟨isClosed_connectedComponent, ?_⟩
  have hcompl : (connectedComponent x)ᶜ =
      ⋃ c ∈ {c : ConnectedComponents X | c ≠ ConnectedComponents.mk x},
        ConnectedComponents.mk ⁻¹' {c} := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage,
      Set.mem_singleton_iff, exists_prop, exists_eq_right', ne_eq]
    show y ∉ connectedComponent x ↔ ¬ ConnectedComponents.mk y = ConnectedComponents.mk x
    rw [ConnectedComponents.coe_eq_coe']
  rw [← isClosed_compl_iff, hcompl]
  refine Set.Finite.isClosed_biUnion (Set.toFinite _) fun c _ => ?_
  obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [connectedComponents_preimage_singleton]
  exact isClosed_connectedComponent

/-- A commutative Noetherian ring admits a finite complete orthogonal
idempotent decomposition such that localizing away from each idempotent
gives a ring whose prime spectrum is connected. -/
public theorem
    IsNoetherianRing.exists_completeOrthogonalIdempotents_forall_connectedSpace_primeSpectrum
    (R : Type*) [CommRing R] [IsNoetherianRing R] :
    ∃ (m : ℕ) (e : Fin m → R), CompleteOrthogonalIdempotents e ∧
      ∀ i, ConnectedSpace (PrimeSpectrum (Localization.Away (e i))) := by
  classical
  haveI : Finite (ConnectedComponents (PrimeSpectrum R)) := finite_connectedComponents_aux
  letI : Fintype (ConnectedComponents (PrimeSpectrum R)) := Fintype.ofFinite _
  have hclopen : ∀ c : ConnectedComponents (PrimeSpectrum R),
      IsClopen (ConnectedComponents.mk ⁻¹' {c}) := by
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [connectedComponents_preimage_singleton]
    exact isClopen_connectedComponent_aux x
  choose e he hbasic using fun c =>
    PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen (hclopen c)
  have hmem : ∀ (c : ConnectedComponents (PrimeSpectrum R)) (p : PrimeSpectrum R),
      e c ∉ p.asIdeal ↔ ConnectedComponents.mk p = c := by
    intro c p
    have := congrArg (p ∈ ·) (hbasic c)
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe,
      PrimeSpectrum.mem_basicOpen, eq_iff_iff] at this
    exact this.symm
  have hortho : ∀ c d, c ≠ d → e c * e d = 0 := by
    intro c d hcd
    have hbot : PrimeSpectrum.basicOpen (e c * e d) = ⊥ := by
      rw [PrimeSpectrum.basicOpen_mul]
      ext p
      simp only [Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
        Opens.coe_bot, Set.mem_empty_iff_false, iff_false, not_and, hmem]
      rintro rfl; exact hcd
    have hnil : IsNilpotent (e c * e d) := (PrimeSpectrum.basicOpen_eq_bot_iff _).mp hbot
    have hid : IsIdempotentElem (e c * e d) := (he c).mul (he d)
    obtain ⟨n, hn⟩ := hnil
    rcases n with _ | n
    · rw [pow_zero] at hn
      rw [← mul_one (e c * e d), hn, mul_zero]
    · rwa [hid.pow_succ_eq] at hn
  have hOI : OrthogonalIdempotents e := ⟨he, fun c d hcd => hortho c d hcd⟩
  have hcomplete : ∑ c, e c = 1 := by
    have hs : IsIdempotentElem (∑ c, e c) := hOI.isIdempotentElem_sum
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem hs IsIdempotentElem.one
    rw [PrimeSpectrum.basicOpen_one]
    ext p
    simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, Opens.coe_top, Set.mem_univ, iff_true]
    intro hsum
    set c₀ := ConnectedComponents.mk p
    have h0 : e c₀ ∉ p.asIdeal := (hmem c₀ p).mpr rfl
    have hrest : ∑ d ∈ Finset.univ.erase c₀, e d ∈ p.asIdeal := by
      refine sum_mem fun d hd => ?_
      have hne : d ≠ c₀ := Finset.ne_of_mem_erase hd
      have : e c₀ * e d ∈ p.asIdeal := by
        rw [hortho c₀ d (Ne.symm hne)]; exact zero_mem _
      exact (p.isPrime.mem_or_mem this).resolve_left h0
    apply h0
    have := Finset.add_sum_erase Finset.univ e (Finset.mem_univ c₀)
    rw [← this] at hsum
    exact (Ideal.add_mem_iff_left _ hrest).mp hsum
  refine ⟨Fintype.card (ConnectedComponents (PrimeSpectrum R)),
    e ∘ (Fintype.equivFin _).symm, ?_, ?_⟩
  · refine ⟨⟨fun i => he _, fun i j hij => hortho _ _ (by simpa using hij)⟩, ?_⟩
    change ∑ i, e ((Fintype.equivFin _).symm i) = 1
    rw [Equiv.sum_comp (Fintype.equivFin _).symm e]
    exact hcomplete
  · intro i
    change ConnectedSpace (PrimeSpectrum (Localization.Away
      (e ((Fintype.equivFin (ConnectedComponents (PrimeSpectrum R))).symm i))))
    generalize (Fintype.equivFin (ConnectedComponents (PrimeSpectrum R))).symm i = c
    have hemb := PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away (e c)) (e c)
    have hrange := PrimeSpectrum.localization_away_comap_range (Localization.Away (e c)) (e c)
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    have hconn : IsConnected (Set.range (PrimeSpectrum.comap
        (algebraMap R (Localization.Away (e (ConnectedComponents.mk x)))))) := by
      rw [hrange, ← hbasic, connectedComponents_preimage_singleton]
      exact isConnected_connectedComponent
    rw [connectedSpace_iff_univ]
    refine ⟨?_, ?_⟩
    · obtain ⟨y, ⟨z, rfl⟩⟩ := hconn.nonempty
      exact ⟨z, Set.mem_univ _⟩
    · rw [← hemb.isInducing.isPreconnected_image, Set.image_univ]
      exact hconn.isPreconnected
