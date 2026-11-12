/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldHalfPlaneCage









open Filter MeasureTheory Set

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}



theorem PeriodicPlaneEmbedding.infiniteOpenBoundaryConnection_measureReal_ge_sq_of_translate
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) (S : Set V) (z : Site 2)
    (hS : S ⊆ E.rightHalfPlaneVertices r)
    (hT : P.shift z '' S ⊆ (E.rightHalfPlaneVertices r)ᶜ) :
    (mu.real (P.setHitsInfinite S)) ^ 2 ≤
      mu.real (E.infiniteOpenBoundaryConnection r S) := by
  have hmul := E.infiniteOpenBoundaryConnection_measureReal_ge_mul
    mu hFKG hunique r hS hT
  rw [P.setHitsInfinite_translate_measureReal_eq mu hTI z S] at hmul
  simpa [pow_two] using hmul



theorem PeriodicPlaneEmbedding.exists_infiniteOpenBoundaryConnection_ge_orbitBox_sq
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) (N : Nat) :
    ∃ S : Set V, S ⊆ E.rightHalfPlaneVertices r ∧
      (mu.real (P.orbitBoxHitsInfinite N)) ^ 2 ≤
        mu.real (E.infiniteOpenBoundaryConnection r S) := by
  obtain ⟨z₀, z₁, hinside, houtside⟩ :=
    E.exists_opposite_translated_orbitBox N r
  let S : Set V := P.shift z₀ '' (P.orbitBox N : Set V)
  refine ⟨S, hinside, ?_⟩
  have hsq := E.infiniteOpenBoundaryConnection_measureReal_ge_sq_of_translate
    mu hFKG hTI hunique r S z₁ hinside houtside
  have hmass : mu.real (P.setHitsInfinite S) =
      mu.real (P.orbitBoxHitsInfinite N) := by
    dsimp only [S]
    rw [P.setHitsInfinite_translate_measureReal_eq mu hTI z₀]
    rfl
  rwa [hmass] at hsq



theorem PeriodicPlaneEmbedding.exists_infiniteOpenBoundaryConnection_sequence_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) :
    ∃ S : Nat → Set V,
      (∀ N, S N ⊆ E.rightHalfPlaneVertices r) ∧
      Tendsto (fun N =>
        mu.real (E.infiniteOpenBoundaryConnection r (S N)))
        atTop (nhds 1) := by
  choose S hS hbound using fun N =>
    E.exists_infiniteOpenBoundaryConnection_ge_orbitBox_sq
      mu hFKG hTI hunique r N
  refine ⟨S, hS, ?_⟩
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun _ h => h.1
  have hbox := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  have hlower : Tendsto
      (fun N => (mu.real (P.orbitBoxHitsInfinite N)) ^ 2)
      atTop (nhds 1) := by
    simpa using hbox.pow 2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlower tendsto_const_nhds hbound (fun _ => measureReal_le_one)


theorem PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo_lower_union_upper
    (E : PeriodicPlaneEmbedding P) (r s : Real) (S : Set V) :
    E.infiniteOpenBoundaryConnectionTo r S
        (E.lowerBoundaryRayVertices r s) ∪
      E.infiniteOpenBoundaryConnectionTo r S
        (E.upperBoundaryRayVertices r s) =
      E.infiniteOpenBoundaryConnection r S := by
  ext omega
  constructor
  · rintro (hlower | hupper)
    · exact E.infiniteOpenBoundaryConnectionTo_subset r S _ hlower
    · exact E.infiniteOpenBoundaryConnectionTo_subset r S _ hupper
  · rintro ⟨x, hxS, hxInfinite, b, hb, z, hbz, hz, hbzOpen, hxb⟩
    rw [E.boundary_eq_lower_union_upper r s] at hb
    rcases hb with hbLower | hbUpper
    · exact Or.inl ⟨x, hxS, hxInfinite, b, hbLower, hbLower.1,
        z, hbz, hz, hbzOpen, hxb⟩
    · exact Or.inr ⟨x, hxS, hxInfinite, b, hbUpper, hbUpper.1,
        z, hbz, hz, hbzOpen, hxb⟩



theorem PeriodicPlaneEmbedding.exists_infiniteOpenBoundaryRay_max_sequence_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) (s : Nat → Real) :
    ∃ S : Nat → Set V,
      (∀ N, S N ⊆ E.rightHalfPlaneVertices r) ∧
      Tendsto (fun N => max
        (mu.real (E.infiniteOpenBoundaryConnectionTo r (S N)
          (E.lowerBoundaryRayVertices r (s N))))
        (mu.real (E.infiniteOpenBoundaryConnectionTo r (S N)
          (E.upperBoundaryRayVertices r (s N))))) atTop (nhds 1) := by
  obtain ⟨S, hS, hfull⟩ :=
    E.exists_infiniteOpenBoundaryConnection_sequence_tendsto_one
      mu hFKG hTI hunique r
  refine ⟨S, hS, ?_⟩
  let L : Nat → Set (ConfigSpace (Sym2 V)) := fun N =>
    E.infiniteOpenBoundaryConnectionTo r (S N)
      (E.lowerBoundaryRayVertices r (s N))
  let U : Nat → Set (ConfigSpace (Sym2 V)) := fun N =>
    E.infiniteOpenBoundaryConnectionTo r (S N)
      (E.upperBoundaryRayVertices r (s N))
  let F : Nat → Set (ConfigSpace (Sym2 V)) := fun N =>
    E.infiniteOpenBoundaryConnection r (S N)
  have hFU (N : Nat) : L N ∪ U N = F N := by
    exact E.infiniteOpenBoundaryConnectionTo_lower_union_upper r (s N) (S N)
  have hsqrt (N : Nat) :
      1 - Real.sqrt (1 - mu.real (F N)) ≤
        max (mu.real (L N)) (mu.real (U N)) := by
    have h := measurable_sqrt_trick mu hFKG
      (E.infiniteOpenBoundaryConnectionTo_isIncreasing r (S N)
        (E.lowerBoundaryRayVertices r (s N)))
      (E.infiniteOpenBoundaryConnectionTo_isIncreasing r (S N)
        (E.upperBoundaryRayVertices r (s N)))
      (E.infiniteOpenBoundaryConnectionTo_measurableSet r (S N)
        (E.lowerBoundaryRayVertices r (s N)))
      (E.infiniteOpenBoundaryConnectionTo_measurableSet r (S N)
        (E.upperBoundaryRayVertices r (s N)))
    change 1 - Real.sqrt (1 - mu.real (L N ∪ U N)) ≤
      max (mu.real (L N)) (mu.real (U N)) at h
    rwa [hFU N] at h
  have hfull' : Tendsto (fun N => mu.real (F N)) atTop (nhds 1) := by
    simpa only [F] using hfull
  have hmiss : Tendsto (fun N => 1 - mu.real (F N)) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hfull'
  have hlower : Tendsto (fun N =>
      1 - Real.sqrt (1 - mu.real (F N))) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hmiss.sqrt
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlower (tendsto_const_nhds (x := (1 : Real))) hsqrt
  intro N
  exact max_le measureReal_le_one measureReal_le_one

end StatMech.FK.PeriodicPlanar
