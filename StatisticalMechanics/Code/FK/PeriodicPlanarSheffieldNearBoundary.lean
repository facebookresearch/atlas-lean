/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldHalfPlaneInfiniteArm
import Code.FK.PeriodicPlanarSheffieldApproximatePreference











open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def PeriodicPlaneEmbedding.leftBoundaryExhaustionVertices
    (E : PeriodicPlaneEmbedding P) (r : Real) (n : Nat) : Set V :=
  E.rectVertices r (r + n) (-(n : Real)) n



def PeriodicPlaneEmbedding.leftBoundaryExhaustionEvent
    (E : PeriodicPlaneEmbedding P) (r : Real) (S : Set V) (n : Nat) :
    Set (ConfigSpace (Sym2 V)) :=
  E.rectSideConnectionEvent r (r + n) (-(n : Real)) n S
    (E.rectLeftBoundaryVertices r (r + n) (-(n : Real)) n)

theorem PeriodicPlaneEmbedding.leftBoundaryExhaustionVertices_mono
    (E : PeriodicPlaneEmbedding P) (r : Real) :
    Monotone (E.leftBoundaryExhaustionVertices r) := by
  intro n N hnN v hv
  change r ≤ E.vertexCoord v 0 ∧ E.vertexCoord v 0 ≤ r + n ∧
    -(n : Real) ≤ E.vertexCoord v 1 ∧ E.vertexCoord v 1 ≤ n at hv
  change r ≤ E.vertexCoord v 0 ∧ E.vertexCoord v 0 ≤ r + N ∧
    -(N : Real) ≤ E.vertexCoord v 1 ∧ E.vertexCoord v 1 ≤ N
  have hcast : (n : Real) ≤ N := by exact_mod_cast hnN
  rcases hv with ⟨h0, h1, h2, h3⟩
  exact ⟨h0, by linarith, by linarith, by linarith⟩

theorem PeriodicPlaneEmbedding.leftBoundaryExhaustionEvent_mono
    (E : PeriodicPlaneEmbedding P) (r : Real) (S : Set V) :
    Monotone (E.leftBoundaryExhaustionEvent r S) := by
  intro n N hnN
  rintro omega ⟨x, hxS, hxinf, y, hy, hxy⟩
  refine ⟨x, hxS, hxinf, y, ?_,
    P.connectedWithinSet_mono_region
      (E.leftBoundaryExhaustionVertices_mono r hnN) x y hxy⟩
  obtain ⟨hyRect, z, hyz, hz⟩ := hy
  exact ⟨E.leftBoundaryExhaustionVertices_mono r hnN hyRect,
    z, hyz, hz⟩



theorem PeriodicPlaneEmbedding.exists_leftBoundaryExhaustion_subset
    (E : PeriodicPlaneEmbedding P) (r : Real) {S : Set V}
    (hSfinite : S.Finite) (hSH : S ⊆ E.rightHalfPlaneVertices r) :
    ∃ n : Nat, S ⊆ E.leftBoundaryExhaustionVertices r n := by
  classical
  let F := hSfinite.toFinset
  let M : Real := ∑ v ∈ F,
    (|E.vertexCoord v 0 - r| + |E.vertexCoord v 1|)
  obtain ⟨n, hn⟩ := exists_nat_ge M
  refine ⟨n, ?_⟩
  intro v hvS
  have hvF : v ∈ F := by simpa [F] using hvS
  have hvterm : |E.vertexCoord v 0 - r| + |E.vertexCoord v 1| ≤ M := by
    dsimp only [M]
    exact Finset.single_le_sum
      (fun w _ => show 0 ≤ |E.vertexCoord w 0 - r| +
        |E.vertexCoord w 1| from
          add_nonneg (abs_nonneg _) (abs_nonneg _)) hvF
  have hn' : M ≤ (n : Real) := hn
  have hvH := hSH hvS
  change r ≤ E.vertexCoord v 0 at hvH
  change r ≤ E.vertexCoord v 0 ∧ E.vertexCoord v 0 ≤ r + n ∧
    -(n : Real) ≤ E.vertexCoord v 1 ∧ E.vertexCoord v 1 ≤ n
  constructor
  · exact hvH
  constructor
  · linarith [le_abs_self (E.vertexCoord v 0 - r), abs_nonneg (E.vertexCoord v 1)]
  constructor
  · linarith [neg_le_abs (E.vertexCoord v 1),
      abs_nonneg (E.vertexCoord v 0 - r)]
  · linarith [le_abs_self (E.vertexCoord v 1),
      abs_nonneg (E.vertexCoord v 0 - r)]



theorem PeriodicPlaneEmbedding.iUnion_leftBoundaryExhaustionEvent
    (E : PeriodicPlaneEmbedding P) (r : Real) {S : Set V}
    (hSfinite : S.Finite) (hSH : S ⊆ E.rightHalfPlaneVertices r) :
    (⋃ n : Nat, E.leftBoundaryExhaustionEvent r S n) =
      P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r) := by
  classical
  ext omega
  constructor
  · intro homega
    obtain ⟨n, x, hxS, hxinf, y, hy, hxy⟩ := Set.mem_iUnion.mp homega
    obtain ⟨hyRect, z, hyz, hz⟩ := hy
    refine ⟨x, hxS, hxinf, y, ⟨hyRect.1, z, hyz, hz⟩, ?_⟩
    exact P.connectedWithinSet_mono_region (fun v hv => hv.1) x y hxy
  · rintro ⟨x, hxS, hxinf, y, hy, l, hchain, hlast, hregion⟩
    let F := hSfinite.toFinset ∪ (x :: l).toFinset
    let M : Real := ∑ v ∈ F,
      (|E.vertexCoord v 0 - r| + |E.vertexCoord v 1|)
    obtain ⟨n, hn⟩ := exists_nat_ge M
    have hbound (v : V) (hvF : v ∈ F) :
        |E.vertexCoord v 0 - r| + |E.vertexCoord v 1| ≤ M := by
      dsimp only [M]
      exact Finset.single_le_sum
        (fun w _ => show 0 ≤ |E.vertexCoord w 0 - r| +
          |E.vertexCoord w 1| from
            add_nonneg (abs_nonneg _) (abs_nonneg _)) hvF
    have hrect (v : V) (hvF : v ∈ F)
        (hvH : v ∈ E.rightHalfPlaneVertices r) :
        v ∈ E.leftBoundaryExhaustionVertices r n := by
      have hvb := hbound v hvF
      have hn' : M ≤ (n : Real) := hn
      change r ≤ E.vertexCoord v 0 at hvH
      change r ≤ E.vertexCoord v 0 ∧ E.vertexCoord v 0 ≤ r + n ∧
        -(n : Real) ≤ E.vertexCoord v 1 ∧ E.vertexCoord v 1 ≤ n
      constructor
      · exact hvH
      constructor
      · linarith [le_abs_self (E.vertexCoord v 0 - r),
          abs_nonneg (E.vertexCoord v 1)]
      constructor
      · linarith [neg_le_abs (E.vertexCoord v 1),
          abs_nonneg (E.vertexCoord v 0 - r)]
      · linarith [le_abs_self (E.vertexCoord v 1),
          abs_nonneg (E.vertexCoord v 0 - r)]
    have hxF : x ∈ F := by simp [F]
    have hyList : y ∈ x :: l := by
      rw [← hlast]
      exact List.getLast_mem _
    have hyF : y ∈ F := by
      change y ∈ hSfinite.toFinset ∪ (x :: l).toFinset
      rw [Finset.mem_union]
      exact Or.inr (by simpa using hyList)
    have hyRect := hrect y hyF hy.1
    have hpathRect : ∀ v ∈ x :: l,
        v ∈ E.leftBoundaryExhaustionVertices r n := by
      intro v hv
      apply hrect v
      · change v ∈ hSfinite.toFinset ∪ (x :: l).toFinset
        rw [Finset.mem_union]
        exact Or.inr (by simpa using hv)
      · exact hregion v hv
    apply Set.mem_iUnion.2
    exact ⟨n, x, hxS, hxinf, y,
      ⟨hyRect, hy.2⟩, l, hchain, hlast, hpathRect⟩

theorem PeriodicPlaneEmbedding.leftBoundaryExhaustion_measureReal_tendsto
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r : Real) {S : Set V}
    (hSfinite : S.Finite) (hSH : S ⊆ E.rightHalfPlaneVertices r) :
    Tendsto (fun n => mu.real (E.leftBoundaryExhaustionEvent r S n))
      atTop (nhds (mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r)))) := by
  have hmeasure := tendsto_measure_iUnion_atTop (μ := mu)
    (E.leftBoundaryExhaustionEvent_mono r S)
  rw [E.iUnion_leftBoundaryExhaustionEvent r hSfinite hSH] at hmeasure
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure



theorem PeriodicPlaneEmbedding.exists_leftBoundaryExhaustion_measureReal_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (r : Real) {S : Set V}
    (hSfinite : S.Finite) (hSH : S ⊆ E.rightHalfPlaneVertices r)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ n : Nat, S ⊆ E.leftBoundaryExhaustionVertices r n ∧
      mu.real (P.infiniteSetConnectionWithin
          (E.rightHalfPlaneVertices r) S
          (E.rightHalfPlaneBoundaryVertices r)) - epsilon <
        mu.real (E.leftBoundaryExhaustionEvent r S n) := by
  obtain ⟨nSource, hnSource⟩ :=
    E.exists_leftBoundaryExhaustion_subset r hSfinite hSH
  have hlim := E.leftBoundaryExhaustion_measureReal_tendsto
    mu r hSfinite hSH
  have hev : ∀ᶠ n : Nat in atTop,
      mu.real (P.infiniteSetConnectionWithin
          (E.rightHalfPlaneVertices r) S
          (E.rightHalfPlaneBoundaryVertices r)) - epsilon <
        mu.real (E.leftBoundaryExhaustionEvent r S n) :=
    (tendsto_order.1 hlim).1 _ (sub_lt_self _ hepsilon)
  obtain ⟨nScore, hnScore⟩ := hev.exists
  let n := max nSource nScore
  refine ⟨n, ?_, ?_⟩
  · exact fun v hv => E.leftBoundaryExhaustionVertices_mono r
      (Nat.le_max_left _ _) (hnSource hv)
  · exact hnScore.trans_le (measureReal_mono
      (E.leftBoundaryExhaustionEvent_mono r S (Nat.le_max_right _ _)))



theorem PeriodicPlaneEmbedding.exists_leftBoundaryPlacement_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) :
    ∃ source : Nat → Finset V, ∃ radius : Nat → Nat,
      (∀ N, (source N : Set V) ⊆
        E.leftBoundaryExhaustionVertices r (radius N)) ∧
      Tendsto (fun N => mu.real (E.leftBoundaryExhaustionEvent r
        (source N : Set V) (radius N))) atTop (nhds 1) := by
  obtain ⟨S, hSfinite, hSH, hhalf⟩ :=
    E.exists_infiniteBoundaryConnection_sequence_tendsto_one
      mu hFKG hTI hunique r
  choose radius hradius using fun N =>
    E.exists_leftBoundaryExhaustion_measureReal_gt mu r
      (hSfinite N) (hSH N)
      (show 0 < (1 : Real) / (N + 1) by positivity)
  let source : Nat → Finset V := fun N => (hSfinite N).toFinset
  refine ⟨source, radius, ?_, ?_⟩
  · intro N
    simpa [source] using (hradius N).1
  · have herror : Tendsto (fun N : Nat => (1 : Real) / (N + 1))
        atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hlower : Tendsto (fun N =>
        mu.real (P.infiniteSetConnectionWithin
          (E.rightHalfPlaneVertices r) (S N)
          (E.rightHalfPlaneBoundaryVertices r)) -
          (1 : Real) / (N + 1)) atTop (nhds 1) := by
      simpa using hhalf.sub herror
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlower tendsto_const_nhds
    · intro N
      simpa [source] using le_of_lt (hradius N).2
    · intro N
      exact measureReal_le_one




theorem PeriodicPlaneEmbedding.exists_translatedOrbitBox_leftBoundaryPlacement_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) :
    ∃ base : Nat → Site 2, ∃ radius : Nat → Nat,
      (∀ N, (P.shift (base N) '' (P.orbitBox N : Set V)) ⊆
        E.leftBoundaryExhaustionVertices r (radius N)) ∧
      Tendsto (fun N => mu.real (E.leftBoundaryExhaustionEvent r
        (P.shift (base N) '' (P.orbitBox N : Set V)) (radius N)))
        atTop (nhds 1) := by
  choose base outside hinside houtside using fun N =>
    E.exists_opposite_translated_orbitBox N r
  let S : Nat → Set V := fun N =>
    P.shift (base N) '' (P.orbitBox N : Set V)
  have hSfinite (N : Nat) : (S N).Finite :=
    (P.orbitBox N).finite_toSet.image (P.shift (base N))
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun _ h => h.1
  have hbox := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  have hlower : Tendsto (fun N =>
      (mu.real (P.orbitBoxHitsInfinite N)) ^ 2) atTop (nhds 1) := by
    simpa using hbox.pow 2
  have hhalf : Tendsto (fun N => mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (S N)
        (E.rightHalfPlaneBoundaryVertices r))) atTop (nhds 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlower tendsto_const_nhds
    · intro N
      have hsq := E.infiniteBoundaryConnection_measureReal_ge_sq_of_translate
        mu hFKG hTI hunique r (S N) (outside N) (hinside N) (houtside N)
      have hmass : mu.real (P.setHitsInfinite (S N)) =
          mu.real (P.orbitBoxHitsInfinite N) := by
        dsimp only [S]
        rw [P.setHitsInfinite_translate_measureReal_eq mu hTI (base N)]
        rfl
      rwa [hmass] at hsq
    · intro N
      exact measureReal_le_one
  choose radius hradius using fun N =>
    E.exists_leftBoundaryExhaustion_measureReal_gt mu r
      (hSfinite N) (hinside N)
      (show 0 < (1 : Real) / (N + 1) by positivity)
  refine ⟨base, radius, fun N => (hradius N).1, ?_⟩
  have herror : Tendsto (fun N : Nat => (1 : Real) / (N + 1))
      atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hbound : Tendsto (fun N =>
      mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) (S N)
        (E.rightHalfPlaneBoundaryVertices r)) -
        (1 : Real) / (N + 1)) atTop (nhds 1) := by
    simpa using hhalf.sub herror
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    hbound tendsto_const_nhds
  · intro N
    simpa only [S] using le_of_lt (hradius N).2
  · intro N
    exact measureReal_le_one




theorem PeriodicPlaneEmbedding.exists_buffered_leftBoundaryPlacement_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (buffer : Nat → Nat) (hbuffer : ∀ N, N ≤ buffer N) (r : Real) :
    ∃ base : Nat → Site 2, ∃ radius : Nat → Nat,
      (∀ N, (P.shift (base N) '' (P.orbitBox (buffer N) : Set V)) ⊆
        E.leftBoundaryExhaustionVertices r (radius N)) ∧
      Tendsto (fun N => mu.real (E.leftBoundaryExhaustionEvent r
        (P.shift (base N) '' (P.orbitBox N : Set V)) (radius N)))
        atTop (nhds 1) := by
  choose base hbigH using fun N =>
    E.exists_shift_orbitBox_subset_rightHalfPlane (buffer N) r
  choose left hleft using fun N =>
    E.exists_shift_orbitBox_subset_leftComplement N r
  let outside : Nat → Site 2 := fun N => left N - base N
  let small : Nat → Set V := fun N =>
    P.shift (base N) '' (P.orbitBox N : Set V)
  let big : Nat → Set V := fun N =>
    P.shift (base N) '' (P.orbitBox (buffer N) : Set V)
  have hsmallBig (N : Nat) : small N ⊆ big N := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, P.orbitBox_mono (hbuffer N) hv, rfl⟩
  have hsmallH (N : Nat) : small N ⊆ E.rightHalfPlaneVertices r := by
    rintro _ ⟨v, hv, rfl⟩
    exact hbigH N v (P.orbitBox_mono (hbuffer N) hv)
  have houtside (N : Nat) :
      P.shift (outside N) '' small N ⊆
        (E.rightHalfPlaneVertices r)ᶜ := by
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    have hshift : P.shift (outside N) (P.shift (base N) v) =
        P.shift (left N) v := by
      rw [← P.shift_add]
      simp [outside]
    rw [hshift]
    exact hleft N v hv
  have hsmallFinite (N : Nat) : (small N).Finite :=
    (P.orbitBox N).finite_toSet.image (P.shift (base N))
  have hbigFinite (N : Nat) : (big N).Finite :=
    (P.orbitBox (buffer N)).finite_toSet.image (P.shift (base N))
  have hbigSubset (N : Nat) : big N ⊆ E.rightHalfPlaneVertices r := by
    rintro _ ⟨v, hv, rfl⟩
    exact hbigH N v hv
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun _ h => h.1
  have hbox := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  have hlower : Tendsto (fun N =>
      (mu.real (P.orbitBoxHitsInfinite N)) ^ 2) atTop (nhds 1) := by
    simpa using hbox.pow 2
  have hhalf : Tendsto (fun N => mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (small N)
        (E.rightHalfPlaneBoundaryVertices r))) atTop (nhds 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlower tendsto_const_nhds
    · intro N
      have hsq := E.infiniteBoundaryConnection_measureReal_ge_sq_of_translate
        mu hFKG hTI hunique r (small N) (outside N)
          (hsmallH N) (houtside N)
      have hmass : mu.real (P.setHitsInfinite (small N)) =
          mu.real (P.orbitBoxHitsInfinite N) := by
        dsimp only [small]
        rw [P.setHitsInfinite_translate_measureReal_eq mu hTI (base N)]
        rfl
      rwa [hmass] at hsq
    · intro N
      exact measureReal_le_one
  choose sourceRadius hsourceRadius using fun N =>
    E.exists_leftBoundaryExhaustion_subset r (hbigFinite N) (hbigSubset N)
  choose scoreRadius hscoreRadius using fun N =>
    E.exists_leftBoundaryExhaustion_measureReal_gt mu r
      (hsmallFinite N) (hsmallH N)
      (show 0 < (1 : Real) / (N + 1) by positivity)
  let radius : Nat → Nat := fun N => max (sourceRadius N) (scoreRadius N)
  refine ⟨base, radius, ?_, ?_⟩
  · intro N
    exact fun v hv => E.leftBoundaryExhaustionVertices_mono r
      (Nat.le_max_left _ _) (hsourceRadius N hv)
  · have herror : Tendsto (fun N : Nat => (1 : Real) / (N + 1))
        atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hbound : Tendsto (fun N =>
        mu.real (P.infiniteSetConnectionWithin
          (E.rightHalfPlaneVertices r) (small N)
          (E.rightHalfPlaneBoundaryVertices r)) -
          (1 : Real) / (N + 1)) atTop (nhds 1) := by
      simpa using hhalf.sub herror
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      hbound tendsto_const_nhds
    · intro N
      have hscore := le_of_lt (hscoreRadius N).2
      exact hscore.trans (measureReal_mono
        (E.leftBoundaryExhaustionEvent_mono r (small N)
          (Nat.le_max_right _ _)))
    · intro N
      exact measureReal_le_one

end StatMech.FK.PeriodicPlanar
