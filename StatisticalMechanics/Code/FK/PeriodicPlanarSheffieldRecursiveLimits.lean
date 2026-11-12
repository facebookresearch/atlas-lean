/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldArrayClosure









open Filter MeasureTheory Set Topology

namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}




theorem PeriodicPlaneEmbedding.exists_cofinalNormalBoundaryBandFamilies_bounded
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
    exists (p : Nat -> Real)
      (family : forall m,
        E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m)),
      Tendsto p atTop (nhds 1) /\ (forall m, p m <= 1) := by
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun _ h => h.1
  let delta : Nat -> Real := fun m => 1 / (m + 1 : Real)
  let p : Nat -> Real := fun m =>
    (mu.real (P.orbitBoxHitsInfinite m)) ^ 2 - delta m
  have hfamily (m : Nat) : Nonempty
      (E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m)) := by
    simpa only [p, delta, PeriodicGraph.setHitsInfinite_orbitBox] using
      E.exists_orbitBox_normalBoundaryBandFamily
        mu hFKG hTI hunique m (by positivity : 0 < delta m)
  let family : forall m,
      E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m) :=
    fun m => Classical.choice (hfamily m)
  have hhit := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  have hdelta : Tendsto delta atTop (nhds 0) := by
    simpa only [delta] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hp : Tendsto p atTop (nhds 1) := by
    convert (hhit.pow 2).sub hdelta using 1 <;> norm_num [p]
  have hp_le (m : Nat) : p m <= 1 := by
    have hprob0 : 0 <= mu.real (P.orbitBoxHitsInfinite m) :=
      measureReal_nonneg
    have hprob1 : mu.real (P.orbitBoxHitsInfinite m) <= 1 :=
      measureReal_le_one
    have hdelta0 : 0 <= delta m := (by positivity : 0 < delta m).le
    have hproduct : 0 <= mu.real (P.orbitBoxHitsInfinite m) *
        (1 - mu.real (P.orbitBoxHitsInfinite m)) :=
      mul_nonneg hprob0 (sub_nonneg.mpr hprob1)
    dsimp only [p]
    nlinarith
  exact ⟨p, family, hp, hp_le⟩




theorem PeriodicPlaneEmbedding.exists_uniformBoundaryBandRadius_with_boundedCofinalConnectorSchedule
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
    exists (radius : Nat -> Nat) (p : Nat -> Real)
      (family : forall m,
        E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m)),
      E.UniformBoundaryBandCrossingRadius mu radius /\
      Tendsto p atTop (nhds 1) /\
      (forall m, p m <= 1) /\
      forall m, (family m).AlignedMarginSchedule E
        (fun _ => E.connectorMarginRequirement (radius m))
        (fun _ => E.connectorMarginRequirement (radius m)) := by
  obtain ⟨radius, hradius⟩ :=
    E.exists_uniformRadius_boundaryBandScores_crossing_max_tendsto_one
      mu hFKG hTI hunique
  obtain ⟨p, family, hp, hp_le⟩ :=
    E.exists_cofinalNormalBoundaryBandFamilies_bounded
      mu hFKG hTI hunique
  refine ⟨radius, p, family, hradius, hp, hp_le, ?_⟩
  intro m
  exact (family m).alignedMarginSchedule E
    (fun _ => E.connectorMarginRequirement (radius m))
    (fun _ => E.connectorMarginRequirement (radius m))




theorem PeriodicPlaneEmbedding.exists_recursiveAlignedSharedLevelSteps_with_limits
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (S : Nat -> Finset V) (p : Nat -> Real)
    (family : forall m, E.NormalBoundaryBandFamily mu (S m) (p m))
    (hp : Tendsto p atTop (nhds 1))
    (hp_le_one : forall m, p m <= 1)
    (verticalRequirement horizontalRequirement : Nat -> Nat -> Nat) :
    let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real)
    exists state : Nat -> Nat × Nat,
      exists steps : forall n, E.AlignedSharedLevelStep mu S p family
        verticalRequirement horizontalRequirement
        (state n).1 (state n).2 (epsilon n) (epsilon n),
      state 0 = (0, 0) /\
      (forall n, state (n + 1) =
        ((steps n).scale + 1, (steps n).nextConnector)) /\
      Tendsto (fun n => (steps n).scale) atTop atTop /\
      Tendsto (fun n => p (steps n).scale) atTop (nhds 1) /\
      Tendsto (fun n => mu.real (E.rectSideConnectionEvent
        (-(steps n).extent : Real) (steps n).extent
        (-(steps n).extent : Real) (steps n).extent
        ((steps n).bottom : Set V)
        (E.rectBottomBoundaryVertices (-(steps n).extent : Real)
          (steps n).extent (-(steps n).extent : Real) (steps n).extent)))
        atTop (nhds 1) /\
      Tendsto (fun n => mu.real (E.rectSideConnectionEvent
        (-(steps n).extent : Real) (steps n).extent
        (-(steps n).extent : Real) (steps n).extent
        ((steps n).top : Set V)
        (E.rectTopBoundaryVertices (-(steps n).extent : Real)
          (steps n).extent (-(steps n).extent : Real) (steps n).extent)))
        atTop (nhds 1) /\
      Tendsto (fun n => mu.real (E.rectSideConnectionEvent
        (-(steps n).extent : Real) (steps n).extent
        (-(steps n).extent : Real) (steps n).extent
        ((steps n).left : Set V)
        (E.rectLeftBoundaryVertices (-(steps n).extent : Real)
          (steps n).extent (-(steps n).extent : Real) (steps n).extent)))
        atTop (nhds 1) /\
      Tendsto (fun n => mu.real (E.rectSideConnectionEvent
        (-(steps n).extent : Real) (steps n).extent
        (-(steps n).extent : Real) (steps n).extent
        ((steps n).right : Set V)
        (E.rectRightBoundaryVertices (-(steps n).extent : Real)
          (steps n).extent (-(steps n).extent : Real) (steps n).extent)))
        atTop (nhds 1) /\
      Tendsto (fun n => mu.real
        (P.pairMergeErrorUnion (steps n).bottom (steps n).top
          (steps n).nextConnector)) atTop (nhds 0) /\
      Tendsto (fun n => mu.real
        (P.pairMergeErrorUnion (steps n).left (steps n).right
          (steps n).nextConnector)) atTop (nhds 0) := by
  dsimp only
  let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real)
  have hepsilon (n : Nat) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  obtain ⟨state, steps, hstate0, hstateSucc⟩ :=
    E.exists_recursiveAlignedSharedLevelSteps mu hTI hunique S p family hp
      verticalRequirement horizontalRequirement epsilon epsilon
      hepsilon hepsilon
  have hstateCofinal : forall n, n <= (state n).1 := by
    intro n
    induction n with
    | zero => simp [hstate0]
    | succ n ih =>
        rw [hstateSucc n]
        exact Nat.succ_le_succ (ih.trans (steps n).scale_ge)
  have hscaleCofinal : forall n, n <= (steps n).scale := fun n =>
    (hstateCofinal n).trans (steps n).scale_ge
  have hscaleTop : Tendsto (fun n => (steps n).scale) atTop atTop := by
    rw [tendsto_atTop]
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hn.trans (hscaleCofinal n)
  have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
    simpa only [epsilon] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  have hscoreLower : Tendsto (fun n => 1 - epsilon n)
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hepsilonZero
  have hscore : Tendsto (fun n => p (steps n).scale)
      atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hscoreLower
      tendsto_const_nhds
      (fun n => le_of_lt (steps n).threshold_gt)
      (fun n => hp_le_one (steps n).scale)
  have hbottom := hscore.squeeze tendsto_const_nhds
    (fun n => le_of_lt (steps n).bottomComponentScore)
    (fun _ => measureReal_le_one)
  have htop := hscore.squeeze tendsto_const_nhds
    (fun n => le_of_lt (steps n).topComponentScore)
    (fun _ => measureReal_le_one)
  have hleft := hscore.squeeze tendsto_const_nhds
    (fun n => le_of_lt (steps n).leftComponentScore)
    (fun _ => measureReal_le_one)
  have hright := hscore.squeeze tendsto_const_nhds
    (fun n => le_of_lt (steps n).rightComponentScore)
    (fun _ => measureReal_le_one)
  have hverticalMerge : Tendsto (fun n => mu.real
      (P.pairMergeErrorUnion (steps n).bottom (steps n).top
        (steps n).nextConnector)) atTop (nhds 0) := by
    apply squeeze_zero
      (fun _ => measureReal_nonneg)
      (fun n => le_of_lt (steps n).verticalMerge)
      hepsilonZero
  have hhorizontalMerge : Tendsto (fun n => mu.real
      (P.pairMergeErrorUnion (steps n).left (steps n).right
        (steps n).nextConnector)) atTop (nhds 0) := by
    apply squeeze_zero
      (fun _ => measureReal_nonneg)
      (fun n => le_of_lt (steps n).horizontalMerge)
      hepsilonZero
  exact ⟨state, steps, hstate0, hstateSucc, hscaleTop, hscore,
    hbottom, htop, hleft, hright, hverticalMerge, hhorizontalMerge⟩




theorem PeriodicPlaneEmbedding.exists_uniformRadius_recursiveAlignedSharedLevelSteps_with_limits
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
    let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real)
    exists (radius : Nat -> Nat) (p : Nat -> Real)
      (family : forall m,
        E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m))
      (state : Nat -> Nat × Nat),
      exists steps : forall n, E.AlignedSharedLevelStep mu
        (fun m => P.orbitBox m) p family
        (fun m _ => E.connectorMarginRequirement (radius m))
        (fun m _ => E.connectorMarginRequirement (radius m))
        (state n).1 (state n).2 (epsilon n) (epsilon n),
      E.UniformBoundaryBandCrossingRadius mu radius /\
      Tendsto p atTop (nhds 1) /\
      (forall m, p m <= 1) /\
      state 0 = (0, 0) /\
      (forall n, state (n + 1) =
        ((steps n).scale + 1, (steps n).nextConnector)) /\
      Tendsto (fun n => (steps n).scale) atTop atTop /\
      Tendsto (fun n => p (steps n).scale) atTop (nhds 1) /\
      Tendsto (fun n => mu.real (E.rectSideConnectionEvent
        (-(steps n).extent : Real) (steps n).extent
        (-(steps n).extent : Real) (steps n).extent
        ((steps n).bottom : Set V)
        (E.rectBottomBoundaryVertices (-(steps n).extent : Real)
          (steps n).extent (-(steps n).extent : Real) (steps n).extent)))
        atTop (nhds 1) /\
      Tendsto (fun n => mu.real (E.rectSideConnectionEvent
        (-(steps n).extent : Real) (steps n).extent
        (-(steps n).extent : Real) (steps n).extent
        ((steps n).top : Set V)
        (E.rectTopBoundaryVertices (-(steps n).extent : Real)
          (steps n).extent (-(steps n).extent : Real) (steps n).extent)))
        atTop (nhds 1) /\
      Tendsto (fun n => mu.real (E.rectSideConnectionEvent
        (-(steps n).extent : Real) (steps n).extent
        (-(steps n).extent : Real) (steps n).extent
        ((steps n).left : Set V)
        (E.rectLeftBoundaryVertices (-(steps n).extent : Real)
          (steps n).extent (-(steps n).extent : Real) (steps n).extent)))
        atTop (nhds 1) /\
      Tendsto (fun n => mu.real (E.rectSideConnectionEvent
        (-(steps n).extent : Real) (steps n).extent
        (-(steps n).extent : Real) (steps n).extent
        ((steps n).right : Set V)
        (E.rectRightBoundaryVertices (-(steps n).extent : Real)
          (steps n).extent (-(steps n).extent : Real) (steps n).extent)))
        atTop (nhds 1) /\
      Tendsto (fun n => mu.real
        (P.pairMergeErrorUnion (steps n).bottom (steps n).top
          (steps n).nextConnector)) atTop (nhds 0) /\
      Tendsto (fun n => mu.real
        (P.pairMergeErrorUnion (steps n).left (steps n).right
          (steps n).nextConnector)) atTop (nhds 0) := by
  dsimp only
  obtain ⟨radius, p, family, hradius, hp, hp_le, _hschedule⟩ :=
    E.exists_uniformBoundaryBandRadius_with_boundedCofinalConnectorSchedule
      mu hFKG hTI hunique
  obtain ⟨state, steps, hstate0, hstateSucc, hscale, hscore,
      hbottom, htop, hleft, hright, hvertical, hhorizontal⟩ :=
    E.exists_recursiveAlignedSharedLevelSteps_with_limits
      mu hTI hunique (fun m => P.orbitBox m) p family hp hp_le
      (fun m _ => E.connectorMarginRequirement (radius m))
      (fun m _ => E.connectorMarginRequirement (radius m))
  exact ⟨radius, p, family, state, steps, hradius, hp, hp_le,
    hstate0, hstateSucc, hscale, hscore, hbottom, htop, hleft, hright,
    hvertical, hhorizontal⟩

end StatMech.FK.PeriodicPlanar
