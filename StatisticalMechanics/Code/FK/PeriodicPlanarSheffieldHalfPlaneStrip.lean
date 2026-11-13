/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldHalfPlaneTranslation









open Filter MeasureTheory Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

theorem PeriodicGraph.setConnectionWithin_mono_region
    (P : PeriodicGraph V) {A B : Set V} (hAB : A ⊆ B) (S T : Set V) :
    P.setConnectionWithin A S T ⊆ P.setConnectionWithin B S T := by
  rintro omega ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, y, hy, P.connectedWithinSet_mono_region hAB x y hxy⟩



def PeriodicPlaneEmbedding.rightHalfPlaneStripVertices
    (E : PeriodicPlaneEmbedding P) (r : Real) (n : Nat) : Set V :=
  E.rightHalfPlaneVertices r ∩ {x | E.vertexCoord x 0 ≤ r + n}

theorem PeriodicPlaneEmbedding.rightHalfPlaneStripVertices_subset
    (E : PeriodicPlaneEmbedding P) (r : Real) (n : Nat) :
    E.rightHalfPlaneStripVertices r n ⊆ E.rightHalfPlaneVertices r :=
  fun _ hx => hx.1

theorem PeriodicPlaneEmbedding.rightHalfPlaneStripVertices_mono
    (E : PeriodicPlaneEmbedding P) (r : Real) :
    Monotone (E.rightHalfPlaneStripVertices r) := by
  intro n N hnN x hx
  change x ∈ E.rightHalfPlaneVertices r ∧
    E.vertexCoord x 0 ≤ r + (n : Real) at hx
  change x ∈ E.rightHalfPlaneVertices r ∧
    E.vertexCoord x 0 ≤ r + (N : Real)
  refine ⟨hx.1, ?_⟩
  have hcast : (n : Real) ≤ N := by exact_mod_cast hnN
  linarith


theorem PeriodicPlaneEmbedding.connectedWithin_rightHalfPlane_exists_strip
    (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V))
    (r : Real) (x y : V)
    (hxy : omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) x y) :
    ∃ n : Nat,
      omega ∈ P.connectedWithinSet (E.rightHalfPlaneStripVertices r n) x y := by
  rcases hxy with ⟨l, hchain, hlast, hregion⟩
  let M : Real := ∑ v ∈ (x :: l).toFinset, |E.vertexCoord v 0 - r|
  obtain ⟨n, hn⟩ := exists_nat_ge M
  refine ⟨n, l, hchain, hlast, ?_⟩
  intro v hv
  have hvH := hregion v hv
  refine ⟨hvH, ?_⟩
  have hvfin : v ∈ (x :: l).toFinset := by simpa using hv
  have hterm : |E.vertexCoord v 0 - r| ≤ M := by
    dsimp only [M]
    exact Finset.single_le_sum
      (fun w _hw => abs_nonneg (E.vertexCoord w 0 - r)) hvfin
  have hdiff : E.vertexCoord v 0 - r ≤ M :=
    (le_abs_self (E.vertexCoord v 0 - r)).trans hterm
  change E.vertexCoord v 0 ≤ r + (n : Real)
  linarith

theorem PeriodicPlaneEmbedding.iUnion_connectedWithin_rightHalfPlaneStrip
    (E : PeriodicPlaneEmbedding P) (r : Real) (x y : V) :
    (⋃ n : Nat, P.connectedWithinSet
        (E.rightHalfPlaneStripVertices r n) x y) =
      P.connectedWithinSet (E.rightHalfPlaneVertices r) x y := by
  ext omega
  constructor
  · intro homega
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp homega
    exact P.connectedWithinSet_mono_region
      (E.rightHalfPlaneStripVertices_subset r n) x y hn
  · intro homega
    obtain ⟨n, hn⟩ :=
      E.connectedWithin_rightHalfPlane_exists_strip omega r x y homega
    exact Set.mem_iUnion.2 ⟨n, hn⟩

theorem PeriodicPlaneEmbedding.setConnectionWithin_rightHalfPlaneStrip_mono
    (E : PeriodicPlaneEmbedding P) (r : Real) (S T : Set V) :
    Monotone (fun n : Nat => P.setConnectionWithin
      (E.rightHalfPlaneStripVertices r n) S T) := by
  intro n N hnN
  exact P.setConnectionWithin_mono_region
    (E.rightHalfPlaneStripVertices_mono r hnN) S T

theorem PeriodicPlaneEmbedding.iUnion_setConnectionWithin_rightHalfPlaneStrip
    (E : PeriodicPlaneEmbedding P) (r : Real) (S T : Set V) :
    (⋃ n : Nat, P.setConnectionWithin
        (E.rightHalfPlaneStripVertices r n) S T) =
      P.setConnectionWithin (E.rightHalfPlaneVertices r) S T := by
  ext omega
  constructor
  · intro homega
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp homega
    exact P.setConnectionWithin_mono_region
      (E.rightHalfPlaneStripVertices_subset r n) S T hn
  · rintro ⟨x, hx, y, hy, hxy⟩
    obtain ⟨n, hn⟩ :=
      E.connectedWithin_rightHalfPlane_exists_strip omega r x y hxy
    exact Set.mem_iUnion.2 ⟨n, x, hx, y, hy, hn⟩

theorem PeriodicPlaneEmbedding.rightHalfPlaneStrip_connection_measureReal_tendsto
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r : Real) (S T : Set V) :
    Tendsto (fun n : Nat => mu.real (P.setConnectionWithin
      (E.rightHalfPlaneStripVertices r n) S T)) atTop
      (nhds (mu.real
        (P.setConnectionWithin (E.rightHalfPlaneVertices r) S T))) := by
  have hmeasure := tendsto_measure_iUnion_atTop (μ := mu)
    (E.setConnectionWithin_rightHalfPlaneStrip_mono r S T)
  rw [E.iUnion_setConnectionWithin_rightHalfPlaneStrip r S T] at hmeasure
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure





def PeriodicPlaneEmbedding.halfPlaneStripPairMergeError
    (E : PeriodicPlaneEmbedding P) (r : Real) (n : Nat) (x y : V) :
    Set (ConfigSpace (Sym2 V)) :=
  ({omega | (P.cluster omega x).Infinite} ∩
    {omega | (P.cluster omega y).Infinite}) \
      P.connectedWithinSet (E.rightHalfPlaneStripVertices r n) x y

theorem PeriodicPlaneEmbedding.halfPlaneStripPairMergeError_measurableSet
    (E : PeriodicPlaneEmbedding P) (r : Real) (n : Nat) (x y : V) :
    MeasurableSet (E.halfPlaneStripPairMergeError r n x y) :=
  ((P.measurableSet_cluster_infinite x).inter
    (P.measurableSet_cluster_infinite y)).diff
      (P.connectedWithinSet_measurableSet
        (E.rightHalfPlaneStripVertices r n) x y)

theorem PeriodicPlaneEmbedding.halfPlaneStripPairMergeError_antitone
    (E : PeriodicPlaneEmbedding P) (r : Real) (x y : V) :
    Antitone (fun n => E.halfPlaneStripPairMergeError r n x y) := by
  intro n N hnN omega herror
  refine ⟨herror.1, ?_⟩
  intro hconn
  exact herror.2 (P.connectedWithinSet_mono_region
    (E.rightHalfPlaneStripVertices_mono r hnN) x y hconn)

theorem PeriodicPlaneEmbedding.iInter_halfPlaneStripPairMergeError
    (E : PeriodicPlaneEmbedding P) (r : Real) (x y : V) :
    (⋂ n : Nat, E.halfPlaneStripPairMergeError r n x y) =
      E.halfPlanePairMergeError r x y := by
  ext omega
  simp only [Set.mem_iInter, PeriodicPlaneEmbedding.halfPlaneStripPairMergeError,
    Set.mem_diff, Set.mem_inter_iff, Set.mem_setOf_eq,
    PeriodicPlaneEmbedding.halfPlanePairMergeError]
  constructor
  · intro h
    refine ⟨(h 0).1, ?_⟩
    intro hconn
    rw [← E.iUnion_connectedWithin_rightHalfPlaneStrip r x y] at hconn
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hconn
    exact (h n).2 hn
  · rintro ⟨hinf, hdisc⟩ n
    refine ⟨hinf, ?_⟩
    intro hconn
    exact hdisc (P.connectedWithinSet_mono_region
      (E.rightHalfPlaneStripVertices_subset r n) x y hconn)

theorem PeriodicPlaneEmbedding.halfPlaneStripPairMergeError_measureReal_tendsto
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r : Real) (x y : V) :
    Tendsto (fun n => mu.real (E.halfPlaneStripPairMergeError r n x y))
      atTop (nhds (mu.real (E.halfPlanePairMergeError r x y))) := by
  have hmeasure : Tendsto
      (fun n : Nat => mu (E.halfPlaneStripPairMergeError r n x y)) atTop
      (nhds (mu (⋂ n : Nat, E.halfPlaneStripPairMergeError r n x y))) :=
    tendsto_measure_iInter_atTop
      (fun n => (E.halfPlaneStripPairMergeError_measurableSet r n x y).nullMeasurableSet)
      (E.halfPlaneStripPairMergeError_antitone r x y)
      ⟨0, measure_ne_top mu _⟩
  rw [E.iInter_halfPlaneStripPairMergeError r x y] at hmeasure
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure




theorem PeriodicPlaneEmbedding.exists_shift_stripPairMergeError_measureReal_lt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) (x y : V) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ z : Site 2, ∃ n : Nat,
      mu.real (E.halfPlaneStripPairMergeError r n
        (P.shift z x) (P.shift z y)) < epsilon := by
  obtain ⟨z, hz⟩ :=
    E.exists_shift_halfPlanePairMergeError_measureReal_lt
      mu hTI hunique r x y (half_pos hepsilon)
  have ht := E.halfPlaneStripPairMergeError_measureReal_tendsto
    mu r (P.shift z x) (P.shift z y)
  have hev : ∀ᶠ n in atTop,
      mu.real (E.halfPlaneStripPairMergeError r n
        (P.shift z x) (P.shift z y)) < epsilon :=
    (tendsto_order.1 ht).2 epsilon (hz.trans (half_lt_self hepsilon))
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨z, n, hn⟩

end StatMech.FK.PeriodicPlanar
