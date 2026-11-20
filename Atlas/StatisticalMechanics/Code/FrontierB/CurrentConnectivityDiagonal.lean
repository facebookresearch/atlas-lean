/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierB.CurrentConnectivityApproximation

open Filter MeasureTheory Set Topology

namespace StatMech.FrontierB

open Lattice

variable {d : ℕ}


def currentPairTraceBoxGate
    (Q : Set (ConfigSpace (Sym2 (Site d)))) (n : ℕ) (x y : Site d) :
    Set (InfiniteCurrentConfig (Sym2 (Site d)) ×
      InfiniteCurrentConfig (Sym2 (Site d))) :=
  superposedCurrentTrace ⁻¹' (Q ∩ boxConnectionEvent n x y)


def currentPairTraceConnectionGate
    (Q : Set (ConfigSpace (Sym2 (Site d)))) (x y : Site d) :
    Set (InfiniteCurrentConfig (Sym2 (Site d)) ×
      InfiniteCurrentConfig (Sym2 (Site d))) :=
  superposedCurrentTrace ⁻¹' (Q ∩ {omega | Connected d omega x y})

theorem currentPairTraceBoxGate_mono
    (Q : Set (ConfigSpace (Sym2 (Site d)))) (x y : Site d) :
    Monotone (fun n => currentPairTraceBoxGate Q n x y) := by
  intro m n hmn p hp
  exact ⟨hp.1, boxConnectionEvent_mono x y hmn hp.2⟩

theorem iUnion_currentPairTraceBoxGate
    (Q : Set (ConfigSpace (Sym2 (Site d)))) (x y : Site d) :
    (⋃ n, currentPairTraceBoxGate Q n x y) =
      currentPairTraceConnectionGate Q x y := by
  ext p
  simp only [Set.mem_iUnion, currentPairTraceBoxGate,
    currentPairTraceConnectionGate, Set.mem_preimage, Set.mem_inter_iff,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hQ, hn⟩
    exact ⟨hQ, (mem_iUnion_boxConnectionEvent_iff_connected
      (superposedCurrentTrace p) x y).mp (Set.mem_iUnion.mpr ⟨n, hn⟩)⟩
  · rintro ⟨hQ, hconn⟩
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp
      ((mem_iUnion_boxConnectionEvent_iff_connected
        (superposedCurrentTrace p) x y).mpr hconn)
    exact ⟨n, hQ, hn⟩

theorem isClopen_currentPairTraceBoxGate
    {Q : Set (ConfigSpace (Sym2 (Site d)))} (hQ : IsClopen Q)
    (n : ℕ) (x y : Site d) :
    IsClopen (currentPairTraceBoxGate Q n x y) :=
  (hQ.inter (isClopen_boxConnectionEvent n x y)).preimage
    continuous_superposedCurrentTrace




def CurrentPairConnectivityNoEscape
    (mu nu : ℕ → ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))))
    (Q : Set (ConfigSpace (Sym2 (Site d)))) (x y : Site d) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ M : ℕ, ∀ m, M ≤ m →
    ∀ᶠ k in atTop,
      ((mu k).prod (nu k) : Measure _).real
        (currentPairTraceBoxGate Q k x y \
          currentPairTraceBoxGate Q m x y) < epsilon



theorem currentPairTraceBoxGate_diagonal_tendsto
    {mu nu : ℕ → ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {muLim nuLim : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    (hmu : WeakCurrentConverges mu muLim)
    (hnu : WeakCurrentConverges nu nuLim)
    {Q : Set (ConfigSpace (Sym2 (Site d)))} (hQ : IsClopen Q)
    (x y : Site d)
    (hno : CurrentPairConnectivityNoEscape mu nu Q x y) :
    Tendsto
      (fun k => ((mu k).prod (nu k) : Measure _).real
        (currentPairTraceBoxGate Q k x y)) atTop
      (nhds ((muLim.prod nuLim : Measure _).real
        (currentPairTraceConnectionGate Q x y))) := by
  have hlimit : Tendsto
      (fun m => (muLim.prod nuLim : Measure _).real
        (currentPairTraceBoxGate Q m x y)) atTop
      (nhds ((muLim.prod nuLim : Measure _).real
        (currentPairTraceConnectionGate Q x y))) := by
    have h := currentPairBoxConnectionEvent_inter_real_tendsto muLim nuLim
      (superposedCurrentTrace ⁻¹' Q) x y
    simpa only [currentPairTraceBoxGate, currentPairTraceConnectionGate,
      currentPairBoxConnectionEvent, currentPairConnectionEvent,
      Set.preimage_inter] using h
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  let delta := epsilon / 4
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hfour : 4 * delta = epsilon := by dsimp [delta]; ring
  obtain ⟨Nlim, hNlim⟩ :=
    (Metric.tendsto_atTop.mp hlimit) delta hdelta
  obtain ⟨M, hM⟩ := hno delta hdelta
  let m := max M Nlim
  have hmM : M ≤ m := le_max_left _ _
  have hmNlim : Nlim ≤ m := le_max_right _ _
  have hlimClose := hNlim m hmNlim
  have hfixed : Tendsto
      (fun k => ((mu k).prod (nu k) : Measure _).real
        (currentPairTraceBoxGate Q m x y)) atTop
      (nhds ((muLim.prod nuLim : Measure _).real
        (currentPairTraceBoxGate Q m x y))) := by
    simpa only [currentPairTraceBoxGate] using
      (hmu.pairBoxConnectionEvent_inter_trace_real hnu hQ m x y)
  obtain ⟨Nfixed, hNfixed⟩ :=
    (Metric.tendsto_atTop.mp hfixed) delta hdelta
  obtain ⟨Nescape, hNescape⟩ := (Filter.eventually_atTop.1 (hM m hmM))
  refine ⟨max m (max Nfixed Nescape), fun k hk => ?_⟩
  have hmk : m ≤ k := le_trans (le_max_left _ _) hk
  have hNfixedk : Nfixed ≤ k :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hk)
  have hNescapek : Nescape ≤ k :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hk)
  have hfixedClose := hNfixed k hNfixedk
  have hescape := hNescape k hNescapek
  have hsubset : currentPairTraceBoxGate Q m x y ⊆
      currentPairTraceBoxGate Q k x y :=
    currentPairTraceBoxGate_mono Q x y hmk
  have hlower : ((mu k).prod (nu k) : Measure _).real
      (currentPairTraceBoxGate Q m x y) ≤
        ((mu k).prod (nu k) : Measure _).real
          (currentPairTraceBoxGate Q k x y) :=
    measureReal_mono hsubset (by finiteness)
  have hdiff : ((mu k).prod (nu k) : Measure _).real
        (currentPairTraceBoxGate Q k x y) -
      ((mu k).prod (nu k) : Measure _).real
        (currentPairTraceBoxGate Q m x y) ≤
      ((mu k).prod (nu k) : Measure _).real
        (currentPairTraceBoxGate Q k x y \
          currentPairTraceBoxGate Q m x y) :=
    le_measureReal_diff
  rw [Real.dist_eq, abs_lt] at hfixedClose hlimClose ⊢
  constructor <;> linarith

end StatMech.FrontierB
