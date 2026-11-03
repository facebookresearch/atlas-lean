/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Configuration.ConfigSpace
public import MathlibExt.Probability.Configuration.ProductMeasure
public import MathlibExt.Probability.CorrelationInequalities.IncreasingEvent
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Probability.Percolation.TwoDimensional.Crossings
public import MathlibExt.Probability.Percolation.Theta

/-!
# Positive association, translates of crossing events, and the box-crossing property

Definitions shared by the RSW-type arguments for general (not necessarily product) measures on
bond configurations of `ℤ²`: positive association (the Harris–FKG inequality for increasing
events, taken as a hypothesis on the measure), translates of crossing events, and the
box-crossing property `BoxCrossingProperty μ ρ`: crossing probabilities of all translates of
`ρn × n` and `n × ρn` rectangles are bounded below uniformly in large `n`.

## Main definitions

* `StatMech.Universality.originCluster`, `StatMech.Universality.percolationEvent`,
  `StatMech.Universality.percolationProbability`, `StatMech.Universality.criticalProbability`:
  the cluster of the origin, `{0 ↔ ∞}`, `θ(p)` as an `ℝ≥0∞`, and `p_c` as a real number.
* `StatMech.Universality.PositivelyAssociated`:
  `μ(A) μ(B) ≤ μ(A ∩ B) μ(univ)` for measurable increasing events under a finite measure.
* `StatMech.Universality.translateConfig` and the translated crossing events.
* `StatMech.Universality.boxCrossingInf`, `StatMech.Universality.BoxCrossingProperty`.

## Main results

* `StatMech.Universality.percolationEvent_increasing`.
* `StatMech.Universality.percolationEvent_eq`, `StatMech.Universality.criticalProbability_eq_pc`:
  agreement with `StatMech.Percolation.percolationEvent` and `StatMech.Percolation.pc`.

## References

* V. Tassion, *Crossing probabilities for Voronoi percolation*, Ann. Probab. 44 (2016), 3385–3398.
* H. Duminil-Copin, V. Sidoravicius, V. Tassion, *Continuity of the phase transition for planar
  random-cluster and Potts models with `1 ≤ q ≤ 4`*, Comm. Math. Phys. 349 (2017), 47–107.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim

variable {d : ℕ}

theorem openSubgraph_mono_dim {ω ω' : ConfigSpace (Sym2 (Site d))} (h : ω ≤ ω') :
    openSubgraph d ω ≤ openSubgraph d ω' := by
  intro x y hxy
  refine ⟨hxy.1, ?_⟩
  have hle := h s(x, y)
  rw [hxy.2] at hle
  exact top_le_iff.mp hle

theorem connected_mono_dim {ω ω' : ConfigSpace (Sym2 (Site d))} (h : ω ≤ ω')
    {x y : Site d} (hxy : Connected d ω x y) : Connected d ω' x y :=
  hxy.mono (openSubgraph_mono_dim h)

theorem cluster_mono_dim {ω ω' : ConfigSpace (Sym2 (Site d))} (h : ω ≤ ω')
    (x : Site d) : cluster d ω x ⊆ cluster d ω' x :=
  fun _ hy => connected_mono_dim h hy

/-- The open cluster of the origin of `ℤ^d`. -/
def originCluster (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) : Set (Site d) :=
  cluster d ω (0 : Site d)

@[simp]
theorem mem_originCluster {ω : ConfigSpace (Sym2 (Site d))} {y : Site d} :
    y ∈ originCluster d ω ↔ Connected d ω (0 : Site d) y := Iff.rfl

theorem origin_mem_originCluster (ω : ConfigSpace (Sym2 (Site d))) :
    (0 : Site d) ∈ originCluster d ω :=
  self_mem_cluster ω (0 : Site d)

theorem originCluster_mono {ω ω' : ConfigSpace (Sym2 (Site d))} (h : ω ≤ ω') :
    originCluster d ω ⊆ originCluster d ω' :=
  cluster_mono_dim h (0 : Site d)

/-- The event `{0 ↔ ∞}` that the open cluster of the origin is infinite. -/
def percolationEvent (d : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | (originCluster d ω).Infinite}

@[simp]
theorem mem_percolationEvent {ω : ConfigSpace (Sym2 (Site d))} :
    ω ∈ percolationEvent d ↔ (originCluster d ω).Infinite := Iff.rfl

theorem percolationEvent_increasing : IsIncreasing (percolationEvent d) := by
  intro ω ω' h hω
  exact hω.mono (originCluster_mono h)

/-- The percolation probability `θ_d(p) = ℙ_p(0 ↔ ∞)`, as an extended nonnegative real. -/
noncomputable def percolationProbability (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : ℝ≥0∞ :=
  bernoulliProductMeasure (E := Sym2 (Site d)) p hp (percolationEvent d)

/-- The set of real densities `p ∈ [0, 1]` with `θ_d(p) = 0`. -/
def subcriticalDensities (d : ℕ) : Set ℝ :=
  {p : ℝ | ∃ (hp0 : 0 ≤ p) (hp1 : p ≤ 1),
      percolationProbability d ⟨p, hp0⟩ (by exact_mod_cast hp1) = 0}

/-- The critical probability `p_c(d) = sup {p ∈ [0, 1] : θ_d(p) = 0}` as a real number
(see `criticalProbability_eq_pc`). -/
noncomputable def criticalProbability (d : ℕ) : ℝ :=
  sSup (subcriticalDensities d)

/-- `percolationEvent` is `StatMech.Percolation.percolationEvent`. -/
theorem percolationEvent_eq : percolationEvent d = Percolation.percolationEvent d := rfl

/-- `criticalProbability` is the real-valued form of `StatMech.Percolation.pc`. -/
theorem criticalProbability_eq_pc : criticalProbability d = (Percolation.pc d : ℝ) := by
  unfold criticalProbability Percolation.pc
  rw [NNReal.coe_sSup]
  congr 1
  ext p
  simp only [subcriticalDensities, percolationProbability, Set.mem_image,
    Percolation.mem_subcriticalSet, Percolation.theta, Set.mem_ofPred_eq, percolationEvent_eq]
  constructor
  · rintro ⟨hp0, hp1, h⟩
    have hp1' : (⟨p, hp0⟩ : ℝ≥0) ≤ 1 := by exact_mod_cast hp1
    refine ⟨⟨p, hp0⟩, ⟨hp1', ?_⟩, rfl⟩
    rw [Measure.real, h, ENNReal.toReal_zero]
  · rintro ⟨q, ⟨hq, h⟩, rfl⟩
    refine ⟨q.2, by exact_mod_cast hq, ?_⟩
    have hfin : bernoulliProductMeasure (E := Sym2 (Site d)) q hq
        (Percolation.percolationEvent d) ≠ ⊤ := measure_ne_top _ _
    exact (measureReal_eq_zero_iff hfin).mp h

/-- A finite measure on configurations is positively associated if
`μ(A) μ(B) ≤ μ(A ∩ B) μ(univ)` for all measurable increasing events `A`, `B`. The total-mass
factor makes the Harris--FKG inequality invariant under finite scaling. -/
def PositivelyAssociated {E : Type*} (μ : Measure (ConfigSpace E))
    [IsFiniteMeasure μ] : Prop :=
  ∀ A B : Set (ConfigSpace E), MeasurableSet A → MeasurableSet B →
    IsIncreasing A → IsIncreasing B →
    μ.real A * μ.real B ≤ μ.real (A ∩ B) * μ.real Set.univ

/-- For a probability measure, normalized positive association is the usual Harris--FKG
inequality. -/
theorem positivelyAssociated_iff_of_isProbabilityMeasure {E : Type*}
    (μ : Measure (ConfigSpace E)) [IsProbabilityMeasure μ] :
    PositivelyAssociated μ ↔
      ∀ A B : Set (ConfigSpace E), MeasurableSet A → MeasurableSet B →
        IsIncreasing A → IsIncreasing B → μ.real A * μ.real B ≤ μ.real (A ∩ B) := by
  simp only [PositivelyAssociated, probReal_univ, mul_one]

/-- The usual unnormalized Harris--FKG inequality for a positively associated probability
measure. -/
theorem PositivelyAssociated.probability {E : Type*} {μ : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μ] (h : PositivelyAssociated μ)
    (A B : Set (ConfigSpace E)) (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    μ.real A * μ.real B ≤ μ.real (A ∩ B) :=
  (positivelyAssociated_iff_of_isProbabilityMeasure μ).mp h A B hAm hBm hA hB

theorem PositivelyAssociated.symm {E : Type*} {μ : Measure (ConfigSpace E)}
    [IsFiniteMeasure μ] (h : PositivelyAssociated μ) (A B : Set (ConfigSpace E))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    μ.real B * μ.real A ≤ μ.real (B ∩ A) * μ.real Set.univ := by
  rw [mul_comm, Set.inter_comm]
  exact h A B hAm hBm hA hB

theorem PositivelyAssociated.sq_le_self {E : Type*} {μ : Measure (ConfigSpace E)}
    [IsFiniteMeasure μ] (h : PositivelyAssociated μ)
    (A : Set (ConfigSpace E)) (hAm : MeasurableSet A)
    (hA : IsIncreasing A) :
    μ.real A * μ.real A ≤ μ.real A * μ.real Set.univ := by
  have key := h A A hAm hAm hA hA
  rwa [Set.inter_self] at key

/-- The configuration `ω` translated by `-v`: the state of `e` is the state of `e + v` in `ω`. -/
def translateConfig (v : Site 2) (ω : ConfigSpace (Sym2 (Site 2))) :
    ConfigSpace (Sym2 (Site 2)) :=
  fun e => ω (e.map (· + v))

@[simp]
theorem translateConfig_apply (v : Site 2) (ω : ConfigSpace (Sym2 (Site 2)))
    (e : Sym2 (Site 2)) : translateConfig v ω e = ω (e.map (· + v)) := rfl

@[simp]
theorem translateConfig_zero (ω : ConfigSpace (Sym2 (Site 2))) :
    translateConfig (0 : Site 2) ω = ω := by
  funext e
  simp only [translateConfig, add_zero]
  rw [Sym2.map_id', id]

/-- The event that the rectangle `v + [0, a] × [0, b]` has an open left–right crossing. -/
def translatedHorizontalCrossingEvent (v : Site 2) (a b : ℤ) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  (translateConfig v) ⁻¹' (horizontalCrossingEvent a b)

/-- The event that the rectangle `v + [0, a] × [0, b]` has an open bottom–top crossing. -/
def translatedVerticalCrossingEvent (v : Site 2) (a b : ℤ) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  (translateConfig v) ⁻¹' (verticalCrossingEvent a b)

@[simp]
theorem translatedHorizontalCrossingEvent_zero (a b : ℤ) :
    translatedHorizontalCrossingEvent (0 : Site 2) a b = horizontalCrossingEvent a b := by
  unfold translatedHorizontalCrossingEvent
  have : (translateConfig (0 : Site 2)) = id := funext translateConfig_zero
  rw [this, Set.preimage_id]

@[simp]
theorem translatedVerticalCrossingEvent_zero (a b : ℤ) :
    translatedVerticalCrossingEvent (0 : Site 2) a b = verticalCrossingEvent a b := by
  unfold translatedVerticalCrossingEvent
  have : (translateConfig (0 : Site 2)) = id := funext translateConfig_zero
  rw [this, Set.preimage_id]

/-- The set of crossing probabilities, for `n ≥ n₀` and all translates, of the long direction of
`⌊ρn⌋ × n` and `n × ⌊ρn⌋` rectangles. -/
noncomputable def boxCrossingProbabilities (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    (ρ : ℝ) (n0 : ℕ) : Set ℝ :=
  {x : ℝ | ∃ (n : ℕ) (τ : Site 2), n0 ≤ n ∧
      (x = μ.real (translatedHorizontalCrossingEvent τ ⌊ρ * (n : ℝ)⌋ (n : ℤ))
        ∨ x = μ.real (translatedVerticalCrossingEvent τ (n : ℤ) ⌊ρ * (n : ℝ)⌋))}

/-- The infimum of `boxCrossingProbabilities μ ρ n₀`. -/
noncomputable def boxCrossingInf (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    (ρ : ℝ) (n0 : ℕ) : ℝ :=
  sInf (boxCrossingProbabilities μ ρ n0)

/-- The box-crossing property with aspect ratio `ρ > 1`: for some `n₀`, the probabilities of
crossing all translates of `⌊ρn⌋ × n` rectangles in the long direction, `n ≥ n₀`, are bounded
below by a positive constant. -/
def BoxCrossingProperty (μ : Measure (ConfigSpace (Sym2 (Site 2)))) (ρ : ℝ) : Prop :=
  1 < ρ ∧ ∃ n0 : ℕ, 0 < boxCrossingInf μ ρ n0

theorem boxCrossingProperty_iff (μ : Measure (ConfigSpace (Sym2 (Site 2)))) (ρ : ℝ) :
    BoxCrossingProperty μ ρ ↔
      1 < ρ ∧ ∃ n0 : ℕ, 0 < sInf (boxCrossingProbabilities μ ρ n0) :=
  Iff.rfl

end Universality

end StatMech
