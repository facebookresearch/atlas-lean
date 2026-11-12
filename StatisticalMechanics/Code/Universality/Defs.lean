/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































import Code.Foundations.ConfigSpace
import Code.Foundations.ProductMeasure
import Code.Inequalities.IncreasingEvent
import Code.Lattice.Clusters
import Code.TwoDim.Crossings

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



def percolationEvent (d : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | (originCluster d ω).Infinite}

@[simp]
theorem mem_percolationEvent {ω : ConfigSpace (Sym2 (Site d))} :
    ω ∈ percolationEvent d ↔ (originCluster d ω).Infinite := Iff.rfl




theorem percolationEvent_increasing : IsIncreasing (percolationEvent d) := by
  intro ω ω' h hω
  exact hω.mono (originCluster_mono h)




noncomputable def percolationProbability (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : ℝ≥0∞ :=
  bernoulliProductMeasure (E := Sym2 (Site d)) p hp (percolationEvent d)




def subcriticalDensities (d : ℕ) : Set ℝ :=
  {p : ℝ | ∃ (hp0 : 0 ≤ p) (hp1 : p ≤ 1),
      percolationProbability d ⟨p, hp0⟩ (by exact_mod_cast hp1) = 0}



noncomputable def criticalProbability (d : ℕ) : ℝ :=
  sSup (subcriticalDensities d)










def PositivelyAssociated {E : Type*} (μ : Measure (ConfigSpace E)) : Prop :=
  ∀ A B : Set (ConfigSpace E), IsIncreasing A → IsIncreasing B →
    μ.real A * μ.real B ≤ μ.real (A ∩ B)


theorem PositivelyAssociated.symm {E : Type*} {μ : Measure (ConfigSpace E)}
    (h : PositivelyAssociated μ) (A B : Set (ConfigSpace E))
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    μ.real B * μ.real A ≤ μ.real (B ∩ A) := by
  rw [mul_comm, Set.inter_comm]
  exact h A B hA hB




theorem PositivelyAssociated.sq_le_self {E : Type*} {μ : Measure (ConfigSpace E)}
    (h : PositivelyAssociated μ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A) :
    μ.real A * μ.real A ≤ μ.real A := by
  have key := h A A hA hA
  rwa [Set.inter_self] at key













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





def translatedHorizontalCrossingEvent (v : Site 2) (a b : ℤ) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  (translateConfig v) ⁻¹' (horizontalCrossingEvent a b)


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







noncomputable def boxCrossingProbabilities (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    (ρ : ℝ) (n0 : ℕ) : Set ℝ :=
  {x : ℝ | ∃ (n : ℕ) (τ : Site 2), n0 ≤ n ∧
      (x = μ.real (translatedHorizontalCrossingEvent τ ⌊ρ * (n : ℝ)⌋ (n : ℤ))
        ∨ x = μ.real (translatedVerticalCrossingEvent τ (n : ℤ) ⌊ρ * (n : ℝ)⌋))}




noncomputable def boxCrossingInf (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    (ρ : ℝ) (n0 : ℕ) : ℝ :=
  sInf (boxCrossingProbabilities μ ρ n0)




def BoxCrossingProperty (μ : Measure (ConfigSpace (Sym2 (Site 2)))) (ρ : ℝ) : Prop :=
  1 < ρ ∧ ∃ n0 : ℕ, 0 < boxCrossingInf μ ρ n0



theorem boxCrossingProperty_iff (μ : Measure (ConfigSpace (Sym2 (Site 2)))) (ρ : ℝ) :
    BoxCrossingProperty μ ρ ↔
      1 < ρ ∧ ∃ n0 : ℕ, 0 < sInf (boxCrossingProbabilities μ ρ n0) :=
  Iff.rfl

end Universality

end StatMech
