/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































import Code.Foundations.ConfigSpace
import Code.Foundations.ProductMeasure
import Code.Inequalities.IncreasingEvent
import Code.Inequalities.Harris
import Code.Lattice.Clusters
import Code.TwoDim.Crossings
import Code.Universality.Defs

open MeasureTheory Set
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim

variable {d : ℕ}










def g3OriginCluster (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) : Set (Site d) :=
  originCluster d ω

theorem g3OriginCluster_eq (ω : ConfigSpace (Sym2 (Site d))) :
    g3OriginCluster d ω = originCluster d ω := rfl


theorem origin_mem_g3OriginCluster (ω : ConfigSpace (Sym2 (Site d))) :
    (0 : Site d) ∈ g3OriginCluster d ω :=
  origin_mem_originCluster ω



theorem g3OriginCluster_mono {ω ω' : ConfigSpace (Sym2 (Site d))} (h : ω ≤ ω') :
    g3OriginCluster d ω ⊆ g3OriginCluster d ω' :=
  originCluster_mono h



def g3PercolationEvent (d : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  percolationEvent d

theorem g3PercolationEvent_eq : g3PercolationEvent d = percolationEvent d := rfl

theorem mem_g3PercolationEvent {ω : ConfigSpace (Sym2 (Site d))} :
    ω ∈ g3PercolationEvent d ↔ (g3OriginCluster d ω).Infinite := Iff.rfl



theorem g3PercolationEvent_increasing : IsIncreasing (g3PercolationEvent d) :=
  percolationEvent_increasing



noncomputable def g3PercolationProbability (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : ℝ≥0∞ :=
  percolationProbability d p hp

theorem g3PercolationProbability_eq (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    g3PercolationProbability d p hp = percolationProbability d p hp := rfl



def g3SubcriticalDensities (d : ℕ) : Set ℝ :=
  subcriticalDensities d

theorem g3SubcriticalDensities_eq : g3SubcriticalDensities d = subcriticalDensities d :=
  rfl





noncomputable def g3CriticalProbability (d : ℕ) : ℝ :=
  sSup (g3SubcriticalDensities d)



theorem g3CriticalProbability_eq (d : ℕ) :
    g3CriticalProbability d = criticalProbability d := rfl










def G3PositivelyAssociated {E : Type*} (μ : Measure (ConfigSpace E)) : Prop :=
  ∀ A B : Set (ConfigSpace E), IsIncreasing A → IsIncreasing B →
    μ.real A * μ.real B ≤ μ.real (A ∩ B)



theorem G3PositivelyAssociated_iff {E : Type*} (μ : Measure (ConfigSpace E)) :
    G3PositivelyAssociated μ ↔ PositivelyAssociated μ := Iff.rfl



theorem G3PositivelyAssociated.symm {E : Type*} {μ : Measure (ConfigSpace E)}
    (h : G3PositivelyAssociated μ) (A B : Set (ConfigSpace E))
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    μ.real B * μ.real A ≤ μ.real (B ∩ A) :=
  PositivelyAssociated.symm (G3PositivelyAssociated_iff μ |>.mp h) A B hA hB



theorem G3PositivelyAssociated.sq_le_self {E : Type*} {μ : Measure (ConfigSpace E)}
    (h : G3PositivelyAssociated μ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A) :
    μ.real A * μ.real A ≤ μ.real A :=
  PositivelyAssociated.sq_le_self (G3PositivelyAssociated_iff μ |>.mp h) A hA







theorem bernoulli_g3PositivelyAssociated {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ≥0} (hp : p ≤ 1) :
    G3PositivelyAssociated (bernoulliProductMeasure (E := E) p hp) :=
  fun _ _ hA hB => harris_inequality hp hA hB












noncomputable def g3BoxCrossingProbabilities
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) (ρ : ℝ) (n0 : ℕ) : Set ℝ :=
  boxCrossingProbabilities μ ρ n0

theorem g3BoxCrossingProbabilities_eq
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) (ρ : ℝ) (n0 : ℕ) :
    g3BoxCrossingProbabilities μ ρ n0 = boxCrossingProbabilities μ ρ n0 := rfl



noncomputable def g3BoxCrossingInf
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) (ρ : ℝ) (n0 : ℕ) : ℝ :=
  boxCrossingInf μ ρ n0

theorem g3BoxCrossingInf_eq
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) (ρ : ℝ) (n0 : ℕ) :
    g3BoxCrossingInf μ ρ n0 = sInf (g3BoxCrossingProbabilities μ ρ n0) := rfl





def G3BoxCrossingProperty (μ : Measure (ConfigSpace (Sym2 (Site 2)))) (ρ : ℝ) : Prop :=
  1 < ρ ∧ ∃ n0 : ℕ, 0 < g3BoxCrossingInf μ ρ n0



theorem G3BoxCrossingProperty_iff (μ : Measure (ConfigSpace (Sym2 (Site 2)))) (ρ : ℝ) :
    G3BoxCrossingProperty μ ρ ↔ BoxCrossingProperty μ ρ := Iff.rfl



theorem G3BoxCrossingProperty.one_lt {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
    {ρ : ℝ} (h : G3BoxCrossingProperty μ ρ) : 1 < ρ :=
  h.1



theorem G3BoxCrossingProperty.exists_pos_inf
    {μ : Measure (ConfigSpace (Sym2 (Site 2)))} {ρ : ℝ}
    (h : G3BoxCrossingProperty μ ρ) :
    ∃ n0 : ℕ, 0 < g3BoxCrossingInf μ ρ n0 :=
  h.2

end Universality

end StatMech
