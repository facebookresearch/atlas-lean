/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Borsuk covers and Euclidean Borsuk numbers
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.EMetricSpace.Diam
public import Mathlib.Data.Set.Card

@[expose] public section

namespace Metric

open Bornology

/-- A set has a `k`-piece Borsuk cover if it is covered by `k` sets, each of strictly
smaller extended diameter. -/
def HasBorsukCover {E : Type*} [PseudoEMetricSpace E] (k : ℕ) (s : Set E) : Prop :=
  ∃ c : Fin k → Set E, s ⊆ ⋃ i, c i ∧ ∀ i, ediam (c i) < ediam s

/-- Least number of strictly smaller-diameter pieces, with infinity if no finite cover exists. -/
noncomputable def setBorsukNumber {n : ℕ} (s : Set (EuclideanSpace ℝ (Fin n))) : ℕ∞ :=
  ⨅ k : {k : ℕ // HasBorsukCover k s}, (k.val : ℕ∞)

/-- The supremum of set Borsuk numbers over bounded sets with at least two points. -/
noncomputable def dimensionBorsukNumber (n : ℕ) : ℕ∞ :=
  ⨆ s : {s : Set (EuclideanSpace ℝ (Fin n)) // IsBounded s ∧ s.Nontrivial},
    setBorsukNumber s.val

/-- Least positive dimension where Borsuk's partition bound fails, or infinity if none does. -/
noncomputable def firstBorsukFailureDimension : ℕ∞ :=
  ⨅ n : {n : ℕ // 0 < n ∧ (n + 1 : ℕ∞) < dimensionBorsukNumber n}, (n.val : ℕ∞)

/-- Every actual finite cover bounds the set's least partition number. -/
theorem setBorsukNumber_le_of_cover {n k : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
    (h : HasBorsukCover k s) : setBorsukNumber s ≤ k :=
  iInf_le_of_le ⟨k, h⟩ le_rfl

/-- Canonical covers can be intersected with the original set to give an exact union. -/
theorem hasBorsukCover_iff_exactUnion {n k : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))} :
    HasBorsukCover k s ↔ ∃ c : Fin k → Set (EuclideanSpace ℝ (Fin n)),
      (∀ i, c i ⊆ s) ∧ s = ⋃ i, c i ∧ ∀ i, ediam (c i) < ediam s := by
  constructor
  · rintro ⟨c, hs, hc⟩
    refine ⟨fun i => s ∩ c i, fun _ => Set.inter_subset_left, ?_, ?_⟩
    · ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs hx)
        exact ⟨i, hx, hi⟩
      · rintro ⟨i, hx, _⟩
        exact hx
    · intro i
      exact lt_of_le_of_lt (ediam_mono Set.inter_subset_right) (hc i)
  · rintro ⟨c, _, rfl, hc⟩
    exact ⟨c, Set.Subset.rfl, hc⟩

/-- The primary's closed ambient covering pieces give the same strict-diameter cover law. -/
theorem hasBorsukCover_iff_closedCover {n k : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))} :
    HasBorsukCover k s ↔ ∃ c : Fin k → Set (EuclideanSpace ℝ (Fin n)),
      s ⊆ ⋃ i, c i ∧ ∀ i, IsClosed (c i) ∧ ediam (c i) < ediam s := by
  constructor
  · rintro ⟨c, hc, hd⟩
    refine ⟨fun i => closure (c i), ?_, fun i => ⟨isClosed_closure, ?_⟩⟩
    · intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hc hx)
      exact Set.mem_iUnion.mpr ⟨i, subset_closure hi⟩
    · simpa only [ediam_closure] using hd i
  · rintro ⟨c, hc, hd⟩
    exact ⟨c, hc, fun i => (hd i).2⟩

/-- A nonempty set cannot have a zero-member cover. -/
theorem hasBorsukCover_pos {n k : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : s.Nonempty) (h : HasBorsukCover k s) : 0 < k := by
  by_contra hk
  have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
  obtain ⟨x, hx⟩ := hs
  obtain ⟨c, hc, _⟩ := h
  have hx' : x ∈ ⋃ i, c i := hc hx
  simp [hk0] at hx'

/-- Repeating an existing piece enlarges a nonempty set's cover to any greater size. -/
theorem hasBorsukCover_mono {n k l : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : s.Nonempty) (h : HasBorsukCover k s) (hkl : k ≤ l) : HasBorsukCover l s := by
  classical
  have hk := hasBorsukCover_pos hs h
  obtain ⟨c, hc, hd⟩ := h
  let c' : Fin l → Set (EuclideanSpace ℝ (Fin n)) :=
    fun i => if hi : i.val < k then c ⟨i.val, hi⟩ else c ⟨0, hk⟩
  refine ⟨c', ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hc hx)
    refine Set.mem_iUnion.mpr ⟨Fin.castLE hkl i, ?_⟩
    simpa [c', i.isLt] using hi
  · intro i
    dsimp [c']
    split <;> apply hd

/-- For a nonempty set, an upper bound on its least number is equivalent to an actual cover. -/
theorem setBorsukNumber_le_iff {n k : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : s.Nonempty) : setBorsukNumber s ≤ k ↔ HasBorsukCover k s := by
  constructor
  · intro h
    have hf : setBorsukNumber s < ⊤ := lt_of_le_of_lt h (by simp)
    have : Nonempty {m : ℕ // HasBorsukCover m s} :=
      (ENat.iInf_natCast_lt_top (f := fun m : {m : ℕ // HasBorsukCover m s} => m.val)).mp hf
    obtain ⟨m, hm⟩ := ENat.exists_eq_iInf
      (fun m : {m : ℕ // HasBorsukCover m s} => (m.val : ℕ∞))
    have hmle : m.val ≤ k := by
      exact_mod_cast hm.trans_le h
    exact hasBorsukCover_mono hs m.prop hmle
  · exact setBorsukNumber_le_of_cover

/-- A dimensional upper bound is exactly the universal canonical smaller-diameter cover law. -/
theorem dimensionBorsukNumber_le_iff {n k : ℕ} : dimensionBorsukNumber n ≤ k ↔
    ∀ s : Set (EuclideanSpace ℝ (Fin n)),
      IsBounded s → s.Nontrivial → HasBorsukCover k s := by
  constructor
  · intro h s hb hn
    apply (setBorsukNumber_le_iff hn.nonempty).mp
    exact (le_iSup_of_le ⟨s, hb, hn⟩ le_rfl).trans h
  · intro h
    apply iSup_le
    intro s
    exact setBorsukNumber_le_of_cover (h s.val s.prop.1 s.prop.2)

/-- Borsuk's partition bound in one Euclidean dimension. -/
def borsukConjectureInDimension (n : ℕ) : Prop := dimensionBorsukNumber n ≤ (n + 1 : ℕ∞)

/-- The source's infinity convention holds exactly when no positive dimension fails. -/
theorem firstBorsukFailureDimension_eq_top_iff : firstBorsukFailureDimension = ⊤ ↔
    ∀ n : ℕ, 0 < n → dimensionBorsukNumber n ≤ (n + 1 : ℕ∞) := by
  rw [firstBorsukFailureDimension, ENat.iInf_natCast_eq_top]
  constructor
  · intro h n hn
    by_contra hf
    exact h.false ⟨n, hn, lt_of_not_ge hf⟩
  · intro h
    exact ⟨fun n => (not_lt_of_ge (h n.val n.prop.1)) n.prop.2⟩

/-- A set's distances between distinct points have exactly two positive values. -/
def IsTwoDistanceSet {n : ℕ} (s : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ a < b ∧
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → dist x y = a ∨ dist x y = b) ∧
    (∃ x ∈ s, ∃ y ∈ s, dist x y = a) ∧
    ∃ x ∈ s, ∃ y ∈ s, dist x y = b

/-- The dimensional Borsuk supremum restricted to two-distance sets. -/
noncomputable def twoDistanceBorsukNumber (n : ℕ) : ℕ∞ :=
  ⨆ s : {s : Set (EuclideanSpace ℝ (Fin n)) //
      Bornology.IsBounded s ∧ s.Nontrivial ∧ IsTwoDistanceSet s}, setBorsukNumber s.val

end Metric
