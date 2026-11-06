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

/-- **Borsuk covers.** Let $s$ be a set in an extended pseudometric space and let $k$ be a
natural number. The set $s$ has a $k$-piece Borsuk cover if there are $k$ sets whose union
contains $s$, each of extended diameter strictly smaller than that of $s$. -/
def HasBorsukCover {E : Type*} [PseudoEMetricSpace E] (k : ℕ) (s : Set E) : Prop :=
  ∃ c : Fin k → Set E, s ⊆ ⋃ i, c i ∧ ∀ i, ediam (c i) < ediam s

/-- **Borsuk number of a set.** The Borsuk number of a set $s$ in the Euclidean space
$\mathbb{R}^n$ is the least natural number $k$ such that $s$ has a $k$-piece Borsuk cover, that
is, $s$ is covered by $k$ sets each of strictly smaller extended diameter than $s$; it is
$\infty$ if no such $k$ exists. -/
noncomputable def setBorsukNumber {n : ℕ} (s : Set (EuclideanSpace ℝ (Fin n))) : ℕ∞ :=
  ⨅ k : {k : ℕ // HasBorsukCover k s}, (k.val : ℕ∞)

/-- **Borsuk number of a Euclidean space.** For a natural number $n$, the Borsuk number of the
Euclidean space $\mathbb{R}^n$ is the supremum, in $\mathbb{N} \cup \{\infty\}$, of the Borsuk
numbers of the bounded subsets of $\mathbb{R}^n$ with at least two points. -/
noncomputable def dimensionBorsukNumber (n : ℕ) : ℕ∞ :=
  ⨆ s : {s : Set (EuclideanSpace ℝ (Fin n)) // IsBounded s ∧ s.Nontrivial},
    setBorsukNumber s.val

/-- **First Borsuk failure dimension.** The first Borsuk failure dimension is the least positive
integer $n$ such that the Borsuk number of the Euclidean space $\mathbb{R}^n$ is greater than
$n + 1$, and $\infty$ if there is no such $n$. -/
noncomputable def firstBorsukFailureDimension : ℕ∞ :=
  ⨅ n : {n : ℕ // 0 < n ∧ (n + 1 : ℕ∞) < dimensionBorsukNumber n}, (n.val : ℕ∞)

/-- **A Borsuk cover bounds the Borsuk number.** If a set $s$ in the Euclidean space
$\mathbb{R}^n$ has a $k$-piece Borsuk cover for a natural number $k$, then the Borsuk number of
$s$ is at most $k$. -/
theorem setBorsukNumber_le_of_cover {n k : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
    (h : HasBorsukCover k s) : setBorsukNumber s ≤ k :=
  iInf_le_of_le ⟨k, h⟩ le_rfl

/-- **Borsuk covers by subsets.** For natural numbers $n$ and $k$, a set $s$ in the Euclidean
space $\mathbb{R}^n$ has a $k$-piece Borsuk cover if and only if there are subsets
$c_1, \dots, c_k$ of $s$ with $s = c_1 \cup \dots \cup c_k$, each of extended diameter strictly
smaller than that of $s$. -/
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

/-- **Borsuk covers by closed sets.** For natural numbers $n$ and $k$, a set $s$ in the Euclidean
space $\mathbb{R}^n$ has a $k$-piece Borsuk cover if and only if there are $k$ closed subsets of
$\mathbb{R}^n$ whose union contains $s$, each of extended diameter strictly smaller than that
of $s$. -/
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

/-- **Borsuk covers of nonempty sets have at least one piece.** Let $n$ and $k$ be natural
numbers. If a nonempty set $s$ in the Euclidean space $\mathbb{R}^n$ has a $k$-piece Borsuk
cover, then $0 < k$. -/
theorem hasBorsukCover_pos {n k : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : s.Nonempty) (h : HasBorsukCover k s) : 0 < k := by
  by_contra hk
  have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
  obtain ⟨x, hx⟩ := hs
  obtain ⟨c, hc, _⟩ := h
  have hx' : x ∈ ⋃ i, c i := hc hx
  simp [hk0] at hx'

/-- **Enlarging a Borsuk cover.** Let $n$, $k$ and $l$ be natural numbers with $k \le l$. If a
nonempty set $s$ in the Euclidean space $\mathbb{R}^n$ has a $k$-piece Borsuk cover, then $s$ has
an $l$-piece Borsuk cover.

Repeating an existing piece enlarges the cover to the larger size. -/
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

/-- **Bounds on the Borsuk number of a set.** For a nonempty set $s$ in the Euclidean space
$\mathbb{R}^n$ and a natural number $k$, the Borsuk number of $s$ is at most $k$ if and only if
$s$ has a $k$-piece Borsuk cover. -/
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

/-- **Upper bounds on the Borsuk number of a Euclidean space.** For natural numbers $n$ and $k$,
the Borsuk number of the Euclidean space $\mathbb{R}^n$ is at most $k$ if and only if every
bounded subset $s$ of $\mathbb{R}^n$ with at least two points has a $k$-piece Borsuk cover,
that is, $s$ is covered by $k$ sets, each of extended diameter strictly smaller than that of
$s$. -/
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

/-- **Borsuk's conjecture in a given dimension.** For a natural number $n$, Borsuk's conjecture
in dimension $n$ is the statement that the Borsuk number of the Euclidean space $\mathbb{R}^n$
is at most $n + 1$.

Equivalently, every bounded subset of $\mathbb{R}^n$ with at least two points is covered by
$n + 1$ sets, each of extended diameter strictly smaller than that of the set. -/
def borsukConjectureInDimension (n : ℕ) : Prop := dimensionBorsukNumber n ≤ (n + 1 : ℕ∞)

/-- **When the first Borsuk failure dimension is infinite.** The first Borsuk failure dimension
is $\infty$ if and only if, for every positive integer $n$, the Borsuk number of the Euclidean
space $\mathbb{R}^n$ is at most $n + 1$. -/
theorem firstBorsukFailureDimension_eq_top_iff : firstBorsukFailureDimension = ⊤ ↔
    ∀ n : ℕ, 0 < n → dimensionBorsukNumber n ≤ (n + 1 : ℕ∞) := by
  rw [firstBorsukFailureDimension, ENat.iInf_natCast_eq_top]
  constructor
  · intro h n hn
    by_contra hf
    exact h.false ⟨n, hn, lt_of_not_ge hf⟩
  · intro h
    exact ⟨fun n => (not_lt_of_ge (h n.val n.prop.1)) n.prop.2⟩

/-- **Two-distance sets.** A set $s$ in the Euclidean space $\mathbb{R}^n$ is a two-distance set
if there are reals $0 < a < b$ such that the distance between any two distinct points of $s$ is
$a$ or $b$, and both $a$ and $b$ occur as the distance between some two points of $s$. -/
def IsTwoDistanceSet {n : ℕ} (s : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ a < b ∧
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → dist x y = a ∨ dist x y = b) ∧
    (∃ x ∈ s, ∃ y ∈ s, dist x y = a) ∧
    ∃ x ∈ s, ∃ y ∈ s, dist x y = b

/-- **Two-distance Borsuk number in dimension $n$.** The two-distance Borsuk number in dimension
$n$ is the supremum, taken in $\mathbb{N} \cup \{\infty\}$, of the Borsuk numbers of all bounded
two-distance sets with at least two points in the Euclidean space $\mathbb{R}^n$. -/
noncomputable def twoDistanceBorsukNumber (n : ℕ) : ℕ∞ :=
  ⨆ s : {s : Set (EuclideanSpace ℝ (Fin n)) //
      Bornology.IsBounded s ∧ s.Nontrivial ∧ IsTwoDistanceSet s}, setBorsukNumber s.val

end Metric
