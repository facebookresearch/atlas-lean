/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.RectanglePreference

/-!
# Crossing limits from preference witnesses and uniform merge radii

A translated orbit box that prefers the bottom and left sides, next to boxes preferring the
opposite sides, forces a crossing of the rectangle; with merge radii chosen uniformly, the larger
of the vertical and horizontal crossing probabilities tends to one.

## i. Overview

`preferenceKingOffset ij` lists the nine king-move offsets `{-1, 0, 1}²`; every king neighbour
of a site is reached by one of them. A preference witness is a site `x` whose translated orbit
box prefers bottom to top and left to right, together with neighbours `xVertical` and
`xHorizontal` whose boxes prefer top to bottom and right to left. By the fourth-root bound and
the preferred-side transfer (from `RectanglePreference`), the larger `A` of the bottom and left
connection probabilities of the box at `x` is at least `1 - (1 - μ(box hits ∞))^{1/4}`, and
either the vertical or the horizontal crossing probability is at least `A (H A - M) - M`.

Under almost sure uniqueness of the infinite cluster, ball merge errors tend to zero, so one can
choose radii `radius n ≥ n` with merge errors below `1/(n+1)`, simultaneously for two targets or
for a finite family of targets; translation invariance carries this to translated rectangles.
Combining these, for rectangles containing the buffered ball of the chosen radius around the
witness, `max (vertical crossing) (horizontal crossing) → 1`.

Headline fidelity: `exists_connectorRadius_crossing_max_tendsto_one` and
`exists_uniform_connectorRadius_crossing_max_tendsto_one` are proved conditionally on FKG,
translation invariance and almost sure uniqueness of the infinite cluster, and on the
preference-witness inequalities given as hypotheses.
`PeriodicGraph.exists_uniform_pairMergeRadius` carries instance arguments
`[Fintype ι] [DecidableEq ι]` that its type does not use; they are kept because removing them
changes the statement.

## ii. Key results

- `PeriodicPlaneEmbedding.crossing_branch_of_preference_witness`
- `PeriodicGraph.exists_uniform_pairMergeRadius`
- `PeriodicPlaneEmbedding.exists_uniform_kingOffset_mergeError_tendsto_zero`
- `PeriodicPlaneEmbedding.exists_uniform_connectorRadius_crossing_max_tendsto_one`

## iii. Table of contents

- A. King offsets
- B. Crossings from a preference witness
- C. Uniform merge radii
- D. Crossing limits

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
-/

@[expose] public section

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

/-! ## A. King offsets -/

/-- The king-move offset `(i - 1, j - 1) ∈ {-1, 0, 1}²` indexed by `(i, j) : Fin 3 × Fin 3`. -/
def preferenceKingOffset (ij : Fin 3 × Fin 3) : Site 2 := fun k =>
  if k = 0 then (ij.1.val : Int) - 1 else (ij.2.val : Int) - 1

/-- Every king neighbour `y` of `x` is `x + preferenceKingOffset ij` for some index `ij`. -/
lemma exists_preferenceKingOffset_of_kingAdj {x y : Site 2}
    (hxy : KingAdj x y) :
    ∃ ij : Fin 3 × Fin 3, y = x + preferenceKingOffset ij := by
  have hcoord (k : Fin 2) : -1 ≤ y k - x k ∧ y k - x k ≤ 1 := by
    have h := hxy.2 k
    have hsquare : (x k - y k) * (x k - y k) ≤ (1 : Int) * 1 :=
      (Int.natAbs_le_iff_mul_self_le (a := x k - y k) (b := 1)).mp
        (by simpa using h)
    constructor <;> nlinarith
  let i : Fin 3 := ⟨(y 0 - x 0 + 1).toNat, by
    have h := hcoord 0
    omega⟩
  let j : Fin 3 := ⟨(y 1 - x 1 + 1).toNat, by
    have h := hcoord 1
    omega⟩
  refine ⟨(i, j), ?_⟩
  funext k
  fin_cases k
  · have hn : 0 ≤ y 0 - x 0 + 1 := by have h := hcoord 0; omega
    have hc : ((y 0 - x 0 + 1).toNat : Int) = y 0 - x 0 + 1 :=
      Int.toNat_of_nonneg hn
    simp [preferenceKingOffset, i, hc]
  · have hn : 0 ≤ y 1 - x 1 + 1 := by have h := hcoord 1; omega
    have hc : ((y 1 - x 1 + 1).toNat : Int) = y 1 - x 1 + 1 :=
      Int.toNat_of_nonneg hn
    simp [preferenceKingOffset, j, hc]

/-! ## B. Crossings from a preference witness -/

/-- For a preference witness `x` (box preferring bottom and left) with neighbours `xVertical`
(preferring top) and `xHorizontal` (preferring right), the larger `A` of the bottom and left
connection probabilities of the box at `x` satisfies the fourth-root bound, and the vertical or the
horizontal crossing probability is at least the corresponding transfer bound `A (H A - M) - M`. -/
lemma PeriodicPlaneEmbedding.crossing_branch_of_preference_witness
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (N : Nat) (a b c d : Real) (x xVertical xHorizontal : Site 2)
    (hbox : ((P.orbitBox N).image (P.shift x) : Set V) ⊆
      E.rectVertices a b c d)
    (hBottomTop :
      mu.real (E.rectSideConnectionEvent a b c d
        ((P.orbitBox N).image (P.shift x) : Set V)
        (E.rectTopBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d
        ((P.orbitBox N).image (P.shift x) : Set V)
        (E.rectBottomBoundaryVertices a b c d)))
    (hLeftRight :
      mu.real (E.rectSideConnectionEvent a b c d
        ((P.orbitBox N).image (P.shift x) : Set V)
        (E.rectRightBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d
        ((P.orbitBox N).image (P.shift x) : Set V)
        (E.rectLeftBoundaryVertices a b c d)))
    (hVerticalOpposite :
      mu.real (E.rectSideConnectionEvent a b c d
        ((P.orbitBox N).image (P.shift xVertical) : Set V)
        (E.rectBottomBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d
        ((P.orbitBox N).image (P.shift xVertical) : Set V)
        (E.rectTopBoundaryVertices a b c d)))
    (hHorizontalOpposite :
      mu.real (E.rectSideConnectionEvent a b c d
        ((P.orbitBox N).image (P.shift xHorizontal) : Set V)
        (E.rectLeftBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d
        ((P.orbitBox N).image (P.shift xHorizontal) : Set V)
        (E.rectRightBoundaryVertices a b c d))) :
    let L := (P.orbitBox N).image (P.shift x)
    let RV := (P.orbitBox N).image (P.shift xVertical)
    let RH := (P.orbitBox N).image (P.shift xHorizontal)
    let Ab := mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
      (E.rectBottomBoundaryVertices a b c d))
    let Al := mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
      (E.rectLeftBoundaryVertices a b c d))
    let A := max Ab Al
    let Hv := mu.real (P.setHitsInfinite (RV : Set V))
    let Hh := mu.real (P.setHitsInfinite (RH : Set V))
    let Mv := mu.real (E.rectanglePairMergeErrorUnion a b c d L RV)
    let Mh := mu.real (E.rectanglePairMergeErrorUnion a b c d L RH)
    1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.orbitBoxHitsInfinite N))) ≤ A ∧
      (A * (Hv * A - Mv) - Mv ≤
          mu.real (E.verticalCrossingEvent a b c d) ∨
        A * (Hh * A - Mh) - Mh ≤
          mu.real (E.horizontalCrossingEvent a b c d)) := by
  classical
  dsimp only
  let L := (P.orbitBox N).image (P.shift x)
  let RV := (P.orbitBox N).image (P.shift xVertical)
  let RH := (P.orbitBox N).image (P.shift xHorizontal)
  let Ab := mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
    (E.rectBottomBoundaryVertices a b c d))
  let Al := mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
    (E.rectLeftBoundaryVertices a b c d))
  have hLset : (L : Set V) =
      P.shift x '' (P.orbitBox N : Set V) := by
    ext v
    simp [L]
  have hpreferred :
      1 - Real.sqrt (Real.sqrt
          (1 - mu.real (P.orbitBoxHitsInfinite N))) ≤ max Ab Al := by
    have h := E.preference_max_bottom_left_ge_fourthRoot
      mu hFKG a b c d (L : Set V) (by simpa [L] using hbox)
      (by simpa [L, Ab] using hBottomTop)
      (by simpa [L, Al] using hLeftRight)
    calc
      1 - Real.sqrt (Real.sqrt
          (1 - mu.real (P.orbitBoxHitsInfinite N))) =
          1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (L : Set V)))) := by
              rw [hLset, P.setHitsInfinite_translate_measureReal_eq mu hTI x,
                P.setHitsInfinite_orbitBox]
      _ ≤ max Ab Al := by simpa [Ab, Al] using h
  refine ⟨hpreferred, ?_⟩
  by_cases hle : Al ≤ Ab
  · left
    have htransfer := E.verticalCrossing_ge_preferredSide_transfer
      mu hFKG a b c d L RV (by simpa [RV] using hVerticalOpposite)
    change max Ab Al *
        (mu.real (P.setHitsInfinite (RV : Set V)) * max Ab Al -
          mu.real (E.rectanglePairMergeErrorUnion a b c d L RV)) -
        mu.real (E.rectanglePairMergeErrorUnion a b c d L RV) ≤
      mu.real (E.verticalCrossingEvent a b c d)
    rw [max_eq_left hle]
    simpa [Ab] using htransfer
  · right
    have hle' : Ab ≤ Al := le_of_not_ge hle
    have htransfer := E.horizontalCrossing_ge_preferredSide_transfer
      mu hFKG a b c d L RH (by simpa [RH] using hHorizontalOpposite)
    change max Ab Al *
        (mu.real (P.setHitsInfinite (RH : Set V)) * max Ab Al -
          mu.real (E.rectanglePairMergeErrorUnion a b c d L RH)) -
        mu.real (E.rectanglePairMergeErrorUnion a b c d L RH) ≤
      mu.real (E.horizontalCrossingEvent a b c d)
    rw [max_eq_right hle']
    simpa [Al] using htransfer

/-! ## C. Uniform merge radii -/

/-- Under uniqueness, radii `radius n ≥ n` making the ball merge errors of `(L n, R₁ n)` and `(L n,
R₂ n)` both smaller than `1/(n+1)`. See also `PeriodicGraph.exists_uniform_pairMergeRadius`
(stronger: any finite family of targets; this is its two-target case). -/
lemma PeriodicGraph.exists_common_pairMergeRadius
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (L R₁ R₂ : Nat -> Finset V) :
    ∃ radius : Nat -> Nat, ∀ n,
      n ≤ radius n ∧
        mu.real (P.pairMergeErrorUnion (L n) (R₁ n) (radius n)) <
          (1 : Real) / (n + 1) ∧
        mu.real (P.pairMergeErrorUnion (L n) (R₂ n) (radius n)) <
          (1 : Real) / (n + 1) := by
  have hepsilon (n : Nat) : 0 < (1 : Real) / (n + 1) := by positivity
  have hrow (n : Nat) : ∃ k : Nat,
      n ≤ k ∧
        mu.real (P.pairMergeErrorUnion (L n) (R₁ n) k) <
          (1 : Real) / (n + 1) ∧
        mu.real (P.pairMergeErrorUnion (L n) (R₂ n) k) <
          (1 : Real) / (n + 1) := by
    have h₁ := P.pairMergeErrorUnion_real_tendsto_zero
      mu hunique (L n) (R₁ n)
    have h₂ := P.pairMergeErrorUnion_real_tendsto_zero
      mu hunique (L n) (R₂ n)
    rw [Metric.tendsto_atTop] at h₁ h₂
    obtain ⟨k₁, hk₁⟩ := h₁ _ (hepsilon n)
    obtain ⟨k₂, hk₂⟩ := h₂ _ (hepsilon n)
    let k := max n (max k₁ k₂)
    refine ⟨k, le_max_left _ _, ?_, ?_⟩
    · simpa [Real.dist_eq, abs_of_nonneg measureReal_nonneg] using
        hk₁ k ((le_max_left k₁ k₂).trans (le_max_right n (max k₁ k₂)))
    · simpa [Real.dist_eq, abs_of_nonneg measureReal_nonneg] using
        hk₂ k ((le_max_right k₁ k₂).trans (le_max_right n (max k₁ k₂)))
  choose radius hradius using hrow
  exact ⟨radius, hradius⟩

/-- Under uniqueness, radii `radius n ≥ n` making the ball merge errors of `(L n, R n i)` smaller
than `1/(n+1)` for all `i` in a finite index type. -/
lemma PeriodicGraph.exists_uniform_pairMergeRadius
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Nat -> Finset V) (R : Nat -> ι -> Finset V) :
    ∃ radius : Nat -> Nat, ∀ n,
      n ≤ radius n ∧ ∀ i,
        mu.real (P.pairMergeErrorUnion (L n) (R n i) (radius n)) <
          (1 : Real) / (n + 1) := by
  have hepsilon (n : Nat) : 0 < (1 : Real) / (n + 1) := by positivity
  have hrow (n : Nat) : ∃ k : Nat,
      n ≤ k ∧ ∀ i,
        mu.real (P.pairMergeErrorUnion (L n) (R n i) k) <
          (1 : Real) / (n + 1) := by
    have hsum : Tendsto (fun k => ∑ i : ι,
        mu.real (P.pairMergeErrorUnion (L n) (R n i) k))
        atTop (nhds 0) := by
      simpa using tendsto_finsetSum Finset.univ (fun i _ =>
        P.pairMergeErrorUnion_real_tendsto_zero mu hunique (L n) (R n i))
    rw [Metric.tendsto_atTop] at hsum
    obtain ⟨k₀, hk₀⟩ := hsum _ (hepsilon n)
    let k := max n k₀
    refine ⟨k, le_max_left _ _, fun i => ?_⟩
    have htotal : (∑ j : ι,
        mu.real (P.pairMergeErrorUnion (L n) (R n j) k)) <
          (1 : Real) / (n + 1) := by
      simpa [Real.dist_eq, abs_of_nonneg (Finset.sum_nonneg fun _ _ =>
        measureReal_nonneg)] using hk₀ k (le_max_right n k₀)
    exact (Finset.single_le_sum
      (f := fun j : ι =>
        mu.real (P.pairMergeErrorUnion (L n) (R n j) k))
      (fun j (_ : j ∈ Finset.univ) => measureReal_nonneg)
      (Finset.mem_univ i)).trans_lt htotal
  choose radius hradius using hrow
  exact ⟨radius, hradius⟩

/-- Translated, rectangle form of `PeriodicGraph.exists_common_pairMergeRadius`: for any rectangles
containing the translated buffered balls, both rectangle merge errors tend to zero. -/
lemma PeriodicPlaneEmbedding.exists_translated_pairMergeErrors_tendsto_zero
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (z : Nat -> Site 2) (L R₁ R₂ : Nat -> Finset V) :
    ∃ radius : Nat -> Nat,
      (∀ n, n ≤ radius n) ∧
      ∀ (a b c d : Nat -> Real),
        (∀ n, (P.shift (z n) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a n) (b n) (c n) (d n)) ->
        Tendsto (fun n => mu.real
          (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
            ((L n).image (P.shift (z n)))
            ((R₁ n).image (P.shift (z n))))) atTop (nhds 0) ∧
        Tendsto (fun n => mu.real
          (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
            ((L n).image (P.shift (z n)))
            ((R₂ n).image (P.shift (z n))))) atTop (nhds 0) := by
  obtain ⟨radius, hradius⟩ :=
    P.exists_common_pairMergeRadius mu hunique L R₁ R₂
  refine ⟨radius, fun n => (hradius n).1, fun a b c d hbox => ?_⟩
  have hepsilon : Tendsto (fun n : Nat => (1 : Real) / (n + 1))
      atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  constructor
  · apply squeeze_zero (fun _ => measureReal_nonneg) _ hepsilon
    intro n
    exact (E.translated_rectanglePairMergeErrorUnion_measureReal_le
      mu hTI (z n) (a n) (b n) (c n) (d n)
      (L n) (R₁ n) (radius n) (hbox n)).trans (hradius n).2.1.le
  · apply squeeze_zero (fun _ => measureReal_nonneg) _ hepsilon
    intro n
    exact (E.translated_rectanglePairMergeErrorUnion_measureReal_le
      mu hTI (z n) (a n) (b n) (c n) (d n)
      (L n) (R₂ n) (radius n) (hbox n)).trans (hradius n).2.2.le

/-- One radius sequence makes the rectangle merge error between the translated orbit box at `x n`
and the box at any king neighbour `x n + preferenceKingOffset (ij n)` tend to zero. -/
lemma PeriodicPlaneEmbedding.exists_uniform_kingOffset_mergeError_tendsto_zero
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
    ∃ radius : Nat -> Nat,
      (∀ n, n ≤ radius n) ∧
      ∀ (x : Nat -> Site 2) (ij : Nat -> Fin 3 × Fin 3)
        (a b c d : Nat -> Real),
        (∀ n, (P.shift (x n) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a n) (b n) (c n) (d n)) ->
        Tendsto (fun n => mu.real
          (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
            ((P.orbitBox n).image (P.shift (x n)))
            ((P.orbitBox n).image
              (P.shift (x n + preferenceKingOffset (ij n))))))
          atTop (nhds 0) := by
  classical
  let L : Nat -> Finset V := fun n => P.orbitBox n
  let R : Nat -> (Fin 3 × Fin 3) -> Finset V := fun n ij =>
    (P.orbitBox n).image (P.shift (preferenceKingOffset ij))
  obtain ⟨radius, hradius⟩ :=
    P.exists_uniform_pairMergeRadius mu hunique L R
  refine ⟨radius, fun n => (hradius n).1, fun x ij a b c d hbox => ?_⟩
  have hepsilon : Tendsto (fun n : Nat => (1 : Real) / (n + 1))
      atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hepsilon
  intro n
  have hR : (R n (ij n)).image (P.shift (x n)) =
      (P.orbitBox n).image
        (P.shift (x n + preferenceKingOffset (ij n))) := by
    simp only [R, Finset.image_image]
    apply Finset.image_congr
    intro u hu
    simpa [add_comm] using
      (P.shift_add (preferenceKingOffset (ij n)) (x n) u).symm
  have hle := E.translated_rectanglePairMergeErrorUnion_measureReal_le
    mu hTI (x n) (a n) (b n) (c n) (d n)
    (L n) (R n (ij n)) (radius n) (hbox n)
  simpa only [L, hR] using hle.trans (((hradius n).2 (ij n)).le)

/-! ## D. Crossing limits -/

/-- Under FKG, translation invariance and uniqueness, for given witness sites there is a radius
sequence such that, in rectangles containing the buffered balls and satisfying the
preference-witness inequalities, the larger crossing probability tends to one. -/
lemma PeriodicPlaneEmbedding.exists_connectorRadius_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (x xVertical xHorizontal : Nat -> Site 2) :
    ∃ radius : Nat -> Nat, ∀ (a b c d : Nat -> Real),
      (∀ n, (P.shift (x n) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
          E.rectVertices (a n) (b n) (c n) (d n)) ->
      (∀ n,
        mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image (P.shift (x n)) : Set V)
          (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n))) ≤
        mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image (P.shift (x n)) : Set V)
          (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) ->
      (∀ n,
        mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image (P.shift (x n)) : Set V)
          (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n))) ≤
        mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image (P.shift (x n)) : Set V)
          (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) ->
      (∀ n,
        mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image (P.shift (xVertical n)) : Set V)
          (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n))) ≤
        mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image (P.shift (xVertical n)) : Set V)
          (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) ->
      (∀ n,
        mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image (P.shift (xHorizontal n)) : Set V)
          (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n))) ≤
        mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image (P.shift (xHorizontal n)) : Set V)
          (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) ->
      Tendsto (fun n => max
        (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n)))
        (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))))
        atTop (nhds 1) := by
  classical
  let deltaV : Nat -> Site 2 := fun n => xVertical n - x n
  let deltaH : Nat -> Site 2 := fun n => xHorizontal n - x n
  let L : Nat -> Finset V := fun n => P.orbitBox n
  let RV : Nat -> Finset V := fun n =>
    (P.orbitBox n).image (P.shift (deltaV n))
  let RH : Nat -> Finset V := fun n =>
    (P.orbitBox n).image (P.shift (deltaH n))
  have hRV (n : Nat) : (RV n).image (P.shift (x n)) =
      (P.orbitBox n).image (P.shift (xVertical n)) := by
    simp only [RV, Finset.image_image]
    apply Finset.image_congr
    intro u hu
    change P.shift (x n) (P.shift (deltaV n) u) = P.shift (xVertical n) u
    rw [← P.shift_add]
    simp [deltaV]
  have hRH (n : Nat) : (RH n).image (P.shift (x n)) =
      (P.orbitBox n).image (P.shift (xHorizontal n)) := by
    simp only [RH, Finset.image_image]
    apply Finset.image_congr
    intro u hu
    change P.shift (x n) (P.shift (deltaH n) u) = P.shift (xHorizontal n) u
    rw [← P.shift_add]
    simp [deltaH]
  obtain ⟨radius, hradius, herrors⟩ :=
    E.exists_translated_pairMergeErrors_tendsto_zero
      mu hTI hunique x L RV RH
  refine ⟨radius, fun a b c d hrect hBT hLR hVOpp hHOpp => ?_⟩
  obtain ⟨hMv0, hMh0⟩ := herrors a b c d hrect
  have hMv : Tendsto (fun n => mu.real
      (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image (P.shift (x n)))
        ((P.orbitBox n).image (P.shift (xVertical n)))))
      atTop (nhds 0) := by
    simpa only [L, hRV] using hMv0
  have hMh : Tendsto (fun n => mu.real
      (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image (P.shift (x n)))
        ((P.orbitBox n).image (P.shift (xHorizontal n)))))
      atTop (nhds 0) := by
    simpa only [L, hRH] using hMh0
  let Ab : Nat -> Real := fun n => mu.real
    (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((P.orbitBox n).image (P.shift (x n)) : Set V)
      (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))
  let Al : Nat -> Real := fun n => mu.real
    (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((P.orbitBox n).image (P.shift (x n)) : Set V)
      (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))
  let A : Nat -> Real := fun n => max (Ab n) (Al n)
  let Hv : Nat -> Real := fun n => mu.real
    (P.setHitsInfinite
      ((P.orbitBox n).image (P.shift (xVertical n)) : Set V))
  let Hh : Nat -> Real := fun n => mu.real
    (P.setHitsInfinite
      ((P.orbitBox n).image (P.shift (xHorizontal n)) : Set V))
  let Mv : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
      ((P.orbitBox n).image (P.shift (x n)))
      ((P.orbitBox n).image (P.shift (xVertical n))))
  let Mh : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
      ((P.orbitBox n).image (P.shift (x n)))
      ((P.orbitBox n).image (P.shift (xHorizontal n))))
  let Cv : Nat -> Real := fun n =>
    mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n))
  let Ch : Nat -> Real := fun n =>
    mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun _ h => h.1
  have hhit := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  have hmiss : Tendsto (fun n =>
      1 - mu.real (P.orbitBoxHitsInfinite n)) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hhit
  have hlower : Tendsto (fun n => 1 - Real.sqrt (Real.sqrt
      (1 - mu.real (P.orbitBoxHitsInfinite n)))) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hmiss.sqrt.sqrt
  have hsource (n : Nat) :
      ((P.orbitBox n).image (P.shift (x n)) : Set V) ⊆
        E.rectVertices (a n) (b n) (c n) (d n) := by
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_image] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    apply hrect n
    refine ⟨u, P.orbitBox_mono ?_ hu, rfl⟩
    exact (hradius n).trans (P.id_le_bufferedRadius (radius n))
  have hbranch (n : Nat) :
      1 - Real.sqrt (Real.sqrt
          (1 - mu.real (P.orbitBoxHitsInfinite n))) ≤ A n ∧
        (A n * (Hv n * A n - Mv n) - Mv n ≤ Cv n ∨
          A n * (Hh n * A n - Mh n) - Mh n ≤ Ch n) := by
    simpa [A, Ab, Al, Hv, Hh, Mv, Mh, Cv, Ch] using
      E.crossing_branch_of_preference_witness mu hFKG hTI n
        (a n) (b n) (c n) (d n) (x n) (xVertical n) (xHorizontal n)
        (hsource n) (hBT n) (hLR n) (hVOpp n) (hHOpp n)
  have hA : Tendsto A atTop (nhds 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
    · exact fun n => (hbranch n).1
    · intro n
      exact max_le measureReal_le_one measureReal_le_one
  have htranslatedHit (z : Nat -> Site 2) : Tendsto (fun n =>
      mu.real (P.setHitsInfinite
        ((P.orbitBox n).image (P.shift (z n)) : Set V)))
      atTop (nhds 1) := by
    apply hhit.congr'
    filter_upwards with n
    have hset : (((P.orbitBox n).image (P.shift (z n)) : Finset V) : Set V) =
        P.shift (z n) '' (P.orbitBox n : Set V) := by
      ext v
      simp
    rw [hset, P.setHitsInfinite_translate_measureReal_eq mu hTI,
      P.setHitsInfinite_orbitBox]
  have hHv : Tendsto Hv atTop (nhds 1) := by
    simpa [Hv] using htranslatedHit xVertical
  have hHh : Tendsto Hh atTop (nhds 1) := by
    simpa [Hh] using htranslatedHit xHorizontal
  have hMv' : Tendsto Mv atTop (nhds 0) := by simpa [Mv] using hMv
  have hMh' : Tendsto Mh atTop (nhds 0) := by simpa [Mh] using hMh
  simpa [Cv, Ch] using crossing_max_tendsto_one_of_preferredSide_branches
    A Hv Hh Mv Mh Cv Ch hA hHv hHh hMv' hMh'
      (fun n => (hbranch n).2) (fun _ => measureReal_le_one)
      (fun _ => measureReal_le_one)

/-- Uniform version of `exists_connectorRadius_crossing_max_tendsto_one`: one radius sequence works
for all witness sites and all king-neighbour choices. -/
lemma PeriodicPlaneEmbedding.exists_uniform_connectorRadius_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
    ∃ radius : Nat -> Nat, ∀ (x : Nat -> Site 2)
      (ijVertical ijHorizontal : Nat -> Fin 3 × Fin 3)
      (a b c d : Nat -> Real),
      (∀ n, (P.shift (x n) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
          E.rectVertices (a n) (b n) (c n) (d n)) ->
      (∀ n,
        mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image (P.shift (x n)) : Set V)
          (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n))) ≤
        mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image (P.shift (x n)) : Set V)
          (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) ->
      (∀ n,
        mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image (P.shift (x n)) : Set V)
          (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n))) ≤
        mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image (P.shift (x n)) : Set V)
          (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) ->
      (∀ n,
        mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image
            (P.shift (x n + preferenceKingOffset (ijVertical n))) : Set V)
          (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n))) ≤
        mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image
            (P.shift (x n + preferenceKingOffset (ijVertical n))) : Set V)
          (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) ->
      (∀ n,
        mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image
            (P.shift (x n + preferenceKingOffset (ijHorizontal n))) : Set V)
          (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n))) ≤
        mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image
            (P.shift (x n + preferenceKingOffset (ijHorizontal n))) : Set V)
          (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) ->
      Tendsto (fun n => max
        (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n)))
        (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))))
        atTop (nhds 1) := by
  classical
  obtain ⟨radius, hradius, hmerge⟩ :=
    E.exists_uniform_kingOffset_mergeError_tendsto_zero mu hTI hunique
  refine ⟨radius, fun x ijV ijH a b c d hrect hBT hLR hVOpp hHOpp => ?_⟩
  let xV : Nat -> Site 2 := fun n =>
    x n + preferenceKingOffset (ijV n)
  let xH : Nat -> Site 2 := fun n =>
    x n + preferenceKingOffset (ijH n)
  have hMv : Tendsto (fun n => mu.real
      (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image (P.shift (x n)))
        ((P.orbitBox n).image (P.shift (xV n)))))
      atTop (nhds 0) := by
    simpa only [xV] using hmerge x ijV a b c d hrect
  have hMh : Tendsto (fun n => mu.real
      (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image (P.shift (x n)))
        ((P.orbitBox n).image (P.shift (xH n)))))
      atTop (nhds 0) := by
    simpa only [xH] using hmerge x ijH a b c d hrect
  let Ab : Nat -> Real := fun n => mu.real
    (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((P.orbitBox n).image (P.shift (x n)) : Set V)
      (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))
  let Al : Nat -> Real := fun n => mu.real
    (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((P.orbitBox n).image (P.shift (x n)) : Set V)
      (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))
  let A : Nat -> Real := fun n => max (Ab n) (Al n)
  let Hv : Nat -> Real := fun n => mu.real
    (P.setHitsInfinite ((P.orbitBox n).image (P.shift (xV n)) : Set V))
  let Hh : Nat -> Real := fun n => mu.real
    (P.setHitsInfinite ((P.orbitBox n).image (P.shift (xH n)) : Set V))
  let Mv : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
      ((P.orbitBox n).image (P.shift (x n)))
      ((P.orbitBox n).image (P.shift (xV n))))
  let Mh : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
      ((P.orbitBox n).image (P.shift (x n)))
      ((P.orbitBox n).image (P.shift (xH n))))
  let Cv : Nat -> Real := fun n =>
    mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n))
  let Ch : Nat -> Real := fun n =>
    mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun _ h => h.1
  have hhit := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  have hmiss : Tendsto (fun n =>
      1 - mu.real (P.orbitBoxHitsInfinite n)) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hhit
  have hlower : Tendsto (fun n => 1 - Real.sqrt (Real.sqrt
      (1 - mu.real (P.orbitBoxHitsInfinite n)))) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hmiss.sqrt.sqrt
  have hsource (n : Nat) :
      ((P.orbitBox n).image (P.shift (x n)) : Set V) ⊆
        E.rectVertices (a n) (b n) (c n) (d n) := by
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_image] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    apply hrect n
    refine ⟨u, P.orbitBox_mono ?_ hu, rfl⟩
    exact (hradius n).trans (P.id_le_bufferedRadius (radius n))
  have hbranch (n : Nat) :
      1 - Real.sqrt (Real.sqrt
          (1 - mu.real (P.orbitBoxHitsInfinite n))) ≤ A n ∧
        (A n * (Hv n * A n - Mv n) - Mv n ≤ Cv n ∨
          A n * (Hh n * A n - Mh n) - Mh n ≤ Ch n) := by
    simpa [A, Ab, Al, Hv, Hh, Mv, Mh, Cv, Ch, xV, xH] using
      E.crossing_branch_of_preference_witness mu hFKG hTI n
        (a n) (b n) (c n) (d n) (x n) (xV n) (xH n)
        (hsource n) (hBT n) (hLR n) (hVOpp n) (hHOpp n)
  have hA : Tendsto A atTop (nhds 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
    · exact fun n => (hbranch n).1
    · intro n
      exact max_le measureReal_le_one measureReal_le_one
  have htranslatedHit (z : Nat -> Site 2) : Tendsto (fun n =>
      mu.real (P.setHitsInfinite
        ((P.orbitBox n).image (P.shift (z n)) : Set V)))
      atTop (nhds 1) := by
    apply hhit.congr'
    filter_upwards with n
    have hset : (((P.orbitBox n).image (P.shift (z n)) : Finset V) : Set V) =
        P.shift (z n) '' (P.orbitBox n : Set V) := by
      ext v
      simp
    rw [hset, P.setHitsInfinite_translate_measureReal_eq mu hTI,
      P.setHitsInfinite_orbitBox]
  have hHv : Tendsto Hv atTop (nhds 1) := by
    simpa [Hv] using htranslatedHit xV
  have hHh : Tendsto Hh atTop (nhds 1) := by
    simpa [Hh] using htranslatedHit xH
  have hMv' : Tendsto Mv atTop (nhds 0) := by simpa [Mv] using hMv
  have hMh' : Tendsto Mh atTop (nhds 0) := by simpa [Mh] using hMh
  simpa [Cv, Ch] using crossing_max_tendsto_one_of_preferredSide_branches
    A Hv Hh Mv Mh Cv Ch hA hHv hHh hMv' hMh'
      (fun n => (hbranch n).2) (fun _ => measureReal_le_one)
      (fun _ => measureReal_le_one)

end StatMech.FK.PeriodicPlanar
