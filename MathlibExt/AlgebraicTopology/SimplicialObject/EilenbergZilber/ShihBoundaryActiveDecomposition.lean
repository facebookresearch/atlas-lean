/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryMixedCancellation
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundaryDecomposition

/-!
# Active-face decomposition for the Shih boundary

For fixed bidegree and positive gap, active upper faces split into mixed and
nonmixed faces.  The mixed family cancels.  The nonmixed family is reindexed
through the canonical shuffle-boundary equivalence, exposing the left and
right insertion coordinates used by the pointwise cancellation lemmas.  The
only exceptional left family is the edge case with Shih left degree zero.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

/-- Active upper-boundary data at a fixed Shih bidegree. -/
abbrev ShihUpperActiveFiber (p q : ℕ) :=
  Shuffle (p + 1) q × Fin ((p + 1) + q + 1)

abbrev ShihUpperActiveFiber.IsMixed {p q : ℕ}
    (z : ShihUpperActiveFiber p q) : Prop :=
  Shuffle.IsMixedBoundary z.1 z.2

abbrev ShihUpperMixedFiber (p q : ℕ) :=
  {z : ShihUpperActiveFiber p q // ShihUpperActiveFiber.IsMixed z}

noncomputable instance (p q : ℕ) :
    DecidablePred (@ShihUpperActiveFiber.IsMixed p q) :=
  Classical.decPred _

abbrev ShihUpperNonmixedFiber (p q : ℕ) :=
  Shuffle.NonmixedBoundaryFace (p + 1) q

noncomputable instance (p q : ℕ) : Fintype (ShihUpperMixedFiber p q) :=
  by classical exact Subtype.fintype _

/-- Exact mixed/nonmixed partition of fixed-bidegree active data. -/
noncomputable def shihUpperActiveEquivMixedSumNonmixed (p q : ℕ) :
    ShihUpperActiveFiber p q ≃
      ShihUpperMixedFiber p q ⊕ ShihUpperNonmixedFiber p q := by
  classical
  exact (Equiv.sumCompl ShihUpperActiveFiber.IsMixed).symm

/-- Sum form of the exact mixed/nonmixed partition. -/
theorem sum_shihUpperActive_eq_mixed_add_nonmixed
    {A : Type*} [AddCommMonoid A] (p q : ℕ)
    (f : ShihUpperActiveFiber p q → A) :
    ∑ z, f z =
      (∑ z ∈ (Finset.univ.filter ShihUpperActiveFiber.IsMixed), f z) +
        ∑ z ∈ Shuffle.nonmixedBoundaryFaces (p + 1) q, f z := by
  classical
  rw [Shuffle.nonmixedBoundaryFaces]
  exact (Finset.sum_filter_add_sum_filter_not Finset.univ
    ShihUpperActiveFiber.IsMixed f).symm

/-- Regard a mixed face as mixed active data. -/
def shihUpperMixedDataOfMixedFace {p q : ℕ}
    (x : Shuffle.MixedFace (p + 1) q) : ShihUpperMixedFiber p q :=
  ⟨(x.shuffle, x.faceIndex),
    ⟨x.lowerPosition, x.upperPosition, x.adjacent, rfl, x.mixed⟩⟩

/-- Recover the canonical mixed-face witness from mixed active data. -/
noncomputable def mixedFaceOfShihUpperMixedData {p q : ℕ}
    (z : ShihUpperMixedFiber p q) : Shuffle.MixedFace (p + 1) q :=
  let lower := z.property.choose
  let upper := z.property.choose_spec.choose
  { shuffle := z.val.1
    lowerPosition := lower
    upperPosition := upper
    adjacent := z.property.choose_spec.choose_spec.1
    mixed := z.property.choose_spec.choose_spec.2.2 }

theorem mixedFaceOfShihUpperMixedData_faceIndex {p q : ℕ}
    (z : ShihUpperMixedFiber p q) :
    (mixedFaceOfShihUpperMixedData z).faceIndex = z.val.2 := by
  change z.property.choose_spec.choose.castSucc = z.val.2
  exact z.property.choose_spec.choose_spec.2.1.symm

/-- A `MixedFace` is the same datum as a mixed active coordinate. -/
noncomputable def shihMixedFaceEquivUpperMixedData (p q : ℕ) :
    Shuffle.MixedFace (p + 1) q ≃ ShihUpperMixedFiber p q where
  toFun := shihUpperMixedDataOfMixedFace
  invFun := mixedFaceOfShihUpperMixedData
  left_inv x := by
    apply Shuffle.MixedFace.ext
    · rfl
    · apply Fin.ext
      have hupper :
          (mixedFaceOfShihUpperMixedData
            (shihUpperMixedDataOfMixedFace x)).upperPosition =
              x.upperPosition := by
        have hface := mixedFaceOfShihUpperMixedData_faceIndex
          (shihUpperMixedDataOfMixedFace x)
        change
          (mixedFaceOfShihUpperMixedData
            (shihUpperMixedDataOfMixedFace x)).upperPosition.castSucc =
              x.upperPosition.castSucc at hface
        exact Fin.castSucc_inj.mp hface
      have hadjacent :=
        (mixedFaceOfShihUpperMixedData
          (shihUpperMixedDataOfMixedFace x)).adjacent
      have hadjacentX := x.adjacent
      have hupperVal := congrArg Fin.val hupper
      omega
    · apply Fin.ext
      have hface := mixedFaceOfShihUpperMixedData_faceIndex
        (shihUpperMixedDataOfMixedFace x)
      change
        (mixedFaceOfShihUpperMixedData
          (shihUpperMixedDataOfMixedFace x)).upperPosition.castSucc =
            x.upperPosition.castSucc at hface
      exact congrArg Fin.val (Fin.castSucc_inj.mp hface)
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      exact congrArg Fin.val (mixedFaceOfShihUpperMixedData_faceIndex z)

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- All mixed active data cancel at fixed bidegree and gap. -/
theorem shihUpperMixedData_sum_eq_zero
    (X Y : SimplicialObject C) (p q m : ℕ) (hm : 0 < m) :
    ∑ z : ShihUpperMixedFiber p q,
      shihUpperBoundaryTerm X Y (p + q + m)
        (ShihIndex.ofGap p q m hm z.val.1)
        (ShihIndex.activeBoundaryFaceOfGap p q m hm z.val.2) = 0 := by
  rw [← Fintype.sum_equiv (shihMixedFaceEquivUpperMixedData p q)
    (fun x : Shuffle.MixedFace (p + 1) q =>
      shihUpperBoundaryTerm X Y (p + q + m)
        (ShihIndex.ofGap p q m hm x.shuffle)
        (ShihIndex.activeBoundaryFaceOfGap p q m hm x.faceIndex))
    (fun z : ShihUpperMixedFiber p q =>
      shihUpperBoundaryTerm X Y (p + q + m)
        (ShihIndex.ofGap p q m hm z.val.1)
        (ShihIndex.activeBoundaryFaceOfGap p q m hm z.val.2))
    (fun _ => rfl)]
  exact shihMixedActiveBoundary_sum_eq_zero X Y p q m hm

/-- The mixed cancellation in the filtered form used by the exact active
partition. -/
theorem shihUpperMixedFiber_filter_sum_eq_zero
    (X Y : SimplicialObject C) (p q m : ℕ) (hm : 0 < m) :
    ∑ z ∈ (Finset.univ.filter ShihUpperActiveFiber.IsMixed),
      shihUpperBoundaryTerm X Y (p + q + m)
        (ShihIndex.ofGap p q m hm z.1)
        (ShihIndex.activeBoundaryFaceOfGap p q m hm z.2) = 0 := by
  classical
  rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
  exact shihUpperMixedData_sum_eq_zero X Y p q m hm

/-- After mixed cancellation, the fixed-bidegree active sum is its nonmixed
subsum. -/
theorem shihUpperActive_sum_eq_nonmixed
    (X Y : SimplicialObject C) (p q m : ℕ) (hm : 0 < m) :
    ∑ z : ShihUpperActiveFiber p q,
      shihUpperBoundaryTerm X Y (p + q + m)
        (ShihIndex.ofGap p q m hm z.1)
        (ShihIndex.activeBoundaryFaceOfGap p q m hm z.2) =
      ∑ z ∈ Shuffle.nonmixedBoundaryFaces (p + 1) q,
        shihUpperBoundaryTerm X Y (p + q + m)
          (ShihIndex.ofGap p q m hm z.1)
          (ShihIndex.activeBoundaryFaceOfGap p q m hm z.2) := by
  rw [sum_shihUpperActive_eq_mixed_add_nonmixed,
    shihUpperMixedFiber_filter_sum_eq_zero, zero_add]

/-- For positive right degree, the nonmixed sum is the left-boundary family
plus the right-boundary family supplied by `Shuffle.nonmixedBoundaryEquiv`. -/
theorem shihUpperNonmixed_sum_positive
    (X Y : SimplicialObject C) (p q m : ℕ) (hm : 0 < m) :
    ∑ z ∈ Shuffle.nonmixedBoundaryFaces (p + 1) (q + 1),
      shihUpperBoundaryTerm X Y (p + (q + 1) + m)
        (ShihIndex.ofGap p (q + 1) m hm z.1)
        (ShihIndex.activeBoundaryFaceOfGap p (q + 1) m hm z.2) =
      (∑ x : Fin (p + 2) × Shuffle p (q + 1),
        shihUpperBoundaryTerm X Y (p + (q + 1) + m)
          (ShihIndex.ofGap p (q + 1) m hm
            (Shuffle.leftBoundaryPair x).1)
          (ShihIndex.activeBoundaryFaceOfGap p (q + 1) m hm
            (Shuffle.leftBoundaryPair x).2)) +
      ∑ x : Fin (q + 2) × Shuffle (p + 1) q,
        shihUpperBoundaryTerm X Y (p + (q + 1) + m)
          (ShihIndex.ofGap p (q + 1) m hm
            (Shuffle.rightBoundaryPair x).1)
          (ShihIndex.activeBoundaryFaceOfGap p (q + 1) m hm
            (Shuffle.rightBoundaryPair x).2) := by
  classical
  exact Shuffle.sum_nonmixedBoundaryFaces_positive
      (A := X.obj (Opposite.op ⦋p + (q + 1) + m⦌) ⊗
        Y.obj (Opposite.op ⦋p + (q + 1) + m⦌) ⟶
        X.obj (Opposite.op ⦋p + (q + 1) + m⦌) ⊗
          Y.obj (Opposite.op ⦋p + (q + 1) + m⦌))
      (p := p) (q := q)
      (fun s k => shihUpperBoundaryTerm X Y (p + (q + 1) + m)
        (ShihIndex.ofGap p (q + 1) m hm s)
        (ShihIndex.activeBoundaryFaceOfGap p (q + 1) m hm k))

/-- At right degree zero, the nonmixed sum consists only of left-boundary
data. -/
theorem shihUpperNonmixed_sum_right_zero
    (X Y : SimplicialObject C) (p m : ℕ) (hm : 0 < m) :
    ∑ z ∈ Shuffle.nonmixedBoundaryFaces (p + 1) 0,
      shihUpperBoundaryTerm X Y (p + 0 + m)
        (ShihIndex.ofGap p 0 m hm z.1)
        (ShihIndex.activeBoundaryFaceOfGap p 0 m hm z.2) =
      ∑ x : Fin (p + 2) × Shuffle p 0,
        shihUpperBoundaryTerm X Y (p + 0 + m)
          (ShihIndex.ofGap p 0 m hm (Shuffle.leftBoundaryPair x).1)
          (ShihIndex.activeBoundaryFaceOfGap p 0 m hm
            (Shuffle.leftBoundaryPair x).2) := by
  classical
  exact Shuffle.sum_nonmixedBoundaryFaces_right_zero
      (A := X.obj (Opposite.op ⦋p + 0 + m⦌) ⊗
        Y.obj (Opposite.op ⦋p + 0 + m⦌) ⟶
        X.obj (Opposite.op ⦋p + 0 + m⦌) ⊗
          Y.obj (Opposite.op ⦋p + 0 + m⦌))
      (p := p)
      (fun s k => shihUpperBoundaryTerm X Y (p + 0 + m)
        (ShihIndex.ofGap p 0 m hm s)
        (ShihIndex.activeBoundaryFaceOfGap p 0 m hm k))

/-- The only left-boundary family not covered by the ordinary inserted-left
coordinates is the edge with Shih left degree zero. -/
abbrev ShihUpperLeftEdgeData (q : ℕ) := Fin 2 × Shuffle 0 q

/-- Ordinary inserted-left data, with positive output left degree. -/
abbrev ShihUpperLeftOrdinaryData (p q : ℕ) :=
  Fin (p + 3) × Shuffle (p + 1) q

/-- Ordinary inserted-right data. -/
abbrev ShihUpperRightOrdinaryData (p q : ℕ) :=
  Fin (q + 2) × Shuffle (p + 1) q

/-- Positive-left and positive-right nonmixed data are expressed directly in
the integrated cancellation coordinates. -/
theorem shihUpperNonmixed_sum_both_positive
    (X Y : SimplicialObject C) (p q m : ℕ) (hm : 0 < m) :
    ∑ z ∈ Shuffle.nonmixedBoundaryFaces ((p + 1) + 1) (q + 1),
      shihUpperBoundaryTerm X Y ((p + 1) + (q + 1) + m)
        (ShihIndex.ofGap (p + 1) (q + 1) m hm z.1)
        (ShihIndex.activeBoundaryFaceOfGap (p + 1) (q + 1) m hm z.2) =
      (∑ x : ShihUpperLeftOrdinaryData p (q + 1),
        shihUpperBoundaryTerm X Y ((p + 1) + (q + 1) + m)
          (ShihIndex.ofGap (p + 1) (q + 1) m hm
            (Shuffle.leftBoundaryPair x).1)
          (ShihIndex.activeBoundaryFaceOfGap (p + 1) (q + 1) m hm
            (Shuffle.leftBoundaryPair x).2)) +
      ∑ x : ShihUpperRightOrdinaryData (p + 1) q,
        shihUpperBoundaryTerm X Y ((p + 1) + (q + 1) + m)
          (ShihIndex.ofGap (p + 1) (q + 1) m hm
            (Shuffle.rightBoundaryPair x).1)
          (ShihIndex.activeBoundaryFaceOfGap (p + 1) (q + 1) m hm
            (Shuffle.rightBoundaryPair x).2) := by
  rw [shihUpperNonmixed_sum_positive]

/-- At positive right degree and left degree zero, the nonmixed family is an
ordinary inserted-right family plus the isolated left edge. -/
theorem shihUpperNonmixed_sum_left_edge
    (X Y : SimplicialObject C) (q m : ℕ) (hm : 0 < m) :
    ∑ z ∈ Shuffle.nonmixedBoundaryFaces (0 + 1) (q + 1),
      shihUpperBoundaryTerm X Y (0 + (q + 1) + m)
        (ShihIndex.ofGap 0 (q + 1) m hm z.1)
        (ShihIndex.activeBoundaryFaceOfGap 0 (q + 1) m hm z.2) =
      (∑ x : ShihUpperLeftEdgeData (q + 1),
        shihUpperBoundaryTerm X Y (0 + (q + 1) + m)
          (ShihIndex.ofGap 0 (q + 1) m hm
            (Shuffle.leftBoundaryPair x).1)
          (ShihIndex.activeBoundaryFaceOfGap 0 (q + 1) m hm
            (Shuffle.leftBoundaryPair x).2)) +
      ∑ x : Fin (q + 2) × Shuffle 1 q,
        shihUpperBoundaryTerm X Y (0 + (q + 1) + m)
          (ShihIndex.ofGap 0 (q + 1) m hm
            (Shuffle.rightBoundaryPair x).1)
          (ShihIndex.activeBoundaryFaceOfGap 0 (q + 1) m hm
            (Shuffle.rightBoundaryPair x).2) := by
  rw [shihUpperNonmixed_sum_positive]

end AlgebraicTopology.EilenbergZilber
