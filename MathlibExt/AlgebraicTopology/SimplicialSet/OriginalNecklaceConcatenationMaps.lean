/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceConcatenation
public import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalTwoStandardBeadPushout

/-!
# Complete original maps into a concatenated necklace

The full prefix and suffix simplex maps restrict to the original
necklace maps. Both endpoint readbacks retain the same native pivot.
The whole concatenation is the union of these original two pieces.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace

open OriginalTwoBead OriginalTwoBead.OrdinalCharts

/-- The literal full original prefix map into the native concatenation. -/
def concatLeft (T U : Data) : T.object.{u} ⟶ (T.concat U).object :=
  Subcomplex.lift ((complex T.joints).ι ≫
    SSet.stdSimplex.map (prefixOperator T.dimension U.dimension)) (by
    rintro ⟨⟨d⟩⟩ s ⟨a, rfl⟩
    exact (prefix_mem_concat_iff T U a.val).mpr a.property)

/-- The literal full original suffix map into the native concatenation. -/
def concatRight (T U : Data) : U.object.{u} ⟶ (T.concat U).object :=
  Subcomplex.lift ((complex U.joints).ι ≫
    SSet.stdSimplex.map (suffixOperator T.dimension U.dimension)) (by
    rintro ⟨⟨d⟩⟩ s ⟨a, rfl⟩
    exact (suffix_mem_concat_iff T U a.val).mpr a.property)

/-- The entire first original map retains its literal ordinal prefix. -/
@[reassoc]
theorem concatLeft_ι (T U : Data) :
    concatLeft.{u} T U ≫ (complex (T.concat U).joints).ι =
      (complex T.joints).ι ≫ SSet.stdSimplex.map
        (prefixOperator T.dimension U.dimension) := rfl

/-- The entire second original map retains its literal ordinal suffix. -/
@[reassoc]
theorem concatRight_ι (T U : Data) :
    concatRight.{u} T U ≫ (complex (T.concat U).joints).ι =
      (complex U.joints).ι ≫ SSet.stdSimplex.map
        (suffixOperator T.dimension U.dimension) := rfl

/-- The original initial vertex is preserved by the whole first map. -/
theorem concatLeft_source (T U : Data) :
    T.source.{u} ≫ concatLeft T U = (T.concat U).source := by
  apply (cancel_mono (complex (T.concat U).joints).ι).1
  rw [Category.assoc, concatLeft_ι, ← Category.assoc]
  change (vertexMap T.joints 0 ≫ (complex T.joints).ι) ≫ _ =
    vertexMap (T.concat U).joints 0 ≫ _
  rw [vertexMap_ι, vertexMap_ι, ← SSet.stdSimplex.map_comp]
  rfl

/-- The original terminal vertex of the first necklace is the same native pivot. -/
theorem concatLeft_target (T U : Data) :
    T.target.{u} ≫ concatLeft T U =
      vertexMap (T.concat U).joints (pivot T.dimension U.dimension) := by
  apply (cancel_mono (complex (T.concat U).joints).ι).1
  rw [Category.assoc, concatLeft_ι, ← Category.assoc]
  change (vertexMap T.joints (Fin.last T.dimension) ≫ (complex T.joints).ι) ≫ _ =
    vertexMap (T.concat U).joints _ ≫ _
  rw [vertexMap_ι, vertexMap_ι, ← SSet.stdSimplex.map_comp]
  rfl

/-- The original initial vertex of the second necklace is that same pivot. -/
theorem concatRight_source (T U : Data) :
    U.source.{u} ≫ concatRight T U =
      vertexMap (T.concat U).joints (pivot T.dimension U.dimension) := by
  apply (cancel_mono (complex (T.concat U).joints).ι).1
  rw [Category.assoc, concatRight_ι, ← Category.assoc]
  change (vertexMap U.joints 0 ≫ (complex U.joints).ι) ≫ _ =
    vertexMap (T.concat U).joints _ ≫ _
  rw [vertexMap_ι, vertexMap_ι, ← SSet.stdSimplex.map_comp]
  congr 1

/-- The original terminal vertex is preserved by the whole second map. -/
theorem concatRight_target (T U : Data) :
    U.target.{u} ≫ concatRight T U = (T.concat U).target := by
  apply (cancel_mono (complex (T.concat U).joints).ι).1
  rw [Category.assoc, concatRight_ι, ← Category.assoc]
  change (vertexMap U.joints (Fin.last U.dimension) ≫ (complex U.joints).ι) ≫ _ =
    vertexMap (T.concat U).joints (Fin.last (T.dimension + U.dimension)) ≫ _
  rw [vertexMap_ι, vertexMap_ι, ← SSet.stdSimplex.map_comp]
  rfl

/-- The two whole original maps agree at the same native overlap point. -/
theorem concat_square (T U : Data) :
    T.target.{u} ≫ concatLeft T U = U.source ≫ concatRight T U := by
  rw [concatLeft_target, concatRight_source]

/-- The entire concatenation crosses none of its actual pivot joint. -/
theorem concat_le_union (T U : Data) :
    complex.{u} (T.concat U).joints ≤ union (pivot T.dimension U.dimension) :=
  iInf_le_of_le (pivot T.dimension U.dimension)
    (iInf_le_of_le (concat_pivot_joint T U) le_rfl)

/-- The complete first piece of the original concatenation. -/
def concatLeftPiece (T U : Data) : (Δ[T.dimension + U.dimension] : SSet.{u}).Subcomplex :=
  complex (T.concat U).joints ⊓ left (pivot T.dimension U.dimension)

/-- The complete second piece of the original concatenation. -/
def concatRightPiece (T U : Data) : (Δ[T.dimension + U.dimension] : SSet.{u}).Subcomplex :=
  complex (T.concat U).joints ⊓ right (pivot T.dimension U.dimension)

/-- The actual two full pieces cover exactly the original concatenation. -/
theorem concatPieces_sup (T U : Data) :
    concatLeftPiece.{u} T U ⊔ concatRightPiece T U = complex (T.concat U).joints := by
  ext ⟨⟨d⟩⟩ s
  change (s ∈ (complex.{u} (T.concat U).joints).obj (op ⦋d⦌) ∧
      s ∈ (left (pivot T.dimension U.dimension)).obj (op ⦋d⦌)) ∨
      (s ∈ (complex.{u} (T.concat U).joints).obj (op ⦋d⦌) ∧
      s ∈ (right (pivot T.dimension U.dimension)).obj (op ⦋d⦌)) ↔ _
  constructor
  · rintro (h | h)
    · exact h.1
    · exact h.1
  · intro hs
    have h := concat_le_union.{u} T U _ hs
    rcases h with hl | hr
    · exact Or.inl ⟨hs, hl⟩
    · exact Or.inr ⟨hs, hr⟩

/-- Both entire original pieces intersect in precisely the same native pivot. -/
theorem concatPieces_inf (T U : Data) :
    concatLeftPiece.{u} T U ⊓ concatRightPiece T U =
      stdSimplex.face {pivot T.dimension U.dimension} := by
  have h : stdSimplex.face {pivot T.dimension U.dimension} ≤
      complex.{u} (T.concat U).joints := by
    rintro ⟨⟨d⟩⟩ s hs
    apply (mem_complex_iff _ _).mpr
    intro j _hj
    have hv : ∀ i, s i = pivot T.dimension U.dimension := by
      intro i
      exact Finset.mem_singleton.mp ((stdSimplex.mem_face_iff _ _).mp hs i)
    rcases le_total (pivot T.dimension U.dimension) j with hl | hr
    · exact Or.inl (fun i => (hv i).le.trans hl)
    · exact Or.inr (fun i => hr.trans (hv i).ge)
  ext ⟨⟨d⟩⟩ s
  change ((s ∈ (complex.{u} (T.concat U).joints).obj (op ⦋d⦌) ∧
      s ∈ (left (pivot T.dimension U.dimension)).obj (op ⦋d⦌)) ∧
      (s ∈ (complex.{u} (T.concat U).joints).obj (op ⦋d⦌) ∧
      s ∈ (right (pivot T.dimension U.dimension)).obj (op ⦋d⦌))) ↔ _
  have hi := congrArg (fun A : (Δ[T.dimension + U.dimension] : SSet.{u}).Subcomplex =>
    s ∈ A.obj (op ⦋d⦌)) (intersection.{u} (pivot T.dimension U.dimension))
  constructor
  · intro hs
    exact hi.mp ⟨hs.1.2, hs.2.2⟩
  · intro hs
    have hp := hi.mpr hs
    exact ⟨⟨h _ hs, hp.1⟩, ⟨h _ hs, hp.2⟩⟩

end SSet.OriginalNecklace
