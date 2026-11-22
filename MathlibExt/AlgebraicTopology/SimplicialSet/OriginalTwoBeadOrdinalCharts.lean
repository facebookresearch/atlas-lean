/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalTwoBeadGluing

/-!
# Original ordinal charts of the two complete beads

Both charts are the canonical native representable-face isomorphisms.
Their inclusions read back the original prefix and suffix ordinal maps.
Zero-length beads and all arities remain included.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.OriginalTwoBead.OrdinalCharts

/-- The same original common vertex in the total bead ordinal. -/
def pivot (p q : ℕ) : Fin (p + q + 1) := ⟨p, by omega⟩

/-- The original initial ordinal embedding of the full first bead. -/
def prefixEmbedding (p q : ℕ) : Fin (p + 1) ↪o Fin (p + q + 1) :=
  Fin.castLEOrderEmb (by omega)

/-- The original shifted ordinal embedding of the full second bead. -/
def suffix (p q : ℕ) : Fin (q + 1) ↪o Fin (p + q + 1) where
  toFun i := ⟨p + i.val, by have := i.isLt; omega⟩
  inj' _ _ h := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))
  map_rel_iff' := by
    intro i j
    change p + i.val ≤ p + j.val ↔ i.val ≤ j.val
    omega

/-- The complete original first-bead face is ordered by its same original ordinal. -/
def leftOrderIso (p q : ℕ) :
    Fin (p + 1) ≃o (Finset.univ.filter
      (fun j : Fin (p + q + 1) => j ≤ pivot p q)) where
  toFun i := ⟨prefixEmbedding p q i, Finset.mem_filter.2
    ⟨Finset.mem_univ _, by change i.val ≤ p; have := i.isLt; omega⟩⟩
  invFun j := ⟨j.val.val, by
    have h := (Finset.mem_filter.1 j.property).2
    change j.val.val ≤ p at h
    omega⟩
  left_inv _ := Fin.ext rfl
  right_inv _ := Subtype.ext (Fin.ext rfl)
  map_rel_iff' := by intro i j; rfl

/-- The complete original second-bead face retains every shifted ordinal vertex. -/
def rightOrderIso (p q : ℕ) :
    Fin (q + 1) ≃o (Finset.univ.filter
      (fun j : Fin (p + q + 1) => pivot p q ≤ j)) where
  toFun i := ⟨suffix p q i, Finset.mem_filter.2
    ⟨Finset.mem_univ _, by change p ≤ p + i.val; omega⟩⟩
  invFun j := ⟨j.val.val - p, by
    have h := (Finset.mem_filter.1 j.property).2
    change p ≤ j.val.val at h
    have := j.val.isLt
    omega⟩
  left_inv i := Fin.ext (by change p + i.val - p = i.val; omega)
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    have h := (Finset.mem_filter.1 j.property).2
    change p ≤ j.val.val at h
    change p + (j.val.val - p) = j.val.val
    omega
  map_rel_iff' := by
    intro i j
    change p + i.val ≤ p + j.val ↔ i.val ≤ j.val
    omega

/-- The native full original first-bead face chart. -/
def leftIso (p q : ℕ) : (Δ[p] : SSet.{u}) ≅ (left (pivot p q) : SSet.{u}) :=
  stdSimplex.isoOfRepresentableBy
    (stdSimplex.faceRepresentableBy _ p (leftOrderIso p q))

/-- The native full original second-bead face chart. -/
def rightIso (p q : ℕ) : (Δ[q] : SSet.{u}) ≅ (right (pivot p q) : SSet.{u}) :=
  stdSimplex.isoOfRepresentableBy
    (stdSimplex.faceRepresentableBy _ q (rightOrderIso p q))

/-- The actual first-bead simplex operator. -/
def prefixOperator (p q : ℕ) : ⦋p⦌ ⟶ ⦋p + q⦌ :=
  SimplexCategory.Hom.mk (prefixEmbedding p q).toOrderHom

/-- The actual second-bead simplex operator. -/
def suffixOperator (p q : ℕ) : ⦋q⦌ ⟶ ⦋p + q⦌ :=
  SimplexCategory.Hom.mk (suffix p q).toOrderHom

/-- The first full chart retains the literal original prefix map. -/
theorem leftIso_inclusion (p q : ℕ) :
    (leftIso.{u} p q).hom ≫ (left (pivot p q)).ι =
      SSet.stdSimplex.map (prefixOperator p q) := by
  ext d x
  rfl

/-- The second full chart retains the literal original suffix map. -/
theorem rightIso_inclusion (p q : ℕ) :
    (rightIso.{u} p q).hom ≫ (right (pivot p q)).ι =
      SSet.stdSimplex.map (suffixOperator p q) := by
  ext d x
  rfl

/-- The original last vertex of the first bead is the original pivot. -/
theorem prefix_last (p q : ℕ) : prefixEmbedding p q (Fin.last p) = pivot p q :=
  Fin.ext rfl

/-- The original first vertex of the second bead is the same original pivot. -/
theorem suffix_zero (p q : ℕ) : suffix p q 0 = pivot p q :=
  Fin.ext (Nat.add_zero p)

/-- The total initial endpoint remains the original first endpoint. -/
theorem prefix_zero (p q : ℕ) : prefixEmbedding p q 0 = 0 :=
  Fin.ext rfl

/-- The total terminal endpoint remains the original last endpoint. -/
theorem suffix_last (p q : ℕ) :
    suffix p q (Fin.last q) = Fin.last (p + q) :=
  Fin.ext rfl

end SSet.OriginalTwoBead.OrdinalCharts
