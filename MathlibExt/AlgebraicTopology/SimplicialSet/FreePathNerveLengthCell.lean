/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathNerveWordFiltration
import MathlibExt.Combinatorics.Quiver.PathPositionLength

/-!
# Actual original word-length cells

The complete original generator word gives its literal native Yoneda
simplex map. Every ordinal coefficient retains the SAME original
interval path. Its preimage of the previous total-length stage is the
union of the two original endpoint-deleting faces, with all native
vertices, coefficients and maps retained.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial
namespace CategoryTheory.FreePathNerveCoordinates
variable (V : Type u) [Quiver.{v} V]

/-- The actual full original path-position word supplies its SAME native Yoneda cell map. -/
def wordCell {x y : V} (p : Quiver.Path x y) :
    (Δ[p.length] : SSet.{max u v}) ⟶ nerve (Paths V) :=
  SSet.yonedaEquiv.symm (Quiver.Path.positionWord (V := V) p)

/-- EVERY complete original cell coefficient retains the SAME whole original ordinal restriction. -/
lemma wordCell_app {x y : V} (p : Quiver.Path x y) (n : ℕ)
    (a : (Δ[p.length] : SSet.{max u v}) _⦋n⦌) :
    (wordCell V p).app (op ⦋n⦌) a =
      (SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv a)).toFunctor ⋙
        Quiver.Path.positionWord (V := V) p := rfl

/-- Every SAME full original cell subword has the exact native original endpoint span length. -/
lemma wordCell_total_length {x y : V} (p : Quiver.Path x y) (n : ℕ)
    (a : (Δ[p.length] : SSet.{max u v}) _⦋n⦌) :
    (totalPath V n ((wordCell V p).app (op ⦋n⦌) a)).length =
      (a (Fin.last n)).val - (a (0 : Fin (n + 1))).val :=
  Quiver.Path.positionWord_map_length (V := V) p (homOfLE
    ((SSet.stdSimplex.asOrderHom a).monotone (Fin.zero_le (Fin.last n))))

/-- The complete SAME original cell preimage of the old length stage
is precisely its two original outer faces, including all original arities. -/
theorem wordCell_preimage_lengthStage {x y : V} (p : Quiver.Path x y) (k : ℕ)
    (hp : p.length = k + 1) :
    (lengthStage V k).preimage (wordCell V p) =
      SSet.stdSimplex.face {(0 : Fin (p.length + 1))}ᶜ ⊔
        SSet.stdSimplex.face {Fin.last p.length}ᶜ := by
  ext q a
  rcases q with ⟨⟨n⟩⟩
  change (totalPath V n ((wordCell V p).app (op ⦋n⦌) a)).length ≤ k ↔ _
  rw [wordCell_total_length]
  simp only [Subfunctor.max_obj, Set.mem_union, SSet.stdSimplex.mem_face_iff,
    Finset.mem_compl, Finset.mem_singleton]
  constructor
  · intro h
    by_cases h0 : a (0 : Fin (n + 1)) = 0
    · right
      intro i hi
      have hlast := SSet.stdSimplex.monotone_apply a (Fin.le_last i)
      have hbound := (a (Fin.last n)).isLt
      have h0val := congrArg Fin.val h0
      have hival := congrArg Fin.val hi
      change (a i).val = p.length at hival
      change (a i).val ≤ (a (Fin.last n)).val at hlast
      change (a (0 : Fin (n + 1))).val = 0 at h0val
      change (a (Fin.last n)).val < p.length + 1 at hbound
      omega
    · left
      intro i hi
      apply h0
      apply Fin.ext
      have hle := SSet.stdSimplex.monotone_apply a (Fin.zero_le i)
      have hiv := congrArg Fin.val hi
      change (a (0 : Fin (n + 1))).val ≤ (a i).val at hle
      change (a i).val = 0 at hiv
      omega
  · rintro (h0 | hlast)
    · have hz := h0 (0 : Fin (n + 1))
      have hlo := (a (0 : Fin (n + 1))).isLt
      have hhi := (a (Fin.last n)).isLt
      have hne : (a (0 : Fin (n + 1))).val ≠ 0 := fun he => hz (Fin.ext he)
      omega
    · have hz := hlast (Fin.last n)
      have hhi := (a (Fin.last n)).isLt
      have hne : (a (Fin.last n)).val ≠ p.length := fun he => hz (Fin.ext (by simpa using he))
      omega

end CategoryTheory.FreePathNerveCoordinates
