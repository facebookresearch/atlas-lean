/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalTwoBeadPairing
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic

/-!
# Inner anodyneness of the full original two-bead inclusion

For a fixed original pivot, every equal-dimensional ancestral face must
delete that pivot itself. Thus nonidentity ancestry strictly decreases
dimension, and the native constant weak rank proves regularity.
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalTwoBead

/-- A missing-pivot face of a paired simplex deletes the same original pivot. -/
theorem Index.face_eq_original_index {n : ℕ} {k : Fin (n + 1)}
    (s t : Index.{u} k) (hd : s.dim = t.dim)
    (i : Fin (t.dim + 2))
    (h : SSet.S.mk ((Δ[n] : SSet.{u}).δ i t.paired.val) =
      SSet.S.mk s.original.val) : i = t.pivotIndex := by
  cases s with
  | mk sd sx sm sb sa =>
    cases t with
    | mk td tx tm tb ta =>
      change sd = td at hd
      subst td
      let t : Index.{u} k := ⟨sd, tx, tm, tb, ta⟩
      by_contra hi
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (Ne.symm hi)
      have hval : (Δ[n] : SSet.{u}).δ i t.paired.val = sx.val :=
        (SSet.S.ext_iff _ _).1 h
      apply sm
      apply (stdSimplex.nonDegenerateEquiv'_iff sx k).2
      refine ⟨j, ?_⟩
      rw [← hval, stdSimplex.δ_apply, hj]
      exact t.paired_pivotIndex

/-- Equal-dimensional original nonidentity ancestry is impossible. -/
theorem no_equal_dimension_ancestry {n : ℕ} (k : Fin (n + 1))
    {s t : (pairingCore.{u} k).ι}
    (h : (pairingCore k).AncestralRel s t)
    (hd : (pairingCore k).dim s = (pairingCore k).dim t) : False := by
  change Index.{u} k at s t
  have hface := h.2
  obtain ⟨f, hf, he⟩ := SSet.N.le_iff_exists_mono.1 hface.le
  change ⦋s.dim⦌ ⟶ ⦋t.dim + 1⦌ at f
  change (Δ[n] : SSet.{u}).map f.op t.paired.val =
    (Δ[n] : SSet.{u}).δ s.pivotIndex s.paired.val at he
  rw [s.distinguished_face] at he
  change s.dim = t.dim at hd
  cases s with
  | mk sd sx sm sb sa =>
    cases t with
    | mk td tx tm tb ta =>
      change sd = td at hd
      subst td
      let s : Index.{u} k := ⟨sd, sx, sm, sb, sa⟩
      let t : Index.{u} k := ⟨sd, tx, tm, tb, ta⟩
      let : Mono f := hf
      obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono f
      have hi : i = t.pivotIndex :=
        s.face_eq_original_index t rfl i ((SSet.S.ext_iff _ _).2 he)
      change (Δ[n] : SSet.{u}).δ i t.paired.val = s.original.val at he
      rw [hi, t.distinguished_face] at he
      exact h.1 (Index.ext_original ((SSet.S.ext_iff _ _).2 he.symm))

/-- The native constant weak rank retains every original pairing face. -/
noncomputable def weakRankFunction {n : ℕ} (k : Fin (n + 1)) :
    (pairingCore.{u} k).WeakRankFunction ℕ where
  rank _ := 0
  lt h hd := (no_equal_dimension_ancestry k h hd).elim

/-- The full original pairing is regular. -/
instance {n : ℕ} (k : Fin (n + 1)) : (pairingCore.{u} k).IsRegular :=
  (weakRankFunction k).isRegular

/-- The union of the two complete original simplex beads is inner anodyne. -/
theorem inclusion_innerAnodyne {n : ℕ} (k : Fin (n + 1)) :
    innerAnodyneExtensions (union.{u} k).ι :=
  (pairingCore k).pairing.innerAnodyneExtensions

end SSet.OriginalTwoBead
