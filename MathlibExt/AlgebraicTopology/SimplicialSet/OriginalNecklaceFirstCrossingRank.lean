/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceFirstCrossingCore

/-!
# Genuine rank and inner anodyneness of the original full necklace inclusion

An equal-dimensional nonidentity ancestral face strictly moves the
actual first crossed joint to the right. The finite original ordinal
distance from that joint to the terminal vertex is a weak rank. The
canonical full original pairing therefore proves that the same original
necklace inclusion is inner anodyne in every coefficient universe.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace.CrossedJoints

/-- A whole original face has crossed-joint set included in the same original paired simplex's crossings. -/
theorem crossed_face_subset {n d : ℕ} (J : Finset (Fin (n + 1)))
    (x : (Δ[n] : SSet.{u}).nonDegenerate (d + 1)) (i : Fin (d + 2)) :
    crossed J (stdSimplex.nonDegenerateEquiv' (stdSimplex.OriginalFaceSupport.face x i)).val ⊆
      crossed J (stdSimplex.nonDegenerateEquiv' x).val := by
  intro k hk
  obtain ⟨hJ, ⟨a, ha⟩, b, hb⟩ := (mem_crossed_support_iff _ _ _).mp hk
  exact (mem_crossed_support_iff _ _ _).mpr
    ⟨hJ, ⟨i.succAbove a, ha⟩, i.succAbove b, hb⟩

/-- Equal-dimensional original ancestry strictly moves the same first crossed joint to the right. -/
theorem pivot_lt_of_equal_dimension_ancestry {n : ℕ} (J : Finset (Fin (n + 1)))
    {s t : (pairingCore.{u} J).ι}
    (h : (pairingCore J).AncestralRel s t)
    (hd : (pairingCore J).dim s = (pairingCore J).dim t) : t.pivot < s.pivot := by
  change Index.{u} J at s t
  obtain ⟨f, hf, he⟩ := SSet.N.le_iff_exists_mono.mp h.2.le
  change ⦋s.bead.dim⦌ ⟶ ⦋t.bead.dim + 1⦌ at f
  change (Δ[n] : SSet.{u}).map f.op t.bead.paired.val =
    (Δ[n] : SSet.{u}).δ s.bead.pivotIndex s.bead.paired.val at he
  rw [s.bead.distinguished_face] at he
  change s.bead.dim = t.bead.dim at hd
  cases s with
  | mk sp sb sj sf =>
    cases sb with
    | mk sd sx sm sl sr =>
      cases t with
      | mk tp tb tj tf =>
        cases tb with
        | mk td tx tm tl tr =>
          change sd = td at hd
          subst td
          let s : Index.{u} J := ⟨sp, ⟨sd, sx, sm, sl, sr⟩, sj, sf⟩
          let t : Index.{u} J := ⟨tp, ⟨sd, tx, tm, tl, tr⟩, tj, tf⟩
          let _ : Mono f := hf
          obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono f
          have he' : (Δ[n] : SSet.{u}).δ i t.bead.paired.val = sx.val := he
          have hsx : stdSimplex.OriginalFaceSupport.face t.bead.paired i = sx :=
            Subtype.ext he'
          have hs : sp ∈ crossed J (stdSimplex.nonDegenerateEquiv' t.bead.paired).val :=
            crossed_face_subset J t.bead.paired i
              (hsx.symm ▸ s.pivot_crossed)
          have hle : tp ≤ sp := tf sp (t.crossed_paired ▸ hs)
          have hne : tp ≠ sp := by
            intro hp
            subst tp
            have hface : i = t.bead.pivotIndex :=
              OriginalTwoBead.Index.face_eq_original_index s.bead t.bead rfl i
                ((SSet.S.ext_iff _ _).mpr he')
            apply h.1
            exact Index.ext_original ((SSet.S.ext_iff _ _).mpr
              ((t.bead.distinguished_face).symm.trans (hface ▸ he'))).symm
          change tp < sp
          exact lt_of_le_of_ne hle hne

/-- The actual remaining original ordinal distance is a genuine weak rank for the full original pairing. -/
def weakRankFunction {n : ℕ} (J : Finset (Fin (n + 1))) :
    (pairingCore.{u} J).WeakRankFunction ℕ where
  rank s := n - s.pivot.val
  lt {s t} h hd := by
    have hp := pivot_lt_of_equal_dimension_ancestry J h hd
    change t.pivot.val < s.pivot.val at hp
    have hs := s.pivot.isLt
    have ht := t.pivot.isLt
    change n - s.pivot.val < n - t.pivot.val
    omega

/-- The full original first-crossed-joint pairing is genuinely regular. -/
instance {n : ℕ} (J : Finset (Fin (n + 1))) : (pairingCore.{u} J).IsRegular :=
  (weakRankFunction J).isRegular

/-- The same full original necklace inclusion is genuinely inner anodyne, with all native joints retained. -/
theorem inclusion_innerAnodyne {n : ℕ} (J : Finset (Fin (n + 1))) :
    SSet.innerAnodyneExtensions (complex.{u} J).ι :=
  (pairingCore J).pairing.innerAnodyneExtensions

end SSet.OriginalNecklace.CrossedJoints
