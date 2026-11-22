/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceFirstCrossingIndex

/-!
# The complete original first-crossing pairing

Both full original simplex directions determine their same actual first
crossed joint. The existing canonical pivot pairing then determines the
entire index. Every native missing simplex is covered, including all
original ordinal dimensions and coefficient universes.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace.CrossedJoints

namespace Index

variable {n : ℕ} {J : Finset (Fin (n + 1))}

/-- The entire original face determines its first crossed joint and full original index. -/
theorem ext_original {s t : Index.{u} J}
    (h : SSet.S.mk s.bead.original.val = SSet.S.mk t.bead.original.val) : s = t := by
  cases s with
  | mk sp sb sj sf =>
    cases t with
    | mk tp tb tj tf =>
      have hd := SSet.S.dim_eq_of_mk_eq h
      let s : Index.{u} J := ⟨sp, sb, sj, sf⟩
      let t : Index.{u} J := ⟨tp, tb, tj, tf⟩
      have hc : crossed J (stdSimplex.nonDegenerateEquiv' sb.original).val =
          crossed J (stdSimplex.nonDegenerateEquiv' tb.original).val := by
        cases sb with
        | mk sd sx sm sl sr =>
          cases tb with
          | mk td tx tm tl tr =>
            change sd = td at hd
            subst td
            have hx : sx = tx := Subtype.ext ((SSet.S.ext_iff _ _).mp h)
            change crossed J (stdSimplex.nonDegenerateEquiv' sx).val =
              crossed J (stdSimplex.nonDegenerateEquiv' tx).val
            rw [hx]
      have hp : sp = tp :=
        le_antisymm (sf tp (hc.symm ▸ t.pivot_crossed))
          (tf sp (hc ▸ s.pivot_crossed))
      subst tp
      have hb : sb = tb := OriginalTwoBead.Index.ext_original h
      subst tb
      rfl

/-- The whole original paired simplex determines its same first crossed joint and full original index. -/
theorem injective_paired {s t : Index.{u} J}
    (h : SSet.S.mk s.bead.paired.val = SSet.S.mk t.bead.paired.val) : s = t := by
  cases s with
  | mk sp sb sj sf =>
    cases t with
    | mk tp tb tj tf =>
      have hd := Nat.succ.inj (SSet.S.dim_eq_of_mk_eq h)
      let s : Index.{u} J := ⟨sp, sb, sj, sf⟩
      let t : Index.{u} J := ⟨tp, tb, tj, tf⟩
      have hc : crossed J (stdSimplex.nonDegenerateEquiv' sb.paired).val =
          crossed J (stdSimplex.nonDegenerateEquiv' tb.paired).val := by
        cases sb with
        | mk sd sx sm sl sr =>
          cases tb with
          | mk td tx tm tl tr =>
            change sd = td at hd
            subst td
            have hx : (OriginalTwoBead.Index.paired ⟨sd, sx, sm, sl, sr⟩) =
                (OriginalTwoBead.Index.paired ⟨sd, tx, tm, tl, tr⟩) :=
              Subtype.ext ((SSet.S.ext_iff _ _).mp h)
            exact congrArg (fun x => crossed J (stdSimplex.nonDegenerateEquiv' x).val) hx
      have hc' : crossed J (stdSimplex.nonDegenerateEquiv' sb.original).val =
          crossed J (stdSimplex.nonDegenerateEquiv' tb.original).val :=
        s.crossed_paired.symm.trans (hc.trans t.crossed_paired)
      have hp : sp = tp :=
        le_antisymm (sf tp (hc'.symm ▸ t.pivot_crossed))
          (tf sp (hc' ▸ s.pivot_crossed))
      subst tp
      have hb : sb = tb := OriginalTwoBead.Index.injective_paired h
      subst tb
      rfl

/-- A same original paired simplex cannot be any original missing face. -/
theorem paired_ne_original (s t : Index.{u} J) :
    SSet.S.mk s.bead.paired.val ≠ SSet.S.mk t.bead.original.val := by
  intro h
  have hd := SSet.S.dim_eq_of_mk_eq h
  have hc : crossed J (stdSimplex.nonDegenerateEquiv' s.bead.paired).val =
      crossed J (stdSimplex.nonDegenerateEquiv' t.bead.original).val := by
    cases s with
    | mk sp sb sj sf =>
      cases sb with
      | mk sd sx sm sl sr =>
        cases t with
        | mk tp tb tj tf =>
          cases tb with
          | mk td tx tm tl tr =>
            change sd + 1 = td at hd
            subst td
            have hx : (OriginalTwoBead.Index.paired ⟨sd, sx, sm, sl, sr⟩) = tx :=
              Subtype.ext ((SSet.S.ext_iff _ _).mp h)
            exact congrArg (fun x => crossed J (stdSimplex.nonDegenerateEquiv' x).val) hx
  have hc' := s.crossed_paired.symm.trans hc
  have hp : s.pivot = t.pivot :=
    le_antisymm (s.first _ (hc'.symm ▸ t.pivot_crossed))
      (t.first _ (hc' ▸ s.pivot_crossed))
  have ht : t.pivot ∈ (stdSimplex.nonDegenerateEquiv' t.bead.original).val := by
    have hm : s.pivot ∈ (stdSimplex.nonDegenerateEquiv' s.bead.paired).val := by
      rw [s.bead.support_paired]
      exact Finset.mem_insert_self _ _
    obtain ⟨i, hi⟩ := (stdSimplex.nonDegenerateEquiv'_iff _ _).mp hm
    have hx : ∃ j, t.bead.original.val j = t.pivot := by
      cases s with
      | mk sp sb sj sf =>
        cases sb with
        | mk sd sx sm sl sr =>
          cases t with
          | mk tp tb tj tf =>
            cases tb with
            | mk td tx tm tl tr =>
              change sd + 1 = td at hd
              subst td
              have he := (SSet.S.ext_iff _ _).mp h
              exact ⟨i, (congrArg (fun x : (Δ[n] : SSet.{u}) _⦋sd + 1⦌ => x i) he).symm.trans
                (hi.trans hp)⟩
    exact (stdSimplex.nonDegenerateEquiv'_iff _ _).mpr hx
  exact t.bead.missing ht

end Index

end SSet.OriginalNecklace.CrossedJoints
