/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceCutAmbientHomSquares
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceAmbientIntervalComposition
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceWholeBeadLift
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceWholeBeadNormalization

/-!
# Genuine full original coefficient lifts for EVERY native necklace

Every complete original flag containing all original joints has an
actual full raw Hom preimage under the SAME native ambient map. The
proof cuts at the first positive original bead and recurses on the
strictly smaller original suffix. Original endpoint maps, complete
coefficients and actual raw composition are retained; no lift or weak
comparison outcome is supplied as a hypothesis.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceHom

open SSet.OriginalNecklace OriginalBeadInterval SimplicialEnrichment

private theorem coefficient_lift_from_cuts (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints)
    (q : SimplexCategoryᵒᵖ) (p : (fullCoefficient.{u} T).obj q)
    (l : (hom (Cut.leftData T j hj).object.{u} (sourceVertex (Cut.leftData T j hj))
      (targetVertex (Cut.leftData T j hj))).obj q)
    (r : (hom (Cut.rightData T j hj).object.{u} (sourceVertex (Cut.rightData T j hj))
      (targetVertex (Cut.rightData T j hj))).obj q)
    (hl : (ambientHomMap (Cut.leftData T j hj)).app q l = (leftJointCoefficient T j hj p).val)
    (hr : (ambientHomMap (Cut.rightData T j hj)).app q r = (rightJointCoefficient T j hj p).val) :
    ∃ a : (hom T.object.{u} (sourceVertex T) (targetVertex T)).obj q,
      (ambientHomMap T).app q a = p.val := by
  let a : (hom T.object.{u} (sourceVertex T) (targetVertex T)).obj q :=
    (eComp SSet.{u} (C := realization T.object.{u}) (sourceVertex T) (nativeVertex T j) (targetVertex T)).app q
      ((leftCutHomMap T j hj).app q l, (rightCutHomMap T j hj).app q r)
  have hL := ConcreteCategory.congr_hom (congr_app (leftCutHomMap_ambient.{u} T j hj) q) l
  have hR := ConcreteCategory.congr_hom (congr_app (rightCutHomMap_ambient.{u} T j hj) q) r
  have hL' : (ambientIntervalMap T 0 j).app q ((leftCutHomMap T j hj).app q l) =
      (homIso.{u} 0 j (Fin.zero_le j)).hom.app q (leftJointCoefficient T j hj p).val :=
    hL.trans (congrArg ((homIso.{u} 0 j (Fin.zero_le j)).hom.app q) hl)
  have hR' : (ambientIntervalMap T j (Fin.last T.dimension)).app q ((rightCutHomMap T j hj).app q r) =
      (homIso.{u} j (Fin.last T.dimension) (Fin.le_last j)).hom.app q
        (rightJointCoefficient T j hj p).val :=
    hR.trans (congrArg ((homIso.{u} j (Fin.last T.dimension) (Fin.le_last j)).hom.app q) hr)
  have hc := ambientIntervalMap_composition_app.{u} T 0 j (Fin.last T.dimension) q
    ((leftCutHomMap T j hj).app q l) ((rightCutHomMap T j hj).app q r)
  refine ⟨a, hc.trans ?_⟩
  exact (congrArg
    ((CompositionFace.composition (ULift.up.{u} (0 : Fin (T.dimension + 1))) (ULift.up.{u} j)
      (ULift.up.{u} (Fin.last T.dimension))).app q)
    (congrArg₂ Prod.mk hL' hR')).trans (jointCoefficient_composition T j hj p)

/-- EVERY complete original joint flag has a genuine actual full raw Hom lift under the SAME native ambient map. -/
theorem exists_native_coefficient_lift (T : Data) (q : SimplexCategoryᵒᵖ)
    (p : (fullCoefficient.{u} T).obj q) :
    ∃ a : (hom T.object.{u} (sourceVertex T) (targetVertex T)).obj q,
      (ambientHomMap T).app q a = p.val := by
  have H : ∀ n : ℕ, ∀ (S : Data), S.dimension = n → ∀ (q : SimplexCategoryᵒᵖ)
      (p : (fullCoefficient.{u} S).obj q),
      ∃ a : (hom S.object.{u} (sourceVertex S) (targetVertex S)).obj q,
        (ambientHomMap S).app q a = p.val := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hn q p
      by_cases h0 : S.dimension = 0
      · exact exists_wholeBead_coefficient_lift S (OriginalFlaggedNecklace.zero_necklace_joints S h0) q p.val
      · let i : Fin S.dimension := ⟨0, Nat.pos_of_ne_zero h0⟩
        obtain ⟨a, j, hcj, ha, _hj⟩ := exists_bead_at_edge S i
        have ha0 : a = 0 := by
          apply Fin.ext
          change a.val = 0
          have ha' : a.val ≤ 0 := ha
          omega
        subst a
        let L := Cut.leftData S j hcj.target
        let R := Cut.rightData S j hcj.target
        obtain ⟨l, hl⟩ := exists_wholeBead_coefficient_lift L (Cut.leftJoints_of_first_bead hcj) q
          (leftJointCoefficient S j hcj.target p).val
        obtain ⟨r, hr⟩ := ih R.dimension ((Cut.rightDimension_lt S j hcj.positive).trans_eq hn) R rfl q
          (rightJointCoefficient S j hcj.target p)
        exact coefficient_lift_from_cuts S j hcj.target q p l r hl hr
  exact H T.dimension T rfl q p

end CategoryTheory.CoherentRealization.OriginalNecklaceHom
