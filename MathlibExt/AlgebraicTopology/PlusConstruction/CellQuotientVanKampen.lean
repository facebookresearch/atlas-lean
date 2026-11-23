/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.CellAnnulusAdjustment

/-!
# The actual quotient functor on the two-cell attachment

Apply the genuine fundamental-groupoid van Kampen universal property to the
constructed collar cover, adjusted outer functor and literal constant inner
functor. Their derived strict overlap equality constructs a quotient-valued
functor on the original two-cell attachment with exact outer and inner
restriction equations.

The actual original inclusion factors through the outer region. Its global
restriction is therefore the normalized based functor for the original
quotient homomorphism. Evaluating the global End map at the actual included
basepoint gives the reverse factorization of the original inclusion map
through `QuotientGroup.mk'`.

No global functor, restriction, factorization, kernel, surjectivity or
quotient-isomorphism witness is supplied as input. Connectedness and perfectness are
not used in this local quotient construction.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology Topology.CWComplex
open MathlibExt.Topology.Homotopy

universe u

namespace AlgebraicTopology.CellQuotientVanKampen

variable (X : TopCat.{u}) (x : X)
variable (P : Subgroup (FundamentalGroup X x)) [P.Normal]

/-- The actual cover data admits a global quotient-valued groupoid functor with both
prescribed restrictions. -/
theorem quotientFunctor_exists :
    ∃ F : FundamentalGroupoid (LoopCellAttachment.space X x P) ⥤
        SingleObj (FundamentalGroup X x ⧸ P),
      FundamentalGroupoid.map
          (MathlibExt.Topology.Homotopy.VanKampenWanted.inclusionSub
            (CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P))) ⋙ F =
          CellAnnulusAdjustment.adjustedOuterFunctor X x P ∧
        FundamentalGroupoid.map
          (MathlibExt.Topology.Homotopy.VanKampenWanted.inclusionSub
            (CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P))) ⋙ F =
          CellAnnulusAdjustment.innerFunctor X x P := by
  exact
    (VanKampenWanted.seifert_vanKampen_fundamentalGroupoid_universalProperty
        (CellCollarCover.isOpen_U X 1 (LoopCellAttachment.attachingMap X x P))
        (CellCollarCover.isOpen_V X 1 (LoopCellAttachment.attachingMap X x P))
        (CellCollarCover.U_union_V X 1 (LoopCellAttachment.attachingMap X x P))
        (CellAnnulusAdjustment.adjustedOuterFunctor X x P)
        (CellAnnulusAdjustment.innerFunctor X x P)
        (CellAnnulusAdjustment.adjustedOuterFunctor_inner_compatibility X x P)).2.exists

/-- The actual global quotient-valued functor supplied by the constructed open-cover data. -/
def quotientFunctor :
    FundamentalGroupoid (LoopCellAttachment.space X x P) ⥤
      SingleObj (FundamentalGroup X x ⧸ P) :=
  (quotientFunctor_exists X x P).choose

/-- The global functor restricts exactly to the adjusted outer functor. -/
theorem quotientFunctor_restrict_outer :
    FundamentalGroupoid.map
        (MathlibExt.Topology.Homotopy.VanKampenWanted.inclusionSub
          (CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P))) ⋙
      quotientFunctor X x P =
        CellAnnulusAdjustment.adjustedOuterFunctor X x P :=
  by simpa [quotientFunctor] using (quotientFunctor_exists X x P).choose_spec.1

/-- The global functor restricts exactly to the literal constant inner functor. -/
theorem quotientFunctor_restrict_inner :
    FundamentalGroupoid.map
        (MathlibExt.Topology.Homotopy.VanKampenWanted.inclusionSub
          (CellCollarCover.V X 1 (LoopCellAttachment.attachingMap X x P))) ⋙
      quotientFunctor X x P =
        CellAnnulusAdjustment.innerFunctor X x P :=
  by simpa [quotientFunctor] using (quotientFunctor_exists X x P).choose_spec.2

omit [P.Normal] in
/-- The original inclusion into the attachment is exactly inclusion into U followed
by the canonical subtype inclusion. -/
theorem inclusionSub_comp_inclusionU :
    (MathlibExt.Topology.Homotopy.VanKampenWanted.inclusionSub
      (CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P))).comp
        (CellCollarDeformation.inclusionU X 1
          (LoopCellAttachment.attachingMap X x P)).hom =
      (LoopCellAttachment.inclusion X x P).hom := by
  apply ContinuousMap.ext
  intro y
  rfl

/-- Restriction of the global functor along the actual original inclusion is
the exact normalized quotient-valued based functor. -/
theorem quotientFunctor_originalInclusion :
    FundamentalGroupoid.map (LoopCellAttachment.inclusion X x P).hom ⋙
      quotientFunctor X x P =
        Groupoid.basedFunctor (FundamentalGroupoid.mk x) (QuotientGroup.mk' P) := by
  let i : C(X, CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P)) :=
    (CellCollarDeformation.inclusionU X 1
      (LoopCellAttachment.attachingMap X x P)).hom
  let j : C(CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P),
      LoopCellAttachment.space X x P) :=
    MathlibExt.Topology.Homotopy.VanKampenWanted.inclusionSub
      (CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P))
  let F := quotientFunctor X x P
  have hComp : j.comp i = (LoopCellAttachment.inclusion X x P).hom :=
    inclusionSub_comp_inclusionU X x P
  have hMap :
      FundamentalGroupoid.map (LoopCellAttachment.inclusion X x P).hom =
        FundamentalGroupoid.map i ⋙ FundamentalGroupoid.map j := by
    exact (congrArg
      (fun f : C(X, LoopCellAttachment.space X x P) => FundamentalGroupoid.map f)
      hComp).symm.trans (FundamentalGroupoid.map_comp j i)
  calc
    _ = (FundamentalGroupoid.map i ⋙ FundamentalGroupoid.map j) ⋙ F :=
      congrArg (fun G : FundamentalGroupoid X ⥤
        FundamentalGroupoid (LoopCellAttachment.space X x P) => G ⋙ F) hMap
    _ = FundamentalGroupoid.map i ⋙ (FundamentalGroupoid.map j ⋙ F) := rfl
    _ = FundamentalGroupoid.map i ⋙
        CellAnnulusAdjustment.adjustedOuterFunctor X x P :=
      congrArg
        (fun G : FundamentalGroupoid
            (CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P)) ⥤
              SingleObj (FundamentalGroup X x ⧸ P) =>
          FundamentalGroupoid.map i ⋙ G)
        (quotientFunctor_restrict_outer X x P)
    _ = _ := CellAnnulusAdjustment.adjustedOuterFunctor_originalInclusion X x P

/-- The global based End homomorphism at the actual included original basepoint. -/
def quotientEnd :
    FundamentalGroup (LoopCellAttachment.space X x P)
        (LoopCellAttachment.inclusion X x P x) →*
      (FundamentalGroup X x ⧸ P) :=
  (SingleObj.toEnd (FundamentalGroup X x ⧸ P)).symm.toMonoidHom.comp
    ((quotientFunctor X x P).mapEnd
      (FundamentalGroupoid.mk (LoopCellAttachment.inclusion X x P x)))

/-- The global End homomorphism gives the actual reverse factorization of the
original inclusion map through the original quotient. -/
theorem quotientEnd_comp_pi1Map :
    (quotientEnd X x P).comp (LoopCellAttachment.pi1Map X x P) =
      QuotientGroup.mk' P := by
  apply MonoidHom.ext
  intro q
  have hFunctor := quotientFunctor_originalInclusion X x P
  have hq := congrArg
    (fun F : FundamentalGroupoid X ⥤ SingleObj (FundamentalGroup X x ⧸ P) =>
      (F.map q.asHom : FundamentalGroup X x ⧸ P)) hFunctor
  change quotientEnd X x P
      (FundamentalGroup.mapOfEq (LoopCellAttachment.inclusion X x P).hom rfl q) =
    QuotientGroup.mk' P q
  rw [FundamentalGroup.mapOfEq_rfl]
  change (quotientFunctor X x P).map
      ((FundamentalGroupoid.map (LoopCellAttachment.inclusion X x P).hom).map q.asHom) =
    QuotientGroup.mk' P q
  exact hq.trans
    (Groupoid.basedFunctor_map_end (FundamentalGroupoid.mk x) (QuotientGroup.mk' P) q)

/-- Evaluation of the reverse factorization retains the same original element. -/
theorem quotientEnd_pi1Map (q : FundamentalGroup X x) :
    quotientEnd X x P (LoopCellAttachment.pi1Map X x P q) = QuotientGroup.mk' P q :=
  DFunLike.congr_fun (quotientEnd_comp_pi1Map X x P) q

/-- The exact reverse factorization gives the reverse inclusion from the
kernel of the original based map to the prescribed subgroup. -/
theorem ker_pi1Map_le :
    (LoopCellAttachment.pi1Map X x P).ker ≤ P := by
  intro q hq
  have hq1 : LoopCellAttachment.pi1Map X x P q = 1 :=
    MonoidHom.mem_ker.mp hq
  have hmk : QuotientGroup.mk' P q = 1 := by
    rw [← quotientEnd_pi1Map X x P q, hq1, map_one]
  exact (QuotientGroup.eq_one_iff q).mp hmk

/-- The actual original inclusion has exactly the prescribed kernel. -/
theorem ker_pi1Map :
    (LoopCellAttachment.pi1Map X x P).ker = P :=
  le_antisymm (ker_pi1Map_le X x P)
    (LoopCellAttachment.subgroup_le_ker X x P)

end AlgebraicTopology.CellQuotientVanKampen

end

end
