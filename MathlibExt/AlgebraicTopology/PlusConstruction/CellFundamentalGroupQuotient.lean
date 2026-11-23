/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.CellAttachmentFundamentalSurjectivity

/-!
# The fundamental-group quotient of the actual two-cell attachment

The literal original inclusion is surjective on fundamental groups and its
kernel is exactly the prescribed normal subgroup. This file packages the
resulting quotient isomorphism while retaining the already constructed
quotient homomorphism as its forward map and the van Kampen quotient map as
its inverse.

Connectedness and perfectness are not used in this fundamental-group
calculation. They remain hypotheses of later plus-construction stages.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology

universe u

namespace AlgebraicTopology.LoopCellAttachment

variable (X : TopCat.{u}) (x : X)
variable (P : Subgroup (FundamentalGroup X x)) [P.Normal]

/-- The constructed quotient-valued End map is a left inverse of the
existing quotient homomorphism into the two-cell attachment. -/
theorem quotientEnd_comp_quotientPi1Map :
    (CellQuotientVanKampen.quotientEnd X x P).comp
        (quotientPi1Map X x P) =
      MonoidHom.id (FundamentalGroup X x ⧸ P) := by
  apply QuotientGroup.monoidHom_ext
  rw [MonoidHom.comp_assoc, quotientPi1Map_comp_mk,
    CellQuotientVanKampen.quotientEnd_comp_pi1Map, MonoidHom.id_comp]

/-- The existing quotient homomorphism is injective, by the exact kernel
calculation for the original inclusion. -/
theorem quotientPi1Map_injective :
    Function.Injective (quotientPi1Map X x P) :=
  (QuotientGroup.injective_lift_iff P
    (pi1Map X x P) (subgroup_le_ker X x P)).mpr
      (CellQuotientVanKampen.ker_pi1Map X x P).symm

/-- The existing quotient homomorphism is surjective, by surjectivity of
the literal original inclusion. -/
theorem quotientPi1Map_surjective :
    Function.Surjective (quotientPi1Map X x P) :=
  QuotientGroup.lift_surjective_of_surjective P
    (pi1Map X x P) (pi1Map_surjective X x P)
    (subgroup_le_ker X x P)

/-- The existing quotient homomorphism is bijective. -/
theorem quotientPi1Map_bijective :
    Function.Bijective (quotientPi1Map X x P) :=
  ⟨quotientPi1Map_injective X x P, quotientPi1Map_surjective X x P⟩

/-- Surjectivity upgrades the constructed left inverse to a right inverse
of the existing quotient homomorphism. -/
theorem quotientPi1Map_comp_quotientEnd :
    (quotientPi1Map X x P).comp
        (CellQuotientVanKampen.quotientEnd X x P) =
      MonoidHom.id
        (FundamentalGroup (space X x P) (inclusion X x P x)) := by
  apply MonoidHom.ext
  intro q
  obtain ⟨a, rfl⟩ := quotientPi1Map_surjective X x P q
  have hLeft := DFunLike.congr_fun
    (quotientEnd_comp_quotientPi1Map X x P) a
  have hLeft' : CellQuotientVanKampen.quotientEnd X x P
      (quotientPi1Map X x P a) = a := by
    simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using hLeft
  change quotientPi1Map X x P
      (CellQuotientVanKampen.quotientEnd X x P
        (quotientPi1Map X x P a)) =
    quotientPi1Map X x P a
  rw [hLeft']

/-- The canonical fundamental-group quotient equivalence for the actual
subgroup-indexed two-cell attachment. -/
def fundamentalGroupQuotientMulEquiv :
    FundamentalGroup X x ⧸ P ≃*
      FundamentalGroup (space X x P) (inclusion X x P x) :=
  QuotientGroup.liftEquiv P (pi1Map_surjective X x P)
    (CellQuotientVanKampen.ker_pi1Map X x P).symm

/-- The forward homomorphism of the quotient equivalence is exactly the
existing quotient homomorphism. -/
theorem fundamentalGroupQuotientMulEquiv_toMonoidHom :
    (fundamentalGroupQuotientMulEquiv X x P).toMonoidHom =
      quotientPi1Map X x P := by
  apply QuotientGroup.monoidHom_ext
  apply MonoidHom.ext
  intro q
  exact (QuotientGroup.liftEquiv_mk P
    (pi1Map_surjective X x P)
    (CellQuotientVanKampen.ker_pi1Map X x P).symm q).trans
      (quotientPi1Map_mk X x P q).symm

/-- The quotient equivalence sends every original quotient class to the
literal inclusion-induced fundamental-group class. -/
@[simp]
theorem fundamentalGroupQuotientMulEquiv_mk
    (q : FundamentalGroup X x) :
    fundamentalGroupQuotientMulEquiv X x P
        (q : FundamentalGroup X x ⧸ P) =
      pi1Map X x P q := by
  change (fundamentalGroupQuotientMulEquiv X x P).toMonoidHom
      (q : FundamentalGroup X x ⧸ P) = _
  rw [fundamentalGroupQuotientMulEquiv_toMonoidHom]
  rfl

/-- The inverse homomorphism of the quotient equivalence is exactly the
constructed van Kampen quotient End map. -/
theorem fundamentalGroupQuotientMulEquiv_symm_toMonoidHom :
    (fundamentalGroupQuotientMulEquiv X x P).symm.toMonoidHom =
      CellQuotientVanKampen.quotientEnd X x P := by
  apply MonoidHom.ext
  intro q
  apply (fundamentalGroupQuotientMulEquiv X x P).injective
  change fundamentalGroupQuotientMulEquiv X x P
      ((fundamentalGroupQuotientMulEquiv X x P).symm q) =
    fundamentalGroupQuotientMulEquiv X x P
      (CellQuotientVanKampen.quotientEnd X x P q)
  rw [(fundamentalGroupQuotientMulEquiv X x P).apply_symm_apply]
  change q = (fundamentalGroupQuotientMulEquiv X x P).toMonoidHom
      (CellQuotientVanKampen.quotientEnd X x P q)
  rw [fundamentalGroupQuotientMulEquiv_toMonoidHom]
  exact (DFunLike.congr_fun (quotientPi1Map_comp_quotientEnd X x P) q).symm

/-- Evaluation of the inverse quotient equivalence is the same constructed
van Kampen quotient class. -/
@[simp]
theorem fundamentalGroupQuotientMulEquiv_symm_apply
    (q : FundamentalGroup (space X x P) (inclusion X x P x)) :
    (fundamentalGroupQuotientMulEquiv X x P).symm q =
      CellQuotientVanKampen.quotientEnd X x P q :=
  DFunLike.congr_fun
    (fundamentalGroupQuotientMulEquiv_symm_toMonoidHom X x P) q

end AlgebraicTopology.LoopCellAttachment

end

end
