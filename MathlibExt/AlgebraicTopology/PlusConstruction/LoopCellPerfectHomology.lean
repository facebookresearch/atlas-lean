/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.Abelianization.PerfectKernel
public import MathlibExt.Topology.Homotopy.TopCat.HurewiczOne
public import MathlibExt.AlgebraicTopology.PlusConstruction.CellFundamentalGroupQuotient
public import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellRelativeHomology

/-!
# The original perfect-subgroup attachment in degrees one and two

Weibel, *The K-book*, Exercise IV.1.4 (printed p. 273), is the primary
source for this two-cell homology step. The proof derives the H₁ and relative
H₂ conclusions used in its direct-sum clause. These homology lifts are not
claimed spherical; the later spherical and three-cell assertions remain open.

Perfectness of the actual kernel makes the original inclusion an integral
H₁ isomorphism. Its actual pair boundary in degree two is therefore zero,
and the actual absolute-to-relative H₂ map is epic. Every original relative
cell generator has an absolute homology lift. Spherical lifts and the
quotient-group-ring three-cell correction remain separate constructions.
-/

public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Topology
open TopPair.HomologyTheoryData.IsExact

universe u

namespace AlgebraicTopology.LoopCellAttachment

variable (X : TopCat.{u}) (x : X)
variable (P : Subgroup (FundamentalGroup X x))

/-- The actual natural-graded projection to relative homology is induced by
 the quotient of singular chains of the original attachment pair. -/
def absoluteToRelativeHomologyTwo :
    (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).obj (space X x P)) ⟶
      (relativeSingularHomologyFunctor AddCommGrpCat.{u}
        (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).obj (relativePair X x P) :=
  HomologicalComplex.homologyMap
    (relativeSingularChainQuotient AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u}) (relativePair X x P)) 2

/-- The actual relative degree-two boundary in natural grading, through the
 canonical integer/natural comparison isomorphisms. -/
def relativeBoundaryHomologyTwo :
    (relativeSingularHomologyFunctor AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).obj (relativePair X x P) ⟶
        (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).obj X) :=
  ((relativeSingularHomologyNatToIntIso AddCommGrpCat.{u}
    (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).app (relativePair X x P)).inv ≫
    (singularHomologyIntData AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u})).boundary 2 (relativePair X x P) ≫
        ((singularHomologyNatToIntIso AddCommGrpCat.{u}
          (singularIntegralCoefficients : AddCommGrpCat.{u}) 1).app X).hom

/-- The natural H₂ projection is exactly the actual integer pair projection
 transported by the canonical comparison maps. -/
theorem absoluteToRelativeHomologyTwo_eq_int_projection :
    absoluteToRelativeHomologyTwo X x P =
      ((singularHomologyNatToIntIso AddCommGrpCat.{u}
        (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).app (space X x P)).inv ≫
        (singularHomologyIntData AddCommGrpCat.{u}
          (singularIntegralCoefficients : AddCommGrpCat.{u})).toRelative 2
            (relativePair X x P) ≫
          ((relativeSingularHomologyNatToIntIso AddCommGrpCat.{u}
            (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).app
              (relativePair X x P)).hom :=
  (singularHomologyIntData_toRelative_natAgreement AddCommGrpCat.{u}
    (singularIntegralCoefficients : AddCommGrpCat.{u}) 2 (relativePair X x P)).symm

section PerfectKernel

variable [hX : PathConnectedSpace X] [hP : P.Normal] [hperfect : Group.IsPerfect P]

include hX hP hperfect

/-- The original inclusion induces an integral H₁ isomorphism, using its
 actual quotient fundamental-group map and perfect kernel. -/
theorem inclusionHomologyOne_isIso_of_perfect :
    IsIso (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).map (inclusion X x P)) := by
  let Y := space X x P
  let i : X ⟶ Y := inclusion X x P
  let : PathConnectedSpace Y :=
    CellFamilyAttachment.pathConnectedSpace X 1 (attachingMap X x P)
  let φ := pi1Map X x P
  have hk : φ.ker = P := CellQuotientVanKampen.ker_pi1Map X x P
  let : Group.IsPerfect φ.ker := by
    rw [hk]
    infer_instance
  have hAb := Abelianization.map_bijective_of_surjective_of_isPerfect_ker
    φ (pi1Map_surjective X x P)
  let e := (MulEquiv.ofBijective (Abelianization.map φ) hAb).toAdditive
  let fAb := AddCommGrpCat.ofHom ((Abelianization.map φ).toAdditive)
  let eIso :
      AddCommGrpCat.of (Additive (Abelianization (FundamentalGroup X x))) ≅
        AddCommGrpCat.of (Additive (Abelianization (FundamentalGroup Y (i x)))) :=
    AddEquiv.toAddCommGrpIso
      (X := AddCommGrpCat.of (Additive (Abelianization (FundamentalGroup X x))))
      (Y := AddCommGrpCat.of (Additive (Abelianization (FundamentalGroup Y (i x))))) e
  have he : eIso.hom = fAb := by
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  have : IsIso fAb := by
    rw [← he]
    infer_instance
  have hn := TopCat.fundamentalGroupAbelianizationHomologyOneIso_hom_naturality i x
  change fAb ≫ (TopCat.fundamentalGroupAbelianizationHomologyOneIso Y (i x)).hom =
    (TopCat.fundamentalGroupAbelianizationHomologyOneIso X x).hom ≫
      (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).map i) at hn
  have : IsIso ((TopCat.fundamentalGroupAbelianizationHomologyOneIso X x).hom ≫
      (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).map i)) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (TopCat.fundamentalGroupAbelianizationHomologyOneIso X x).hom _

/-- The integer-graded H₁ map is the same original inclusion isomorphism. -/
theorem inclusionHomologyOneInt_isIso_of_perfect :
    IsIso ((singularHomologyIntData AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u})).subspaceMap 1
        (relativePair X x P)) := by
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let Y : TopCat.{u} := space X x P
  let i : X ⟶ Y := inclusion X x P
  let F : TopCat.{u} ⥤ AddCommGrpCat.{u} :=
    (singularHomologyFunctor AddCommGrpCat.{u} 1).obj R
  let G : TopCat.{u} ⥤ AddCommGrpCat.{u} :=
    singularHomologyIntFunctor AddCommGrpCat.{u} R ((1 : ℕ) : ℤ)
  let e : G ≅ F := singularHomologyNatToIntIso AddCommGrpCat.{u} R 1
  have : IsIso (F.map i) := inclusionHomologyOne_isIso_of_perfect X x P
  have hn : G.map i ≫ (e.app Y).hom = (e.app X).hom ≫ F.map i :=
    e.hom.naturality i
  have hIso : IsIso ((e.app X).hom ≫ F.map i) := by infer_instance
  have : IsIso (G.map i ≫ (e.app Y).hom) := hn.symm ▸ hIso
  change IsIso (G.map i)
  exact IsIso.of_isIso_comp_right (G.map i) (e.app Y).hom

/-- The actual integer relative H₂ boundary vanishes; no boundary-zero input is used. -/
theorem relativeBoundaryHomologyTwoInt_eq_zero_of_perfect :
    (singularHomologyIntData AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u})).boundary 2
        (relativePair X x P) = 0 := by
  let E := singularHomologyIntData AddCommGrpCat.{u}
    (singularIntegralCoefficients : AddCommGrpCat.{u})
  let A := relativePair X x P
  have : IsIso (E.subspaceMap ((2 : ℤ) - 1) A) := by
    change IsIso (E.subspaceMap 1 A)
    exact inclusionHomologyOneInt_isIso_of_perfect X x P
  apply (cancel_mono (E.subspaceMap ((2 : ℤ) - 1) A)).mp
  rw [boundary_comp_subspaceMap, Limits.zero_comp]

/-- The actual relative H₂ boundary in natural grading also vanishes. -/
theorem relativeBoundaryHomologyTwo_eq_zero_of_perfect :
    relativeBoundaryHomologyTwo X x P = 0 := by
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let A : TopPair.{u} := relativePair X x P
  let E : TopPair.HomologyTheoryData.{u} AddCommGrpCat.{u} :=
    singularHomologyIntData AddCommGrpCat.{u} R
  let eRelative :
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2).obj A ≅
        (E.Hₚ 2).obj A :=
    ((relativeSingularHomologyNatToIntIso AddCommGrpCat.{u} R 2).app A).symm
  let eAbsolute :
      (E.H ((2 : ℤ) - 1)).obj A.snd ≅
        (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj R).obj X) :=
    (singularHomologyNatToIntIso AddCommGrpCat.{u} R 1).app X
  have hBoundary : E.boundary 2 A =
      (0 : (E.Hₚ 2).obj A ⟶ (E.H ((2 : ℤ) - 1)).obj A.snd) :=
    relativeBoundaryHomologyTwoInt_eq_zero_of_perfect X x P
  have hDefinition : relativeBoundaryHomologyTwo X x P =
      eRelative.hom ≫ E.boundary 2 A ≫ eAbsolute.hom := rfl
  have hTransport := congrArg
    (fun f : (E.Hₚ 2).obj A ⟶ (E.H ((2 : ℤ) - 1)).obj A.snd =>
      eRelative.hom ≫ f ≫ eAbsolute.hom) hBoundary
  exact hDefinition.trans (hTransport.trans (by
    simp only [Limits.zero_comp, Limits.comp_zero]))

/-- Each original characteristic generator has zero actual connecting boundary. -/
theorem relativeGenerator_boundary_eq_zero_of_perfect (p : P) :
    relativeGenerator X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) p ≫
      relativeBoundaryHomologyTwo X x P = 0 := by
  rw [relativeBoundaryHomologyTwo_eq_zero_of_perfect X x P, Limits.comp_zero]

/-- The actual integer absolute-to-relative H₂ map is epic by the original pair exact sequence. -/
theorem absoluteToRelativeHomologyTwoInt_epi_of_perfect :
    Epi ((singularHomologyIntData AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u})).toRelative 2
        (relativePair X x P)) := by
  have h := exact_toRelative_boundary
    (singularHomologyIntData AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u})) 2 (relativePair X x P)
  exact h.epi_f (relativeBoundaryHomologyTwoInt_eq_zero_of_perfect X x P)

/-- The original natural-graded projection of singular chains is epic. -/
theorem absoluteToRelativeHomologyTwo_epi_of_perfect :
    Epi (absoluteToRelativeHomologyTwo X x P) := by
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let A : TopPair.{u} := relativePair X x P
  let E : TopPair.HomologyTheoryData.{u} AddCommGrpCat.{u} :=
    singularHomologyIntData AddCommGrpCat.{u} R
  let f : (E.H 2).obj A.fst ⟶ (E.Hₚ 2).obj A := E.toRelative 2 A
  let eAbsolute :
      (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj R).obj (space X x P)) ≅
        (E.H 2).obj A.fst :=
    ((singularHomologyNatToIntIso AddCommGrpCat.{u} R 2).app (space X x P)).symm
  let eRelative :
      (E.Hₚ 2).obj A ≅
        (relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2).obj A :=
    (relativeSingularHomologyNatToIntIso AddCommGrpCat.{u} R 2).app A
  have : Epi f := absoluteToRelativeHomologyTwoInt_epi_of_perfect X x P
  have hEpi : Epi (eAbsolute.hom ≫ f ≫ eRelative.hom) := by infer_instance
  have hProjection : absoluteToRelativeHomologyTwo X x P =
      eAbsolute.hom ≫ f ≫ eRelative.hom :=
    absoluteToRelativeHomologyTwo_eq_int_projection X x P
  exact hProjection.symm ▸ hEpi

/-- Every actual relative H₂ class has an original absolute H₂ preimage. -/
theorem absoluteToRelativeHomologyTwo_surjective_of_perfect :
    Function.Surjective (absoluteToRelativeHomologyTwo X x P) := by
  have : Epi (absoluteToRelativeHomologyTwo X x P) :=
    absoluteToRelativeHomologyTwo_epi_of_perfect X x P
  exact (AddCommGrpCat.epi_iff_surjective (absoluteToRelativeHomologyTwo X x P)).mp
    inferInstance

/-- The original pth relative characteristic class has an absolute homology lift.
 No choice is asserted to be spherical or canonical. -/
theorem exists_absoluteHomologyTwo_generator_lift_of_perfect (p : P) :
    ∃ a : (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).obj (space X x P)),
      absoluteToRelativeHomologyTwo X x P a =
        relativeGenerator X x P (singularIntegralCoefficients : AddCommGrpCat.{u}) p
          (ULift.up (1 : ℤ)) :=
  absoluteToRelativeHomologyTwo_surjective_of_perfect X x P _

end PerfectKernel

end AlgebraicTopology.LoopCellAttachment

end
