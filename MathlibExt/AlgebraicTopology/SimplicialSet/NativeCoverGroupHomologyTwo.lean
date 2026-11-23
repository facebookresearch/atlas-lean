/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.NativeCoverBarAugmentation
import MathlibExt.AlgebraicTopology.SimplicialSet.NativeCoverHomologyOne
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanSpectralSequence
import MathlibExt.AlgebraicTopology.SingularHomology.HomologyZero
import MathlibExt.CategoryTheory.CategoryHomology.Constant
import MathlibExt.CategoryTheory.CategoryHomology.CoefficientLinear
import MathlibExt.RepresentationTheory.Homological.GroupHomology.NerveComparison
import MathlibExt.Algebra.Homology.FirstQuadrantDegreeTwo

/-!
# Native integral group H2 from original-base H2

The actual cover supplies its canonical H0 augmentation and vanished H1
coefficient row. The existing BK second-page, constant-coefficient and
forgetful homology dictionaries identify the zero row with true native
group homology. The original total comparison and the first-quadrant
degree-two theorem then derive group H2 vanishing from original-base H2
vanishing. No row or cover-H2 vanishing is an input.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace SSet.KanComplex

/-- The actual native-cover H0 coefficient system is canonically constant,
with the original connected-cover augmentation as its component. -/
def nativeCoverHomologyZeroCoefficientIso (R : AddCommGrpCat.{u})
    (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    nativeCoverDeckFunctor X x ⋙ SSet.homologyFunctor R 0 ≅
      (Functor.const (SingleObj (End (SSet.FundamentalGroupoid.mk x)))).obj R := by
  letI : (nativeCover X x).IsConnected := nativeCover_isConnected (X := X) (x := x)
  let e₀ : (nativeCover X x).homology R 0 ≅ R := asIso ((nativeCover X x).homology₀ε R)
  exact NatIso.ofComponents (fun _ => e₀) (by
    intro j j' g
    change SSet.homologyMap (nativeCoverDeckMap g) R 0 ≫
        (nativeCover X x).homology₀ε R = (nativeCover X x).homology₀ε R ≫ 𝟙 R
    rw [Category.comp_id]
    exact SSet.homologyMap_comp_homology₀ε (nativeCoverDeckMap g) R)

/-- Every forward coefficient component is the canonical original H0 augmentation. -/
theorem nativeCoverHomologyZeroCoefficientIso_hom_app (R : AddCommGrpCat.{u})
    (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌)
    (j : SingleObj (End (SSet.FundamentalGroupoid.mk x))) :
    (nativeCoverHomologyZeroCoefficientIso R X x).hom.app j =
      (nativeCover X x).homology₀ε R := rfl

/-- The actual native integral zero row is the underlying abelian group of
Mathlib's genuine group homology with the original trivial coefficients. -/
def nativeCoverSecondPageZeroRowGroupHomologyIso (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) (p : ℕ) :
    ((SSet.bkHomologySpectralSequence
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
      (nativeCoverDeckFunctor X x)).page 2).X (p, 0) ≅
        (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u}).obj
          (groupHomology (Rep.trivial (ULift.{u} ℤ)
            (End (SSet.FundamentalGroupoid.mk x)) (ULift.{u} ℤ)) p) := by
  let k : Type u := ULift.{u} ℤ
  let Γ : Type u := End (SSet.FundamentalGroupoid.mk x)
  let R : AddCommGrpCat.{u} := AlgebraicTopology.singularIntegralCoefficients
  let F : ModuleCat.{u} k ⥤ AddCommGrpCat.{u} := forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}
  let N : SSet.{u} := CategoryTheory.nerve (SingleObj Γ)
  let A : ModuleCat.{u} k := ModuleCat.of k k
  letI : HasColimitsOfSize.{u, u} AddCommGrpCat.{u} :=
    AddCommGrpCat.hasColimitsOfSize.{u, u, u}
  letI : PreservesColimitsOfSize.{u, u} F := by
    change PreservesColimitsOfSize.{u, u} (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u})
    exact ModuleCat.forget₂PreservesColimitsOfSize (R := k)
  let c := (SSet.mapChainComplexFunctorIso.{u} F A).app N
  let e : F.obj (N.homology A p) ≅ N.homology (F.obj A) p :=
    ((HomologicalComplex.mapHomologyFunctorIso p F).app (N.chainComplex A)).symm ≪≫
      HomologicalComplex.homologyMapIso c p
  let eG : F.obj (groupHomology (Rep.trivial k Γ k) p) ≅ N.homology R p :=
    F.mapIso (groupHomology.trivialNerveHomologyIso k Γ p) ≪≫ e
  exact SSet.bkSecondPageCoefficientHomologyIso R (nativeCoverDeckFunctor X x) p 0 ≪≫
    (CategoryTheory.CategoryHomology.homologyWithCoefficientsFunctor
      (C := SingleObj Γ) (A := AddCommGrpCat.{u}) p).mapIso
        (nativeCoverHomologyZeroCoefficientIso R X x) ≪≫
      CategoryTheory.CategoryHomology.homologyWithConstantCoefficientsIso
        (SingleObj Γ) AddCommGrpCat.{u} R p ≪≫ eG.symm

/-- Actual native-cover H1 vanishing makes the whole integral first
coefficient row zero. Its degree-zero term is the H1-cover coinvariants. -/
theorem nativeCoverSecondPageOne_isZero (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) (p : ℕ) :
    IsZero (((SSet.bkHomologySpectralSequence
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
      (nativeCoverDeckFunctor X x)).page 2).X (p, 1)) := by
  let R : AddCommGrpCat.{u} := AlgebraicTopology.singularIntegralCoefficients
  let Γ : Type u := End (SSet.FundamentalGroupoid.mk x)
  let M := nativeCoverDeckFunctor X x ⋙ SSet.homologyFunctor R 1
  let H := CategoryTheory.CategoryHomology.homologyWithCoefficientsFunctor
    (C := SingleObj Γ) (A := AddCommGrpCat.{u}) p
  let : H.PreservesZeroMorphisms :=
    { map_zero := by
        intro A B
        simpa only [zero_smul] using H.map_smul (0 : ℤ) (0 : A ⟶ B) }
  have hM : IsZero M := Functor.isZero M (fun _ => nativeCoverHomologyOne_isZero X x)
  have hH : IsZero (H.obj M) := H.map_isZero hM
  exact hH.of_iso (SSet.bkSecondPageCoefficientHomologyIso R (nativeCoverDeckFunctor X x) p 1)

/-- For a connected Kan original base, original integral H2 vanishing
forces its original endomorphism group's genuine native integral H2 to vanish. -/
theorem nativeCoverGroupHomologyTwo_isZero (X : SSet.{u}) [KanComplex X] [X.IsConnected]
    (x : X _⦋0⦌)
    (hX : IsZero (X.homology
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) 2)) :
    IsZero (groupHomology (Rep.trivial (ULift.{u} ℤ)
      (End (SSet.FundamentalGroupoid.mk x)) (ULift.{u} ℤ)) 2) := by
  let R : AddCommGrpCat.{u} := AlgebraicTopology.singularIntegralCoefficients
  let K := SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (nativeCoverDeckFunctor X x)
  have hTotal := hX.of_iso (nativeCoverTotalHomologyIsoAddCommGrp R X x 2)
  have h01 := nativeCoverSecondPageOne_isZero X x 0
  have h20 := HomologicalComplex₂.isZero_horizontalSecondPage_two_zero_of_totalH2_zero
    K hTotal h01
  let e := nativeCoverSecondPageZeroRowGroupHomologyIso X x 2
  have hG := h20.of_iso e.symm
  let F : ModuleCat.{u} (ULift.{u} ℤ) ⥤ AddCommGrpCat.{u} :=
    forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u}
  let A := groupHomology (Rep.trivial (ULift.{u} ℤ)
    (End (SSet.FundamentalGroupoid.mk x)) (ULift.{u} ℤ)) 2
  apply (IsZero.iff_id_eq_zero A).mpr
  exact F.zero_of_map_zero (𝟙 A)
    ((F.map_id A).trans ((IsZero.iff_id_eq_zero (F.obj A)).mp hG))

end SSet.KanComplex

end
