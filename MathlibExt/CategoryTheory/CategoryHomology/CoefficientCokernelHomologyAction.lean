/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.InvertingCoefficientCoinvariants
public import MathlibExt.Algebra.Homology.ShortComplex.CokernelSequence
public import MathlibExt.Algebra.Homology.HomologySequenceFunctor
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.Algebra.Category.Grp.EpiMono

/-!
# The original coefficient-cokernel homology sequence and its actual root actions

The third carrier is the original functor-category cokernel, and its map
is the original quotient projection. Evaluation gives its canonical
pointwise cokernel Iso; this certifies short exactness from the original
monomorphism. The connecting natural transformation is the existing
homology-sequence map of that SAME evaluated short exact family.

Both the quotient and the connecting map extend through the coefficient
fundamental groupoid. Their original components therefore intertwine the
computed root actions, and their original exact sequence remains exact
as a sequence of those underlying root modules. No equivariance,
connecting-map, short-exactness or nilpotence witness is supplied.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryHomology

universe uJ vJ uA

public section

namespace CategoryTheory.CategoryHomology

variable {J : Type uJ} [Category.{vJ} J]
  {A B : J ⥤ ChainComplex AddCommGrpCat.{uA} ℕ} (α : A ⟶ B) [Mono α]

/-- The actual functor-category cokernel sequence, evaluated at each original object. -/
def coefficientCokernelFamily : J ⥤ ShortComplex (ChainComplex AddCommGrpCat.{uA} ℕ) :=
  (ShortComplex.functorEquivalence J (ChainComplex AddCommGrpCat.{uA} ℕ)).functor.obj
    (ShortComplex.cokernelSequence α)

/-- The original first carrier of the stored evaluated family. -/
def coefficientCokernelFamilyX1Iso (i : J) :
    ((coefficientCokernelFamily α).obj i).X₁ ≅ A.obj i := by
  dsimp only [coefficientCokernelFamily]
  exact Iso.refl (A.obj i)

/-- The original functor-category cokernel is the stored third carrier. -/
def coefficientCokernelFamilyX3Iso (i : J) :
    ((coefficientCokernelFamily α).obj i).X₃ ≅ (cokernel α).obj i := by
  dsimp only [coefficientCokernelFamily]
  exact Iso.refl ((cokernel α).obj i)

/-- Its pointwise comparison preserves both original sides and the original quotient map. -/
def coefficientCokernelFamilyIso (i : J) :
    (coefficientCokernelFamily α).obj i ≅ ShortComplex.cokernelSequence (α.app i) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (HomologicalComplex.coefficientCokernelEvaluationIso α i)
    (by
      change 𝟙 _ ≫ α.app i = α.app i ≫ 𝟙 _
      exact (Category.id_comp _).trans (Category.comp_id _).symm)
    (by
      change 𝟙 _ ≫ cokernel.π (α.app i) =
        (cokernel.π α).app i ≫ (HomologicalComplex.coefficientCokernelEvaluationIso α i).hom
      exact (Category.id_comp _).trans
        (HomologicalComplex.coefficientCokernelEvaluationIso_projection α i).symm)

/-- Pointwise short exactness is derived from the SAME original monomorphism. -/
theorem coefficientCokernelFamily_shortExact (i : J) :
    ((coefficientCokernelFamily α).obj i).ShortExact := by
  let a : Arrow (ChainComplex AddCommGrpCat.{uA} ℕ) := Arrow.mk (α.app i)
  let : Mono a.hom := by
    change Mono (α.app i)
    infer_instance
  have h : (ShortComplex.cokernelSequence (α.app i)).ShortExact :=
    ShortComplex.cokernelSequence_shortExact a
  exact ShortComplex.shortExact_of_iso (coefficientCokernelFamilyIso α i).symm h

/-- The actual quotient induces its original homology natural transformation. -/
def coefficientCokernelHomologyProjection (n : ℕ) :
    B ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uA} (ComplexShape.down ℕ) n ⟶
      cokernel α ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{uA} (ComplexShape.down ℕ) n :=
  Functor.whiskerRight (cokernel.π α)
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{uA} (ComplexShape.down ℕ) n)

/-- The original LES boundary, jointly natural in the original coefficient diagram. -/
def coefficientCokernelHomologyBoundary (n : ℕ) :
    cokernel α ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{uA} (ComplexShape.down ℕ) (n + 1) ⟶
      A ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uA} (ComplexShape.down ℕ) n :=
  HomologicalComplex.HomologySequence.δNatTransOfFamily
    (coefficientCokernelFamily α) (coefficientCokernelFamily_shortExact α)
    (n + 1) n (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)

private theorem coefficientCokernelHomologyBoundary_app_computation (n : ℕ) (i : J) :
    (coefficientCokernelHomologyBoundary α n).app i =
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{uA} (ComplexShape.down ℕ) (n + 1)).map
          (coefficientCokernelFamilyX3Iso α i).inv ≫
        (coefficientCokernelFamily_shortExact α i).δ (n + 1) n
          (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl) ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{uA} (ComplexShape.down ℕ) n).map
          (coefficientCokernelFamilyX1Iso α i).hom := by
  let H₃ := HomologicalComplex.homologyFunctor AddCommGrpCat.{uA}
    (ComplexShape.down ℕ) (n + 1)
  let H₁ := HomologicalComplex.homologyFunctor AddCommGrpCat.{uA}
    (ComplexShape.down ℕ) n
  let d : H₃.obj ((cokernel α).obj i) ⟶ H₁.obj (A.obj i) :=
    (coefficientCokernelFamily_shortExact α i).δ (n + 1) n
      (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)
  have hThird : (coefficientCokernelFamilyX3Iso α i).inv =
      (𝟙 ((cokernel α).obj i) : (cokernel α).obj i ⟶ (cokernel α).obj i) := by
    unfold coefficientCokernelFamilyX3Iso
    rfl
  have hFirst : (coefficientCokernelFamilyX1Iso α i).hom =
      (𝟙 (A.obj i) : A.obj i ⟶ A.obj i) := by
    unfold coefficientCokernelFamilyX1Iso
    rfl
  have hMap₃ : H₃.map (coefficientCokernelFamilyX3Iso α i).inv =
      𝟙 (H₃.obj ((cokernel α).obj i)) :=
    (congrArg (fun m : (cokernel α).obj i ⟶ (cokernel α).obj i => H₃.map m)
      hThird).trans (H₃.map_id ((cokernel α).obj i))
  have hMap₁ : H₁.map (coefficientCokernelFamilyX1Iso α i).hom =
      𝟙 (H₁.obj (A.obj i)) :=
    (congrArg (fun m : A.obj i ⟶ A.obj i => H₁.map m)
      hFirst).trans (H₁.map_id (A.obj i))
  have hApp : (coefficientCokernelHomologyBoundary α n).app i = d := by
    change (HomologicalComplex.HomologySequence.δNatTransOfFamily
      (coefficientCokernelFamily α) (coefficientCokernelFamily_shortExact α)
      (n + 1) n (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)).app i = d
    exact HomologicalComplex.HomologySequence.δNatTransOfFamily_app
      (coefficientCokernelFamily α) (coefficientCokernelFamily_shortExact α)
      (n + 1) n (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl) i
  have hTransport :
      H₃.map (coefficientCokernelFamilyX3Iso α i).inv ≫ d ≫
        H₁.map (coefficientCokernelFamilyX1Iso α i).hom = d :=
    (congrArg
      (fun m : H₃.obj ((cokernel α).obj i) ⟶ H₃.obj ((cokernel α).obj i) =>
        m ≫ d ≫ H₁.map (coefficientCokernelFamilyX1Iso α i).hom)
      hMap₃).trans
        ((Category.id_comp _).trans
          ((congrArg (fun m : H₁.obj (A.obj i) ⟶ H₁.obj (A.obj i) => d ≫ m)
            hMap₁).trans (Category.comp_id d)))
  exact hApp.trans hTransport.symm

/-- The actual LES component retains its original first and third carriers
through the two computed identity-carrier isomorphisms. -/
theorem coefficientCokernelHomologyBoundary_app (n : ℕ) (i : J) :
    (coefficientCokernelHomologyBoundary α n).app i =
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{uA} (ComplexShape.down ℕ) (n + 1)).map
          (coefficientCokernelFamilyX3Iso α i).inv ≫
        (coefficientCokernelFamily_shortExact α i).δ (n + 1) n
          (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl) ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{uA} (ComplexShape.down ℕ) n).map
          (coefficientCokernelFamilyX1Iso α i).hom :=
  coefficientCokernelHomologyBoundary_app_computation α n i

omit [Mono α] in
private theorem coefficientCokernelHomologyProjection_app_computation (n : ℕ) (i : J) :
    (coefficientCokernelHomologyProjection α n).app i =
      HomologicalComplex.homologyMap ((cokernel.π α).app i) n := by
  rfl

/-- The SAME original quotient and connecting map form an exact underlying sequence. -/
theorem coefficientCokernelHomology_exact (n : ℕ) (i : J) :
    Function.Exact
      ((coefficientCokernelHomologyProjection α (n + 1)).app i)
      ((coefficientCokernelHomologyBoundary α n).app i) := by
  let S := (coefficientCokernelFamily α).obj i
  let hS := coefficientCokernelFamily_shortExact α i
  let hrel : (ComplexShape.down ℕ).Rel (n + 1) n := rfl
  have h := hS.homology_exact₃ (n + 1) n hrel
  exact (ShortComplex.ab_exact_iff_function_exact _).mp h

/-- The original degree-zero quotient homology map is epi, from the actual short exact sequence. -/
theorem coefficientCokernelHomologyProjection_epi_zero (i : J) :
    Epi ((coefficientCokernelHomologyProjection α 0).app i) := by
  let g := (cokernel.π α).app i
  let : Epi g := (coefficientCokernelFamily_shortExact α i).epi_g
  exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel g 0 (by
    intro j hj
    change j + 1 = 0 at hj
    exact Nat.succ_ne_zero j hj)

section QuotientRoot

variable (n : ℕ)
  [∀ {i j : J} (f : i ⟶ j), IsIso
    ((B ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uA}
      (ComplexShape.down ℕ) n).map f)]
  [∀ {i j : J} (f : i ⟶ j), IsIso
    ((cokernel α ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uA}
      (ComplexShape.down ℕ) n).map f)]

/-- The original quotient is an intertwining map of the computed root representations. -/
def coefficientCokernelProjectionRootMap (i : J) :
    Representation.IntertwiningMap
      (invertingCoefficientRootAction
        (B ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uA}
          (ComplexShape.down ℕ) n) i)
      (invertingCoefficientRootAction
        (cokernel α ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uA}
          (ComplexShape.down ℕ) n) i) :=
  invertingCoefficientRootMap
    (B ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uA} (ComplexShape.down ℕ) n)
    (coefficientCokernelHomologyProjection α n) i

omit [Mono α] in
private theorem coefficientCokernelProjectionRootMap_apply_computation (i : J)
    (v : (B.obj i).homology n) :
    coefficientCokernelProjectionRootMap α n i v =
      HomologicalComplex.homologyMap ((cokernel.π α).app i) n v := by
  let M := B ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uA} (ComplexShape.down ℕ) n
  let q := coefficientCokernelHomologyProjection α n
  have hRoot : coefficientCokernelProjectionRootMap α n i v = (q.app i).hom v :=
    invertingCoefficientRootMap_apply M q i v
  have hProjection : q.app i = HomologicalComplex.homologyMap ((cokernel.π α).app i) n :=
    coefficientCokernelHomologyProjection_app_computation α n i
  exact hRoot.trans (congrArg
    (fun m : (B.obj i).homology n ⟶ ((cokernel α).obj i).homology n => m.hom v)
    hProjection)

omit [Mono α] in
/-- The root quotient map retains the actual quotient homology value. -/
theorem coefficientCokernelProjectionRootMap_apply (i : J) (v : (B.obj i).homology n) :
    coefficientCokernelProjectionRootMap α n i v =
      HomologicalComplex.homologyMap ((cokernel.π α).app i) n v :=
  coefficientCokernelProjectionRootMap_apply_computation α n i v

end QuotientRoot

section BoundaryRoot

variable (n : ℕ)
  [∀ {i j : J} (f : i ⟶ j), IsIso
    ((cokernel α ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uA}
      (ComplexShape.down ℕ) (n + 1)).map f)]
  [∀ {i j : J} (f : i ⟶ j), IsIso
    ((A ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uA}
      (ComplexShape.down ℕ) n).map f)]

/-- The original LES connecting map is an intertwining map of those SAME representations. -/
def coefficientCokernelBoundaryRootMap (i : J) :
    Representation.IntertwiningMap
      (invertingCoefficientRootAction
        (cokernel α ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uA}
          (ComplexShape.down ℕ) (n + 1)) i)
      (invertingCoefficientRootAction
        (A ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uA}
          (ComplexShape.down ℕ) n) i) :=
  invertingCoefficientRootMap
    (cokernel α ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uA}
      (ComplexShape.down ℕ) (n + 1))
    (coefficientCokernelHomologyBoundary α n) i

private theorem coefficientCokernelBoundaryRootMap_apply_computation (i : J)
    (v : ((cokernel α).obj i).homology (n + 1)) :
    coefficientCokernelBoundaryRootMap α n i v =
      (coefficientCokernelHomologyBoundary α n).app i v := by
  let M := cokernel α ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{uA} (ComplexShape.down ℕ) (n + 1)
  let d := coefficientCokernelHomologyBoundary α n
  exact invertingCoefficientRootMap_apply M d i v

/-- The root connecting map retains the original LES natural component;
the preceding whole-map equation records its computed carrier transport. -/
theorem coefficientCokernelBoundaryRootMap_apply (i : J)
    (v : ((cokernel α).obj i).homology (n + 1)) :
    coefficientCokernelBoundaryRootMap α n i v =
      (coefficientCokernelHomologyBoundary α n).app i v :=
  coefficientCokernelBoundaryRootMap_apply_computation α n i v

end BoundaryRoot

section RootSequence

variable (n : ℕ)
  [∀ {i j : J} (f : i ⟶ j), IsIso
    ((B ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uA}
      (ComplexShape.down ℕ) (n + 1)).map f)]
  [∀ {i j : J} (f : i ⟶ j), IsIso
    ((cokernel α ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uA}
      (ComplexShape.down ℕ) (n + 1)).map f)]
  [∀ {i j : J} (f : i ⟶ j), IsIso
    ((A ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uA}
      (ComplexShape.down ℕ) n).map f)]

/-- The original root sequence is exact; equivariance is part of its computed maps. -/
theorem coefficientCokernelRootMaps_exact (i : J) :
    Function.Exact (coefficientCokernelProjectionRootMap α (n + 1) i)
      (coefficientCokernelBoundaryRootMap α n i) := by
  have hProjection : (fun v => coefficientCokernelProjectionRootMap α (n + 1) i v) =
      (fun v => (coefficientCokernelHomologyProjection α (n + 1)).app i v) := by
    funext v
    exact (coefficientCokernelProjectionRootMap_apply α (n + 1) i v).trans
      (congrArg (fun m : (B.obj i).homology (n + 1) ⟶
          ((cokernel α).obj i).homology (n + 1) => m.hom v)
        (coefficientCokernelHomologyProjection_app_computation α (n + 1) i).symm)
  have hBoundary : (fun v => coefficientCokernelBoundaryRootMap α n i v) =
      (fun v => (coefficientCokernelHomologyBoundary α n).app i v) := by
    funext v
    exact coefficientCokernelBoundaryRootMap_apply α n i v
  change Function.Exact (fun v => coefficientCokernelProjectionRootMap α (n + 1) i v)
    (fun v => coefficientCokernelBoundaryRootMap α n i v)
  rw [hProjection, hBoundary]
  exact coefficientCokernelHomology_exact α n i

end RootSequence

section RootZero

variable
  [∀ {i j : J} (f : i ⟶ j), IsIso
    ((B ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uA}
      (ComplexShape.down ℕ) 0).map f)]
  [∀ {i j : J} (f : i ⟶ j), IsIso
    ((cokernel α ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uA}
      (ComplexShape.down ℕ) 0).map f)]

/-- The initial root quotient is actually surjective, including the original degree-zero edge. -/
theorem coefficientCokernelProjectionRootMap_zero_surjective (i : J) :
    Function.Surjective (coefficientCokernelProjectionRootMap α 0 i) := by
  let m := (coefficientCokernelHomologyProjection α 0).app i
  let : Epi m := coefficientCokernelHomologyProjection_epi_zero α i
  have hm : Function.Surjective m := (AddCommGrpCat.epi_iff_surjective m).mp inferInstance
  have hProjection : (fun v => coefficientCokernelProjectionRootMap α 0 i v) =
      (fun v => m v) := by
    funext v
    exact (coefficientCokernelProjectionRootMap_apply α 0 i v).trans
      (congrArg (fun q : (B.obj i).homology 0 ⟶ ((cokernel α).obj i).homology 0 => q.hom v)
        (coefficientCokernelHomologyProjection_app_computation α 0 i).symm)
  change Function.Surjective (fun v => coefficientCokernelProjectionRootMap α 0 i v)
  rw [hProjection]
  exact hm

end RootZero

end CategoryTheory.CategoryHomology
