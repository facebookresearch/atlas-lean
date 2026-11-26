/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CompletedFilteredPrismaticTensors
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-!
# Completed filtered inverse of the prismatic tensor tower

The completed evaluation map, from the resolved Milnor limit of the finite
tensor products to the resolved Milnor limit of the weight-zero tower, is an
isomorphism in the derived category and commutes with the projections to every
finite level; the comparison maps from the completed twists commute with the
projections and the finite completion maps.

Source: BMS19 arXiv:1802.03261v2, Theorem1.12(3), footnote3,
Sections5.1/7.3/7.4; Bhatt–Scholze arXiv:1905.08229v4,
Sections12–15.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CompletedFilteredPrismaticTensors

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry AbsolutePrismaticBasis PrismaticFilteredTwists
open SyntomicNearbyComparisons CompletedFilteredPrismaticTensors
open MathlibExt (FunctorialKInjective)

attribute [local instance] HasDerivedCategory.standard

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex in
private theorem coneMap_fst {C : Type*} [Category* C] [Abelian C]
    {K L K' L' : CochainComplex C ℤ} (φ : K ⟶ L) (φ' : K' ⟶ L')
    (H : ∀ (j : ℤ), ∃ i, (ComplexShape.up ℤ).Rel i j)
    (α : Arrow.mk φ ⟶ Arrow.mk φ') :
    (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).map
        (HomologicalComplex.homotopyCofiber.mapArrowHom φ φ' H α) ≫
      CochainComplex.mappingCocone.fst φ' =
    CochainComplex.mappingCocone.fst φ ≫ α.left := by
  have hrel : ∀ (p : ℤ), (ComplexShape.up ℤ).Rel (p + -1) p :=
    fun p => ComplexShape.up_mk _ _ (by omega)
  have hfst : ∀ {F G : CochainComplex C ℤ} (ψ : F ⟶ G) (p : ℤ),
      (mappingCocone.fst ψ).f p =
      homotopyCofiber.fstX ψ (p + -1) p (hrel p) := by
    intro F G ψ p
    have hsign : (-1 * 0 + -1 * (-1 - 1) / 2 : ℤ) = 1 := by norm_num
    have hIso : ∀ (K : CochainComplex C ℤ) (p : ℤ) (hh : p + -1 = p + -1),
        (K.shiftFunctorObjXIso (-1) p (p + -1) hh).hom = 𝟙 _ := fun _ _ _ => rfl
    have hsmul : ∀ {X Y : C} (f : X ⟶ Y), ((-1 : ℤˣ) • f) = -f := fun _ => by simp
    simp only [mappingCocone.fst, HomologicalComplex.neg_f_apply,
      HomComplex.Cocycle.homOf_f]
    change -(((mappingCone.fst ψ).1.leftShift (-1) 0 (add_neg_cancel 1)).v p p
      (add_zero p)) = _
    rw [HomComplex.Cochain.leftShift_v _ (-1) 0 _ p p _ (p + -1) (by omega),
      hsign, Int.negOnePow_one, hIso, hsmul, neg_neg, Category.id_comp]
    rfl
  have hinr : ∀ (p : ℤ), (homotopyCofiber.inr φ').f (p + -1) ≫
      homotopyCofiber.fstX φ' (p + -1) p (hrel p) = 0 := by
    intro p
    have h := mappingCone.inr_f_fst_v φ' (p + -1) p (by omega)
    have hfstX : (mappingCone.fst φ').1.v (p + -1) p (by omega) =
        homotopyCofiber.fstX φ' (p + -1) p (hrel p) := rfl
    rwa [hfstX] at h
  have hAC : ∀ (p : ℤ), homotopyCofiber.fstX φ (p + -1) p (hrel p) ≫
        (α.left.f p ≫ (homotopyCofiber.inlX φ' p (p + -1) (hrel p) ≫
        homotopyCofiber.fstX φ' (p + -1) p (hrel p))) =
      homotopyCofiber.fstX φ (p + -1) p (hrel p) ≫ α.left.f p := by
    intro p
    simp only [homotopyCofiber.inlX_fstX]
    change homotopyCofiber.fstX φ (p + -1) p (hrel p) ≫
      (α.left.f p ≫ 𝟙 (((Arrow.mk φ').left).X p)) = _
    rw [Category.comp_id]
  have hBC : ∀ (p : ℤ), homotopyCofiber.sndX φ (p + -1) ≫
        ((α.right ≫ homotopyCofiber.inr φ').f (p + -1) ≫
        homotopyCofiber.fstX φ' (p + -1) p (hrel p)) = 0 := by
    intro p
    simp only [HomologicalComplex.comp_f, Category.assoc, hinr p, Limits.comp_zero]
  ext p
  change ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).map
      (homotopyCofiber.mapArrowHom φ φ' H α)).f p ≫ (mappingCocone.fst φ').f p =
    (mappingCocone.fst φ).f p ≫ α.left.f p
  rw [CochainComplex.shiftFunctor_map_f', hfst φ p, hfst φ' p]
  simp only [homotopyCofiber.mapArrowHom]
  rw [homotopyCofiber.desc_f _ _ _ _ p (hrel p)]
  simp only [Homotopy.trans_hom, Homotopy.compLeft_hom, Homotopy.ofEq_hom,
    Pi.zero_apply]
  rw [homotopyCofiber.inrCompHomotopy_hom _ _ _ _ (hrel p)]
  simp only [zero_add, add_zero]
  rw [Preadditive.add_comp]
  simp only [Category.assoc]
  rw [hAC p, hBC p, add_zero]
  rfl

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex in
private instance productMap_isIso {M : Type 2} [Category.{1} M] [Abelian M]
    [HasLimitsOfShape (Discrete ℕ) M] {X Y : Tower M} (f : Tower.Hom X Y)
    [∀ n, IsIso (f.map n)] : IsIso (Tower.productMap f) := by
  have heq : Tower.productMap f = Limits.Pi.map (f.map) := by
    apply Pi.hom_ext
    intro n
    simp only [Pi.map_π, Tower.productMap, Pi.lift_comp_π]
  rw [heq]
  exact inferInstance

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex in
private theorem towerMap_projection {M : Type 2} [Category.{1} M] [Abelian M]
    [HasLimitsOfShape (Discrete ℕ) M] {X Y : Tower M} (f : Tower.Hom X Y)
    (n : ℕ) : Tower.map f ≫ Y.projection n = X.projection n ≫ f.map n := by
  have H0 : ∀ (j : ℤ), ∃ i, (ComplexShape.up ℤ).Rel i j :=
    fun j : ℤ ↦ ⟨j - 1, by simp⟩
  have hπ : Tower.productMap f ≫ Pi.π _ n = Pi.π _ n ≫ f.map n := by
    simp only [Tower.productMap, Pi.lift_comp_π]
  have h := coneMap_fst X.difference Y.difference H0
    (Arrow.homMk (Tower.productMap f) (Tower.productMap f) (Tower.square f))
  simp only [Arrow.homMk_left] at h
  have s1 : Tower.map f ≫ Y.projection n =
      (CategoryTheory.shiftFunctor (CochainComplex M ℤ) (-1 : ℤ)).map
          (HomologicalComplex.homotopyCofiber.mapArrowHom X.difference Y.difference H0
            (Arrow.homMk (Tower.productMap f) (Tower.productMap f) (Tower.square f))) ≫
          (CochainComplex.mappingCocone.fst Y.difference ≫ Pi.π _ n) := rfl
  have s2 : (CategoryTheory.shiftFunctor (CochainComplex M ℤ) (-1 : ℤ)).map
          (HomologicalComplex.homotopyCofiber.mapArrowHom X.difference Y.difference H0
            (Arrow.homMk (Tower.productMap f) (Tower.productMap f) (Tower.square f))) ≫
          (CochainComplex.mappingCocone.fst Y.difference ≫ Pi.π _ n) =
      ((CategoryTheory.shiftFunctor (CochainComplex M ℤ) (-1 : ℤ)).map
          (HomologicalComplex.homotopyCofiber.mapArrowHom X.difference Y.difference H0
            (Arrow.homMk (Tower.productMap f) (Tower.productMap f) (Tower.square f))) ≫
          CochainComplex.mappingCocone.fst Y.difference) ≫ Pi.π _ n :=
    (Category.assoc _ _ _).symm
  have s3 : ((CategoryTheory.shiftFunctor (CochainComplex M ℤ) (-1 : ℤ)).map
          (HomologicalComplex.homotopyCofiber.mapArrowHom X.difference Y.difference H0
            (Arrow.homMk (Tower.productMap f) (Tower.productMap f) (Tower.square f))) ≫
          CochainComplex.mappingCocone.fst Y.difference) ≫ Pi.π _ n =
      (CochainComplex.mappingCocone.fst X.difference ≫ Tower.productMap f) ≫ Pi.π _ n :=
    congrArg (· ≫ Pi.π _ n) h
  have s4 : (CochainComplex.mappingCocone.fst X.difference ≫ Tower.productMap f) ≫ Pi.π _ n =
      CochainComplex.mappingCocone.fst X.difference ≫ (Tower.productMap f ≫ Pi.π _ n) :=
    Category.assoc _ _ _
  have s5 : CochainComplex.mappingCocone.fst X.difference ≫ (Tower.productMap f ≫ Pi.π _ n) =
      CochainComplex.mappingCocone.fst X.difference ≫ (Pi.π _ n ≫ f.map n) :=
    congrArg _ hπ
  have s6 : CochainComplex.mappingCocone.fst X.difference ≫ (Pi.π _ n ≫ f.map n) =
      (CochainComplex.mappingCocone.fst X.difference ≫ Pi.π _ n) ≫ f.map n :=
    (Category.assoc _ _ _).symm
  have s7 : (CochainComplex.mappingCocone.fst X.difference ≫ Pi.π _ n) ≫ f.map n =
      X.projection n ≫ f.map n := rfl
  exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans s7)))))

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex in
private theorem towerMap_isIso {M : Type 2} [Category.{1} M] [Abelian M]
    [HasLimitsOfShape (Discrete ℕ) M] {X Y : Tower M} (f : Tower.Hom X Y)
    [∀ n, IsIso (f.map n)] : IsIso (DerivedCategory.Q.map (Tower.map f)) := by
  have H0 : ∀ (j : ℤ), ∃ i, (ComplexShape.up ℤ).Rel i j :=
    fun j : ℤ ↦ ⟨j - 1, by simp⟩
  have harrow : Arrow.homMk (Tower.productMap f) (Tower.productMap f) (Tower.square f) =
      (Arrow.isoMk' X.difference Y.difference (asIso (Tower.productMap f))
        (asIso (Tower.productMap f)) (Tower.square f)).hom := by
    apply Arrow.hom_ext
    · rfl
    · rfl
  have hmap : Tower.map f = (CategoryTheory.shiftFunctor (CochainComplex M ℤ) (-1 : ℤ)).map
      (HomologicalComplex.homotopyCofiber.mapArrowHom X.difference Y.difference H0
        (Arrow.homMk (Tower.productMap f) (Tower.productMap f) (Tower.square f))) := rfl
  have hfin : HomologicalComplex.homotopyCofiber.mapArrowHom X.difference Y.difference H0
        (Arrow.isoMk' X.difference Y.difference (asIso (Tower.productMap f))
          (asIso (Tower.productMap f)) (Tower.square f)).hom =
      (HomologicalComplex.homotopyCofiber.mapArrowIso X.difference Y.difference H0
        (Arrow.isoMk' X.difference Y.difference (asIso (Tower.productMap f))
          (asIso (Tower.productMap f)) (Tower.square f))).hom := rfl
  rw [hmap, harrow, hfin]
  exact Iso.isIso_hom (DerivedCategory.Q.mapIso
    ((CategoryTheory.shiftFunctor (CochainComplex M ℤ) (-1 : ℤ)).mapIso
      (HomologicalComplex.homotopyCofiber.mapArrowIso X.difference Y.difference H0
        (Arrow.isoMk' X.difference Y.difference (asIso (Tower.productMap f))
          (asIso (Tower.productMap f)) (Tower.square f)))))

private instance evaluationLevel_isIso (p : ℕ) [Fact p.Prime]
    (A : QuasiSyntomicPrismSites.Ring p)
    (D : ∀ B : Basis p A, InitialLift p (ring p B))
    (Z : ZeroReduction p A D) (T : TwistTower p A D Z)
    (R : FunctorialKInjective (PrismaticNygaardCohomology.Sheaves p A)) (n : ℕ) :
    IsIso ((Tower.resolveHom R (evaluationTower p A D Z T)).map n) := by
  change IsIso (R.functor.map ((HomologicalComplex.single (Sheaves p A)
    (ComplexShape.up ℤ) 0).map (finiteEvaluation p A D Z T n).hom))
  exact inferInstance

/-- Completed filtered inverse: for a prime $p$, a quasisyntomic ring `A` with chosen initial prisms
`D`, a zero reduction `Z`, a twist tower `T`, a functorial K-injective resolution `R` and commuting
finite completion maps `C`: the completed evaluation map, from the derived limit (the Milnor limit
of the resolved tower) of the finite tensor products $L_n^\vee \otimes L_n$ to the derived limit of
the weight-zero tower, is an isomorphism in the derived category; it commutes with the projections
to every finite level, where it is the resolved finite evaluation; and for every weight $i$, the
comparison map from the completed twist of weight $i$ to the derived limit of its resolved finite
tower commutes with the projections to every level and the finite completion maps. -/
public theorem completedFilteredInverse
    (p : ℕ) [Fact p.Prime] (A : QuasiSyntomicPrismSites.Ring p)
    (D : ∀ B : Basis p A, InitialLift p (ring p B))
    (Z : ZeroReduction p A D) (T : TwistTower p A D Z)
    (R : FunctorialKInjective (PrismaticNygaardCohomology.Sheaves p A))
    (C : CompletionMaps p A D Z T R) :
    CompletedFilteredInverse p A D Z T R C := by
  refine ⟨?_, ?_, ?_⟩
  · exact towerMap_isIso (Tower.resolveHom R (evaluationTower p A D Z T))
  · intro n
    have h := towerMap_projection (Tower.resolveHom R (evaluationTower p A D Z T)) n
    have hQ := congrArg DerivedCategory.Q.map h
    rw [Functor.map_comp, Functor.map_comp] at hQ
    have hFn : (Tower.resolveHom R (evaluationTower p A D Z T)).map n =
        R.functor.map ((evaluationTower p A D Z T).map n) := rfl
    rw [hFn] at hQ
    exact hQ
  · intro i n
    have h := towerMap_projection (C.tower i) n
    have hQ := congrArg DerivedCategory.Q.map h
    rw [Functor.map_comp, Functor.map_comp] at hQ
    have hFn : (C.tower i).map n = finiteCompletionMap p A D Z T R i n := rfl
    rw [hFn] at hQ
    exact hQ

end WantedExt.AlgebraicGeometry.CompletedFilteredPrismaticTensors
