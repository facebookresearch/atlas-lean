/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.Algebra.Homology.SingleQuasiIso
public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.DiskPair
public import MathlibExt.AlgebraicTopology.SingularHomology.RelativeReducedCoefficient
public import MathlibExt.AlgebraicTopology.SingularHomology.Sphere.Homology
public import MathlibExt.AlgebraicTopology.SingularHomology.Sphere.Transport

/-!
# Relative homology of classical disk pairs

The classical `n`-disk pair `(Dⁿ, Sⁿ⁻¹)` satisfies `Hₙ ≅ R` and `Hₖ = 0` for
`k ≠ n`.  The diagonal result is generic in an abelian target where singular
homology has excision; in positive dimension it proceeds via the
contractible-ambient reduced comparison, boundary homeomorphism, and the
accepted reduced sphere calculation.  The additive off-diagonal and
projective single-complex APIs are retained below.
-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex

namespace Topology.CWComplex

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [AB4OfSize.{w} C]

noncomputable def classicalCellBoundarySphereHomologyIntNatIso
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] [AB4OfSize.{w} C]
    (hExcisive : ∀ R : C,
      (AlgebraicTopology.singularHomologyIntData C R).IsExcisive)
    (m : ℕ) (n : ℤ) :
    AlgebraicTopology.singularHomologyIntCoefficientFunctor (C := C) n ⋙
        (evaluation TopCat.{w} C).obj
          (classicalCellDiskPair.{w} (m + 1)).snd ≅
      AlgebraicTopology.singularHomologyIntCoefficientFunctor (C := C) n ⋙
        (evaluation TopCat.{w} C).obj (TopCat.sphere.{w} m) :=
  NatIso.ofComponents
    (fun R =>
      (TopPair.GeneralizedHomologyTheory.classicalCellBoundarySphereNatIso
        (C := C) m n).app
          (TopPair.OrdinaryHomologyTheory.forgetDimension.obj
            ((AlgebraicTopology.singularHomologyIntTheoryFunctor
              (hExcisive := hExcisive)).obj R)))
    (fun {_ _} a =>
      (TopPair.GeneralizedHomologyTheory.classicalCellBoundarySphereNatIso
        (C := C) m n).hom.naturality
          ((AlgebraicTopology.singularHomologyIntTheoryFunctor
            (hExcisive := hExcisive) ⋙
              TopPair.OrdinaryHomologyTheory.forgetDimension).map a))

@[simp]
theorem classicalCellBoundarySphereHomologyIntNatIso_app
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] [AB4OfSize.{w} C]
    (hExcisive : ∀ R : C,
      (AlgebraicTopology.singularHomologyIntData C R).IsExcisive)
    (m : ℕ) (n : ℤ) (R : C) :
    (classicalCellBoundarySphereHomologyIntNatIso hExcisive m n).app R =
      (singularHomologyIntTheory (C := C) R).obj.closedBallPairUnitSphereIso
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm n :=
  rfl

/-- The relative-to-boundary-sphere comparison for classical disk pairs is
natural in singular-homology coefficients. -/
noncomputable def classicalCellDiskPairBoundaryHomologyIntNatIso
    (hExcisive : ∀ R : C,
      (AlgebraicTopology.singularHomologyIntData C R).IsExcisive)
    (m : ℕ) (n : ℤ) (hn : n ≠ 0) (hnPrev : n - 1 ≠ 0) :
    AlgebraicTopology.relativeSingularHomologyIntCoefficientFunctor
          (C := C) n ⋙
        (evaluation TopPair.{w} C).obj
          (classicalCellDiskPair.{w} (m + 1)) ≅
      AlgebraicTopology.singularHomologyIntCoefficientFunctor
          (C := C) (n - 1) ⋙
        (evaluation TopCat.{w} C).obj (TopCat.sphere.{w} m) := by
  let T := AlgebraicTopology.singularHomologyIntTheoryFunctor
    (hExcisive := hExcisive)
  let Hₚ := TopPair.OrdinaryHomologyTheory.hₚFunctor (C := C) n
  let H := TopPair.OrdinaryHomologyTheory.hFunctor (C := C) (n - 1)
  let evP := (evaluation TopPair.{w} C).obj
    (classicalCellDiskPair.{w} (m + 1))
  let evS := (evaluation TopCat.{w} C).obj (TopCat.sphere.{w} m)
  exact
    (Functor.isoWhiskerRight
      (AlgebraicTopology.singularHomologyIntTheoryFunctorHₚIso
        (C := C) hExcisive n) evP).symm ≪≫
      Functor.associator T Hₚ evP ≪≫
      Functor.isoWhiskerLeft T
        (TopPair.OrdinaryHomologyTheory.classicalCellDiskPairBoundaryNatIso
          (C := C) m n hn hnPrev) ≪≫
      (Functor.associator T H evS).symm ≪≫
      Functor.isoWhiskerRight
        (AlgebraicTopology.singularHomologyIntTheoryFunctorHIso
          (C := C) hExcisive (n - 1)) evS

theorem classicalCellDiskPairBoundaryHomologyIntNatIso_hom_naturality
    (hExcisive : ∀ R : C,
      (AlgebraicTopology.singularHomologyIntData C R).IsExcisive)
    (m : ℕ) (n : ℤ) (hn : n ≠ 0) (hnPrev : n - 1 ≠ 0)
    {R S : C} (a : R ⟶ S) :
    (AlgebraicTopology.relativeSingularHomologyIntCoefficientFunctor
          (C := C) n ⋙
        (evaluation TopPair.{w} C).obj
          (classicalCellDiskPair.{w} (m + 1))).map a ≫
        (classicalCellDiskPairBoundaryHomologyIntNatIso
          hExcisive m n hn hnPrev).hom.app S =
      (classicalCellDiskPairBoundaryHomologyIntNatIso
        hExcisive m n hn hnPrev).hom.app R ≫
        (AlgebraicTopology.singularHomologyIntCoefficientFunctor
            (C := C) (n - 1) ⋙
          (evaluation TopCat.{w} C).obj (TopCat.sphere.{w} m)).map a :=
  (classicalCellDiskPairBoundaryHomologyIntNatIso
    hExcisive m n hn hnPrev).hom.naturality a

/-- Zero-dimensional disk-pair relative homology `R ≅ H₀(D⁰, ∂D⁰; R)`. -/
noncomputable def classicalCellDiskPairZeroRelativeHomologyIso
    (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] (R : C) :
    R ≅ (AlgebraicTopology.relativeSingularHomologyFunctor.{w, v, u} C R 0).obj
      (classicalCellDiskPair.{w} 0) :=
  (asIso ((classicalCellDiskPair.{w} 0).fst.singularHomology₀ε (C := C) R)).symm
    ≪≫ AlgebraicTopology.singularHomologyEmptyPairObjIso.{w, v, u} C R
      (classicalCellDiskPair.{w} 0) 0

/-- Vanishing of `Hₖ(D⁰, ∂D⁰; R)` for `k ≠ 0`. -/
theorem isZero_relativeSingularHomology_classicalCellDiskPair_zero_of_ne_zero
    (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    (R : C) (k : ℕ) (hk : k ≠ 0) :
    IsZero ((AlgebraicTopology.relativeSingularHomologyFunctor C R k).obj
      (classicalCellDiskPair 0)) := by
  have iso :=
    AlgebraicTopology.singularHomologyEmptyPairObjIso C R
      (classicalCellDiskPair 0) k
  have h :
      IsZero (((AlgebraicTopology.singularHomologyFunctor C k).obj R).obj
        (classicalCellDiskPair 0).fst) :=
    AlgebraicTopology.isZero_singularHomology_of_contractible C R k hk _
  exact h.of_iso iso.symm

/-- Diagonal relative homology `R ≅ Hₙ(Dⁿ, ∂Dⁿ; R)` in an abelian target where
singular homology satisfies excision. -/
noncomputable def classicalCellDiskPairRelativeHomologyIso
    [HasCoproducts.{0} C] (R : C)
    [hExcisive : (AlgebraicTopology.singularHomologyIntData.{w, v, u} C R :
      TopPair.HomologyTheoryData.{w} C).IsExcisive] : (n : ℕ) →
    R ≅ (AlgebraicTopology.relativeSingularHomologyFunctor.{w, v, u} C R n).obj
      (classicalCellDiskPair.{w} n)
  | 0 =>
    classicalCellDiskPairZeroRelativeHomologyIso.{w, v, u} C R
  | n + 1 =>
    (AlgebraicTopology.reducedSphereHomologyIso.{w, v, u} (C := C) R
      (hExcisive := hExcisive) n).symm
      ≪≫ AlgebraicTopology.homeoReducedHomologyIso.{w, v, u} R n
        (classicalCellBoundarySphereHomeomorph.{w} n).symm
      ≪≫ (AlgebraicTopology.relativeSingularHomologyReducedIsoOfContractibleAmbient.{w, v, u}
        C R (classicalCellDiskPair.{w} (n + 1)) n).symm

@[simp]
theorem classicalCellDiskPairRelativeHomologyIso_zero
    [HasCoproducts.{0} C] (R : C)
    [hExcisive : (AlgebraicTopology.singularHomologyIntData.{w, v, u} C R :
      TopPair.HomologyTheoryData.{w} C).IsExcisive] :
    classicalCellDiskPairRelativeHomologyIso.{w, v, u} (C := C) R
        (hExcisive := hExcisive) 0 =
      classicalCellDiskPairZeroRelativeHomologyIso.{w, v, u} C R :=
  rfl

/-- Recursive successor formula for the generalized classical disk-pair
coordinate. -/
theorem classicalCellDiskPairRelativeHomologyIso_succ_of_excisive
    [HasCoproducts.{0} C] (R : C)
    [hExcisive : (AlgebraicTopology.singularHomologyIntData.{w, v, u} C R :
      TopPair.HomologyTheoryData.{w} C).IsExcisive] (n : ℕ) :
    classicalCellDiskPairRelativeHomologyIso.{w, v, u} (C := C) R
        (hExcisive := hExcisive) (n + 1) =
      (AlgebraicTopology.reducedSphereHomologyIso.{w, v, u} (C := C) R
        (hExcisive := hExcisive) n).symm ≪≫
        AlgebraicTopology.homeoReducedHomologyIso.{w, v, u} R n
          (classicalCellBoundarySphereHomeomorph.{w} n).symm ≪≫
        (AlgebraicTopology.relativeSingularHomologyReducedIsoOfContractibleAmbient.{w, v, u}
          C R (classicalCellDiskPair.{w} (n + 1)) n).symm :=
  rfl

@[simp]
theorem classicalCellDiskPairRelativeHomologyIso_succ
    (R : AddCommGrpCat.{0}) (n : ℕ) :
    classicalCellDiskPairRelativeHomologyIso R (n + 1) =
      (AlgebraicTopology.reducedSphereHomologyIso R n).symm
        ≪≫ AlgebraicTopology.homeoReducedHomologyIso R n
          (classicalCellBoundarySphereHomeomorph n).symm
        ≪≫ (AlgebraicTopology.relativeSingularHomologyReducedIsoOfContractibleAmbient
          AddCommGrpCat.{0} R (classicalCellDiskPair (n + 1)) n).symm :=
  rfl

/-- Off-diagonal vanishing `Hₖ(Dⁿ, ∂Dⁿ; R) = 0` for `k ≠ n`. -/
theorem isZero_relativeSingularHomology_classicalCellDiskPair_of_ne
    (R : AddCommGrpCat.{0}) (n k : ℕ) (h : k ≠ n) :
    IsZero ((AlgebraicTopology.relativeSingularHomologyFunctor AddCommGrpCat.{0} R k).obj
      (classicalCellDiskPair n)) := by
  match n, k with
  | 0, k =>
    have hk : k ≠ 0 := h
    exact isZero_relativeSingularHomology_classicalCellDiskPair_zero_of_ne_zero
      AddCommGrpCat.{0} R k hk
  | n + 1, 0 =>
    exact AlgebraicTopology.isZero_relativeSingularHomologyZero_of_pathConnectedSpace
      AddCommGrpCat.{0} R (classicalCellDiskPair (n + 1)) inferInstance
  | n + 1, k + 1 =>
    have hk : k ≠ n := fun heq => h (congrArg Nat.succ heq)
    have iso₁ :=
      AlgebraicTopology.relativeSingularHomologyReducedIsoOfContractibleAmbient
        AddCommGrpCat.{0} R (classicalCellDiskPair (n + 1)) k
    have iso₂ :=
      AlgebraicTopology.homeoReducedHomologyIso R k
        (classicalCellBoundarySphereHomeomorph n)
    have hRed : IsZero (AlgebraicTopology.reducedSingularHomology AddCommGrpCat.{0} R k
        (TopCat.sphere.{0} n)) :=
      AlgebraicTopology.isZero_reducedSphereHomology_of_ne R n k hk
    have hRedSnd : IsZero (AlgebraicTopology.reducedSingularHomology AddCommGrpCat.{0} R k
        (classicalCellDiskPair (n + 1)).snd) :=
      hRed.of_iso iso₂
    exact hRedSnd.of_iso iso₁

/-- Projective single-complex lift to the relative chain complex. -/
noncomputable def classicalCellDiskPairSingleToRelativeChain
    (R : AddCommGrpCat.{0}) [Projective R] (n : ℕ) :
    ((single AddCommGrpCat.{0} (ComplexShape.down ℕ) n).obj R) ⟶
      (AlgebraicTopology.relativeSingularChainFunctor AddCommGrpCat.{0} R).obj
        (classicalCellDiskPair n) :=
  singleToComplexOfProjective n
    (classicalCellDiskPairRelativeHomologyIso R n)

theorem classicalCellDiskPairSingleToRelativeChain_homologyMap
    (R : AddCommGrpCat.{0}) [Projective R] (n : ℕ) :
    homologyMap
        (classicalCellDiskPairSingleToRelativeChain R n) n =
      (singleObjHomologySelfIso (ComplexShape.down ℕ) n R).hom
        ≫ (classicalCellDiskPairRelativeHomologyIso R n).hom :=
  singleToComplexOfProjective_homologyMap n (classicalCellDiskPairRelativeHomologyIso R n)

noncomputable instance classicalCellDiskPairSingleToRelativeChain_quasiIso
    (R : AddCommGrpCat.{0}) [Projective R] (n : ℕ) :
    QuasiIso (classicalCellDiskPairSingleToRelativeChain R n) :=
  singleToComplexOfProjective_quasiIso n
    (classicalCellDiskPairRelativeHomologyIso R n)
    (fun k hk => isZero_relativeSingularHomology_classicalCellDiskPair_of_ne R n k hk)

theorem classicalCellDiskPairZeroRelativeHomologyIso_hom_naturality_coefficient
    (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    {R S : C} (a : R ⟶ S) :
    a ≫ (classicalCellDiskPairZeroRelativeHomologyIso C S).hom =
      (classicalCellDiskPairZeroRelativeHomologyIso C R).hom ≫
        ((AlgebraicTopology.relativeSingularHomologyCoefficientFunctor
          (C := C) 0).map a).app (classicalCellDiskPair.{w} 0) := by
  let P := classicalCellDiskPair.{w} 0
  let X := P.fst
  let f := ((AlgebraicTopology.singularHomologyFunctor C 0).map a).app X
  let g : (AlgebraicTopology.relativeSingularHomologyFunctor C R 0).obj P ⟶
      (AlgebraicTopology.relativeSingularHomologyFunctor C S 0).obj P :=
    ((AlgebraicTopology.relativeSingularHomologyCoefficientFunctor
      (C := C) 0).map a).app P
  let eR := X.singularHomology₀ε (C := C) R
  let eS := X.singularHomology₀ε (C := C) S
  let iR := AlgebraicTopology.singularHomologyEmptyPairObjIso C R P 0
  let iS := AlgebraicTopology.singularHomologyEmptyPairObjIso C S P 0
  have hε : f ≫ eS = eR ≫ a :=
    TopCat.singularHomology₀ε_naturality_coefficient (C := C) X a
  have hES : eS ≫ (asIso eS).symm.hom = 𝟙 _ := by
    simpa only [Iso.symm_hom, asIso_hom] using (asIso eS).hom_inv_id
  have hER : eR ≫ (asIso eR).symm.hom = 𝟙 _ := by
    simpa only [Iso.symm_hom, asIso_hom] using (asIso eR).hom_inv_id
  have hInv :
      a ≫ (asIso eS).symm.hom = (asIso eR).symm.hom ≫ f := by
    apply (cancel_epi eR).mp
    rw [← Category.assoc, ← hε, Category.assoc, hES, Category.comp_id,
      ← Category.assoc, hER, Category.id_comp]
  have hEmpty : f ≫ iS.hom = iR.hom ≫ g := by
    exact
      AlgebraicTopology.singularHomologyEmptyPairObjIso_hom_naturality_coefficient
        (C := C) a P 0
  change a ≫ ((asIso eS).symm.hom ≫ iS.hom) =
    ((asIso eR).symm.hom ≫ iR.hom) ≫ g
  rw [← Category.assoc, hInv, Category.assoc, hEmpty, ← Category.assoc]

noncomputable def classicalCellDiskPairZeroRelativeHomologyCoefficientNatIso
    (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] :
    (𝟭 C : C ⥤ C) ≅
      AlgebraicTopology.relativeSingularHomologyCoefficientFunctor (C := C) 0 ⋙
        (evaluation TopPair.{w} C).obj (classicalCellDiskPair.{w} 0) :=
  NatIso.ofComponents
    (fun R => classicalCellDiskPairZeroRelativeHomologyIso C R)
    (fun {_ _} a => classicalCellDiskPairZeroRelativeHomologyIso_hom_naturality_coefficient C a)

@[simp] theorem classicalCellDiskPairZeroRelativeHomologyCoefficientNatIso_app
    (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    (R : C) :
    (classicalCellDiskPairZeroRelativeHomologyCoefficientNatIso C).app R =
      classicalCellDiskPairZeroRelativeHomologyIso C R :=
  rfl

theorem isZero_relativeSingularHomologyCoefficientFunctor_classicalCellDiskPair_zero_of_ne_zero
    (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    (k : ℕ) (hk : k ≠ 0) :
    IsZero
      (AlgebraicTopology.relativeSingularHomologyCoefficientFunctor
        (C := C) k ⋙
          (evaluation TopPair.{w} C).obj (classicalCellDiskPair.{w} 0)) :=
  Functor.isZero _ fun R =>
    isZero_relativeSingularHomology_classicalCellDiskPair_zero_of_ne_zero C R k hk

/-- Diagonal disk-pair relative homology, naturally in coefficients. -/
noncomputable def classicalCellDiskPairRelativeHomologyCoefficientNatIso :
    (n : ℕ) →
      (𝟭 AddCommGrpCat.{0} : AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}) ≅
        AlgebraicTopology.relativeSingularHomologyCoefficientFunctor
            (C := AddCommGrpCat.{0}) n ⋙
          (evaluation TopPair.{0} AddCommGrpCat.{0}).obj (classicalCellDiskPair n)
  | 0 => classicalCellDiskPairZeroRelativeHomologyCoefficientNatIso AddCommGrpCat.{0}
  | n + 1 => by
      let h := (classicalCellBoundarySphereHomeomorph n).symm
      let e :
          AlgebraicTopology.reducedSingularHomologyCoefficientFunctor
                AddCommGrpCat.{0} n ⋙
              (evaluation TopCat.{0} AddCommGrpCat.{0}).obj (TopCat.sphere.{0} n) ≅
            AlgebraicTopology.reducedSingularHomologyCoefficientFunctor
                AddCommGrpCat.{0} n ⋙
              (evaluation TopCat.{0} AddCommGrpCat.{0}).obj
                (classicalCellDiskPair (n + 1)).snd :=
        NatIso.ofComponents
          (fun R => AlgebraicTopology.homeoReducedHomologyIso R n h)
          (fun {_ _} a =>
            AlgebraicTopology.homeoReducedHomologyIso_hom_naturality_coefficient a n h)
      exact (AlgebraicTopology.reducedSphereHomologyCoefficientNatIso n).symm ≪≫ e ≪≫
        (AlgebraicTopology.relativeSingularHomologyReducedCoefficientIsoOfContractibleAmbient
          (C := AddCommGrpCat.{0}) (classicalCellDiskPair (n + 1)) n).symm

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem classicalCellDiskPairRelativeHomologyCoefficientNatIso_app
    (R : AddCommGrpCat.{0}) (n : ℕ) :
    (classicalCellDiskPairRelativeHomologyCoefficientNatIso n).app R =
      classicalCellDiskPairRelativeHomologyIso R n := by
  cases n with
  | zero => rfl
  | succ n =>
      change ((AlgebraicTopology.reducedSphereHomologyCoefficientNatIso n).app R).symm ≪≫
          AlgebraicTopology.homeoReducedHomologyIso R n
            (classicalCellBoundarySphereHomeomorph n).symm ≪≫
          (AlgebraicTopology.relativeSingularHomologyReducedIsoOfContractibleAmbient
            AddCommGrpCat.{0} R (classicalCellDiskPair (n + 1)) n).symm = _
      rw [AlgebraicTopology.reducedSphereHomologyCoefficientNatIso_app]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- The diagonal disk-pair relative-homology isomorphism is natural in coefficients. -/
theorem classicalCellDiskPairRelativeHomologyIso_hom_naturality_coefficient
    {R S : AddCommGrpCat.{0}} (a : R ⟶ S) (n : ℕ) :
    a ≫ (classicalCellDiskPairRelativeHomologyIso S n).hom =
      (classicalCellDiskPairRelativeHomologyIso R n).hom ≫
        ((AlgebraicTopology.relativeSingularHomologyCoefficientFunctor
          (C := AddCommGrpCat.{0}) n).map a).app (classicalCellDiskPair n) := by
  have h := (classicalCellDiskPairRelativeHomologyCoefficientNatIso n).hom.naturality a
  have hS : (classicalCellDiskPairRelativeHomologyCoefficientNatIso n).hom.app S =
      (classicalCellDiskPairRelativeHomologyIso S n).hom :=
    congrArg (fun e => e.hom)
      (classicalCellDiskPairRelativeHomologyCoefficientNatIso_app S n)
  have hR : (classicalCellDiskPairRelativeHomologyCoefficientNatIso n).hom.app R =
      (classicalCellDiskPairRelativeHomologyIso R n).hom :=
    congrArg (fun e => e.hom)
      (classicalCellDiskPairRelativeHomologyCoefficientNatIso_app R n)
  rw [hS, hR] at h
  exact h

/-- Disk-pair relative homology vanishes off the diagonal, naturally in coefficients. -/
theorem isZero_relativeSingularHomologyCoefficientFunctor_classicalCellDiskPair_of_ne
    (n k : ℕ) (h : k ≠ n) :
    IsZero
      (AlgebraicTopology.relativeSingularHomologyCoefficientFunctor
          (C := AddCommGrpCat.{0}) k ⋙
        (evaluation TopPair.{0} AddCommGrpCat.{0}).obj (classicalCellDiskPair n)) :=
  Functor.isZero _ fun R =>
    isZero_relativeSingularHomology_classicalCellDiskPair_of_ne R n k h

end Topology.CWComplex
