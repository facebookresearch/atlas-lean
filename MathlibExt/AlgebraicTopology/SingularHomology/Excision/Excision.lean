/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.SingularHomology.Excision.RelativeChains
public import MathlibExt.AlgebraicTopology.SingularHomology.RelativeCoefficientFunctor
public import MathlibExt.AlgebraicTopology.SingularHomology.SmallChains.TwoSetQuasiIso
public import MathlibExt.Algebra.Homology.NatIsoOfQuasiIsoAt

/-!
# Excision

Excision quasi-isomorphism for interiors-cover pairs.

Main definitions:
* `excisionTargetComp_quasiIso`
* `excisionChainMapNatTrans` – the relative excision chain map, natural in coefficients.
* `excisionChainMapNatTrans_quasiIso` – coefficient-natural quasi-isomorphism (proof producer).
* `excisionMap_quasiIso` – relative chain quasi-isomorphism for excision
  (evaluation of the coefficient-natural quasi-isomorphism at `R`).
* `isIso_excisionHomologyMap` – induced isomorphism on relative homology.
* `excisionHomologyIso` – homology isomorphism between excision source and target.
* `excisionHomologyIso_hom` – simp lemma identifying the iso hom with the functor map.
* `excisionMap_quasiIso_of_closure_subset_interior` – closure-form quasi-iso.
* `isIso_excisionHomologyMap_of_closure_subset_interior` – closure-form homology isIso.
* `excisionHomologyIso_of_closure_subset_interior` – closure-form homology iso.
* `excisionHomologyIso_of_closure_subset_interior_hom` – simp lemma for closure-form iso.

-/

@[expose] public section

open CategoryTheory AlgebraicTopology Limits

namespace AlgebraicTopology

universe w v u

section GenericExcision

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

private lemma mapLeftBoth_mono_generic (Y : TopCat.{w}) (A B : Set Y)
    (R : C) :
    Mono (mapLeftBoth (A := A) (B := B) R) := by
  have hComp :
      mapLeftBoth (A := A) (B := B) R ≫
        smallChainInclusion R (smallCoverBoth A B) =
        smallChainInclusion R (smallCoverLeft A) :=
    smallChainMapOfLE_comp_inclusion _ _ _ _
  have : Mono (smallChainInclusion (C := C) R (smallCoverLeft A)) :=
    inferInstance
  have : Mono (mapLeftBoth (A := A) (B := B) R ≫
      smallChainInclusion R (smallCoverBoth A B)) := by
    rw [hComp]
    infer_instance
  exact mono_of_mono (mapLeftBoth (A := A) (B := B) R)
    (smallChainInclusion R (smallCoverBoth A B))

private lemma mono_excisionTargetArrow_generic (Y : TopCat.{w}) (A : Set Y)
    (R : C) :
    Mono (excisionTargetArrow Y A R).hom := by
  have hComp : Mono ((subspaceChainIsoSubcomplex A R).hom ≫
      smallChainInclusion (C := C) R (fun _ : Unit => A)) := by
    infer_instance
  have hEq : (subspaceChainIsoSubcomplex A R).hom ≫
      smallChainInclusion (C := C) R (fun _ : Unit => A) =
      (excisionTargetArrow Y A R).hom :=
    subspaceChainIsoSubcomplex_hom_comp_smallChainInclusion A R
  rw [hEq] at hComp
  exact hComp

private noncomputable def mapLeftBothMonoArrow_generic
    (Y : TopCat.{w}) (A B : Set Y) (R : C) :
    (MorphismProperty.monomorphisms (ChainComplex C ℕ)).Arrow ⊤ ⊤ :=
  MorphismProperty.Arrow.mk (mapLeftBoth (A := A) (B := B) R)
    (mapLeftBoth_mono_generic Y A B R)

private noncomputable def excisionTargetMonoArrow_generic
    (Y : TopCat.{w}) (A : Set Y) (R : C) :
    (MorphismProperty.monomorphisms (ChainComplex C ℕ)).Arrow ⊤ ⊤ :=
  MorphismProperty.Arrow.mk (excisionTargetArrow Y A R).hom
    (mono_excisionTargetArrow_generic Y A R)

private noncomputable def excisionTargetMonoArrowHom_generic
    (Y : TopCat.{w}) (A B : Set Y) (R : C) :
    mapLeftBothMonoArrow_generic Y A B R ⟶
      excisionTargetMonoArrow_generic Y A R :=
  MorphismProperty.Arrow.Hom.mk (excisionTargetArrowHom Y A B R) trivial trivial

private noncomputable def monoArrowCokerFunctor_generic :
    (MorphismProperty.monomorphisms (ChainComplex C ℕ)).Arrow ⊤ ⊤ ⥤
      ChainComplex C ℕ :=
  MorphismProperty.Arrow.forget
      (MorphismProperty.monomorphisms (ChainComplex C ℕ)) ⊤ ⊤ ⋙
    Limits.coker (ChainComplex C ℕ)

private lemma excisionTargetMonoArrowHom_left_eq_generic
    (Y : TopCat.{w}) (A B : Set Y) (R : C) :
    (excisionTargetMonoArrowHom_generic Y A B R).left =
      (subspaceChainIsoSubcomplex A R).symm.hom := rfl

private lemma excisionTargetMonoArrowHom_right_eq_generic
    (Y : TopCat.{w}) (A B : Set Y) (R : C) :
    (excisionTargetMonoArrowHom_generic Y A B R).right =
      smallChainInclusion R (smallCoverBoth A B) := rfl

private lemma excisionTargetMonoArrowHom_left_quasiIso_generic
    (Y : TopCat.{w}) (A B : Set Y) (R : C) :
    QuasiIso (excisionTargetMonoArrowHom_generic Y A B R).left := by
  have hIsIso : IsIso (excisionTargetMonoArrowHom_generic Y A B R).left := by
    rw [excisionTargetMonoArrowHom_left_eq_generic]
    let e := subspaceChainIsoSubcomplex A R
    exact ⟨e.symm.inv, e.symm.hom_inv_id, e.symm.inv_hom_id⟩
  have := hIsIso
  infer_instance

private lemma excisionTargetMonoArrowHom_right_quasiIsoULift_generic
    (G : C) [Projective G] [CategoryTheory.IsFinitelyPresentable.{w} G]
    (hG : CategoryTheory.IsSeparator G)
    (Y : TopCat.{w}) (A B : Set Y) (R : C)
    (h : (Set.univ : Set Y) ⊆ interior A ∪ interior B) :
    QuasiIso (excisionTargetMonoArrowHom_generic Y A B R).right := by
  rw [excisionTargetMonoArrowHom_right_eq_generic]
  exact smallChainInclusion_twoSet_quasiIsoULift R G hG A B h

private lemma monoArrowCokerFunctor_map_quasiIsoULift_generic
    (G : C) [Projective G] [CategoryTheory.IsFinitelyPresentable.{w} G]
    (hG : CategoryTheory.IsSeparator G)
    (Y : TopCat.{w}) (A B : Set Y) (R : C)
    (h : (Set.univ : Set Y) ⊆ interior A ∪ interior B) :
    QuasiIso
      (monoArrowCokerFunctor_generic.map
        (excisionTargetMonoArrowHom_generic Y A B R)) :=
  HomologicalComplex.HomologySequence.quasiIso_coker_map
    (excisionTargetMonoArrowHom_generic Y A B R)
    (excisionTargetMonoArrowHom_left_quasiIso_generic Y A B R)
    (excisionTargetMonoArrowHom_right_quasiIsoULift_generic G hG Y A B R h)

private lemma monoArrowCokerFunctor_map_eq_excisionTargetComp_generic
    (Y : TopCat.{w}) (A B : Set Y) (R : C) :
    monoArrowCokerFunctor_generic.map
        (excisionTargetMonoArrowHom_generic Y A B R) =
      excisionTargetComp Y A B R := rfl

/-- Universe- and coefficient-general proof producer for the target comparison
in relative excision. -/
public theorem excisionTargetComp_quasiIsoULift
    (G : C) [Projective G] [CategoryTheory.IsFinitelyPresentable.{w} G]
    (hG : CategoryTheory.IsSeparator G)
    (Y : TopCat.{w}) (A B : Set Y) (R : C)
    (h : (Set.univ : Set Y) ⊆ interior A ∪ interior B) :
    QuasiIso (excisionTargetComp Y A B R) := by
  rw [← monoArrowCokerFunctor_map_eq_excisionTargetComp_generic]
  exact monoArrowCokerFunctor_map_quasiIsoULift_generic G hG Y A B R h

/-- The relative excision chain map, natural in coefficients. -/
public noncomputable def excisionChainMapNatTrans
    (X : TopCat.{w}) (A B : Set X) :
    (relativeSingularChainComplexFunctor (C := C)).flip.obj
        (excisionSourcePair X A B) ⟶
      (relativeSingularChainComplexFunctor (C := C)).flip.obj
        (excisionTargetPair X A) :=
  (relativeSingularChainComplexFunctor (C := C)).flip.map
    (excisionTopPairHom X A B)

@[simp]
public theorem excisionChainMapNatTrans_app
    (X : TopCat.{w}) (A B : Set X) (R : C) :
    (excisionChainMapNatTrans (C := C) X A B).app R =
      (relativeSingularChainFunctor C R).map
        (excisionTopPairHom X A B) := rfl

/-- Relative excision is a coefficient-natural quasi-isomorphism in any
abelian category with a projective finitely presentable separator. -/
public theorem excisionChainMapNatTrans_quasiIsoULift
    (G : C) [Projective G] [CategoryTheory.IsFinitelyPresentable.{w} G]
    (hG : CategoryTheory.IsSeparator G)
    (X : TopCat.{w}) (A B : Set X)
    (hcover : (Set.univ : Set X) ⊆ interior A ∪ interior B) :
    (HomologicalComplex.quasiIso C (ComplexShape.down ℕ)).functorCategory C
      (excisionChainMapNatTrans (C := C) X A B) := by
  intro R
  change QuasiIso
    ((relativeSingularChainFunctor C R).map (excisionTopPairHom X A B))
  rw [excisionFactorization]
  have : IsIso (excisionSourceRelIso X A B R).hom := inferInstance
  have : IsIso (cokernelComparison A B R) := inferInstance
  have : QuasiIso (excisionTargetComp X A B R) :=
    excisionTargetComp_quasiIsoULift G hG X A B R hcover
  infer_instance

/-- Fixed-coefficient evaluation of universe- and coefficient-general relative
excision. -/
public theorem excisionMap_quasiIsoULift
    (G : C) [Projective G] [CategoryTheory.IsFinitelyPresentable.{w} G]
    (hG : CategoryTheory.IsSeparator G)
    (Y : TopCat.{w}) (A B : Set Y) (R : C)
    (h : (Set.univ : Set Y) ⊆ interior A ∪ interior B) :
    QuasiIso
      ((relativeSingularChainFunctor C R).map
        (excisionTopPairHom Y A B)) := by
  exact excisionChainMapNatTrans_quasiIsoULift G hG Y A B h R

/-- Relative excision on homology, natural in coefficients, in the generic
coefficient category. -/
public noncomputable def excisionHomologyCoefficientNatIsoULift
    (G : C) [Projective G] [CategoryTheory.IsFinitelyPresentable.{w} G]
    (hG : CategoryTheory.IsSeparator G)
    (X : TopCat.{w}) (A B : Set X)
    (hcover : (Set.univ : Set X) ⊆ interior A ∪ interior B) (n : ℕ) :
    (relativeSingularHomologyCoefficientFunctor (C := C) n).flip.obj
        (excisionSourcePair X A B) ≅
      (relativeSingularHomologyCoefficientFunctor (C := C) n).flip.obj
        (excisionTargetPair X A) :=
  HomologicalComplex.homologyNatIsoOfQuasiIsoAt
    (excisionChainMapNatTrans (C := C) X A B) n
    (fun R ↦
      (excisionChainMapNatTrans_quasiIsoULift G hG X A B hcover R).quasiIsoAt n)

@[simp]
public theorem excisionHomologyCoefficientNatIsoULift_hom_app
    (G : C) [Projective G] [CategoryTheory.IsFinitelyPresentable.{w} G]
    (hG : CategoryTheory.IsSeparator G)
    (X : TopCat.{w}) (A B : Set X)
    (hcover : (Set.univ : Set X) ⊆ interior A ∪ interior B)
    (n : ℕ) (R : C) :
    (excisionHomologyCoefficientNatIsoULift G hG X A B hcover n).hom.app R =
      (relativeSingularHomologyFunctor C R n).map
        (excisionTopPairHom X A B) := rfl

/-- Relative excision induces an isomorphism on relative homology in the
generic coefficient category. -/
public theorem isIso_excisionHomologyMapULift
    (G : C) [Projective G] [CategoryTheory.IsFinitelyPresentable.{w} G]
    (hG : CategoryTheory.IsSeparator G)
    (Y : TopCat.{w}) (A B : Set Y) (R : C)
    (h : (Set.univ : Set Y) ⊆ interior A ∪ interior B) (n : ℕ) :
    IsIso ((relativeSingularHomologyFunctor C R n).map
      (excisionTopPairHom Y A B)) := by
  change IsIso
    ((excisionHomologyCoefficientNatIsoULift G hG Y A B h n).hom.app R)
  infer_instance

/-- Homology isomorphism induced by generic relative excision. -/
public noncomputable def excisionHomologyIsoULift
    (G : C) [Projective G] [CategoryTheory.IsFinitelyPresentable.{w} G]
    (hG : CategoryTheory.IsSeparator G)
    (Y : TopCat.{w}) (A B : Set Y) (R : C)
    (h : (Set.univ : Set Y) ⊆ interior A ∪ interior B) (n : ℕ) :
    (relativeSingularHomologyFunctor C R n).obj
        (excisionSourcePair Y A B) ≅
      (relativeSingularHomologyFunctor C R n).obj
        (excisionTargetPair Y A) :=
  (excisionHomologyCoefficientNatIsoULift G hG Y A B h n).app R

@[simp]
public theorem excisionHomologyIsoULift_hom
    (G : C) [Projective G] [CategoryTheory.IsFinitelyPresentable.{w} G]
    (hG : CategoryTheory.IsSeparator G)
    (Y : TopCat.{w}) (A B : Set Y) (R : C)
    (h : (Set.univ : Set Y) ⊆ interior A ∪ interior B) (n : ℕ) :
    (excisionHomologyIsoULift G hG Y A B R h n).hom =
      (relativeSingularHomologyFunctor C R n).map
        (excisionTopPairHom Y A B) := rfl

private lemma closure_subset_interior_imp_interiors_cover_generic
    (X : TopCat.{w}) (A U : Set X) (h : closure U ⊆ interior A) :
    (Set.univ : Set X) ⊆ interior A ∪ interior Uᶜ := by
  intro x _
  by_cases hx : x ∈ closure U
  · exact Set.mem_union_left _ (h hx)
  · have hxInterior : x ∈ interior Uᶜ := by
      rw [interior_compl]
      exact hx
    exact Set.mem_union_right _ hxInterior

/-- Closure-form generic relative excision quasi-isomorphism. -/
public theorem excisionMap_quasiIsoULift_of_closure_subset_interior
    (G : C) [Projective G] [CategoryTheory.IsFinitelyPresentable.{w} G]
    (hG : CategoryTheory.IsSeparator G)
    (X : TopCat.{w}) (A U : Set X) (R : C)
    (h : closure U ⊆ interior A) :
    QuasiIso ((relativeSingularChainFunctor C R).map
      (excisionTopPairHom X A Uᶜ)) := by
  exact excisionMap_quasiIsoULift G hG X A Uᶜ R
    (closure_subset_interior_imp_interiors_cover_generic X A U h)

/-- Closure-form generic relative excision induces an isomorphism on
homology. -/
public theorem isIso_excisionHomologyMapULift_of_closure_subset_interior
    (G : C) [Projective G] [CategoryTheory.IsFinitelyPresentable.{w} G]
    (hG : CategoryTheory.IsSeparator G)
    (X : TopCat.{w}) (A U : Set X) (R : C)
    (h : closure U ⊆ interior A) (n : ℕ) :
    IsIso ((relativeSingularHomologyFunctor C R n).map
      (excisionTopPairHom X A Uᶜ)) := by
  exact isIso_excisionHomologyMapULift G hG X A Uᶜ R
    (closure_subset_interior_imp_interiors_cover_generic X A U h) n

/-- Homology isomorphism for closure-form generic relative excision. -/
public noncomputable def
    excisionHomologyIsoULift_of_closure_subset_interior
    (G : C) [Projective G] [CategoryTheory.IsFinitelyPresentable.{w} G]
    (hG : CategoryTheory.IsSeparator G)
    (X : TopCat.{w}) (A U : Set X) (R : C)
    (h : closure U ⊆ interior A) (n : ℕ) :
    (relativeSingularHomologyFunctor C R n).obj
        (excisionSourcePair X A Uᶜ) ≅
      (relativeSingularHomologyFunctor C R n).obj
        (excisionTargetPair X A) :=
  excisionHomologyIsoULift G hG X A Uᶜ R (by
    intro x _
    by_cases hx : x ∈ closure U
    · exact Set.mem_union_left _ (h hx)
    · have hxInterior : x ∈ interior Uᶜ := by
        rw [interior_compl]
        exact hx
      exact Set.mem_union_right _ hxInterior) n

@[simp]
public theorem excisionHomologyIsoULift_of_closure_subset_interior_hom
    (G : C) [Projective G] [CategoryTheory.IsFinitelyPresentable.{w} G]
    (hG : CategoryTheory.IsSeparator G)
    (X : TopCat.{w}) (A U : Set X) (R : C)
    (h : closure U ⊆ interior A) (n : ℕ) :
    (excisionHomologyIsoULift_of_closure_subset_interior
      G hG X A U R h n).hom =
      (relativeSingularHomologyFunctor C R n).map
        (excisionTopPairHom X A Uᶜ) := rfl

end GenericExcision

section AddCommGrpCompatibility

variable [UnivLE.{w, u}]

public theorem excisionTargetComp_quasiIso
    (Y : TopCat.{w}) (A B : Set Y) (R : AddCommGrpCat.{u})
    (h : (Set.univ : Set Y) ⊆ interior A ∪ interior B) :
    QuasiIso (excisionTargetComp Y A B R) :=
  excisionTargetComp_quasiIsoULift
    (AddCommGrpCat.of (ULift.{u} ℤ)) AddCommGrpCat.isSeparator_uliftInt
    Y A B R h

/-- Relative excision is a coefficient-natural quasi-isomorphism. -/
public theorem excisionChainMapNatTrans_quasiIso
    (X : TopCat.{w}) (A B : Set X)
    (hcover : (Set.univ : Set X) ⊆ interior A ∪ interior B) :
    (HomologicalComplex.quasiIso AddCommGrpCat.{u}
      (ComplexShape.down ℕ)).functorCategory AddCommGrpCat.{u}
        (excisionChainMapNatTrans (C := AddCommGrpCat.{u}) X A B) :=
  excisionChainMapNatTrans_quasiIsoULift
    (AddCommGrpCat.of (ULift.{u} ℤ)) AddCommGrpCat.isSeparator_uliftInt
    X A B hcover

/-- Relative excision induces a quasi-isomorphism of relative chain complexes. -/
public theorem excisionMap_quasiIso
    (Y : TopCat.{w}) (A B : Set Y) (R : AddCommGrpCat.{u})
    (h : (Set.univ : Set Y) ⊆ interior A ∪ interior B) :
    QuasiIso ((relativeSingularChainFunctor AddCommGrpCat.{u} R).map
      (excisionTopPairHom Y A B)) :=
  excisionMap_quasiIsoULift
    (AddCommGrpCat.of (ULift.{u} ℤ)) AddCommGrpCat.isSeparator_uliftInt
    Y A B R h

/-- Relative excision on homology, natural in coefficients. -/
public noncomputable def excisionHomologyCoefficientNatIso
    (X : TopCat.{w}) (A B : Set X)
    (hcover : (Set.univ : Set X) ⊆ interior A ∪ interior B) (n : ℕ) :
    (relativeSingularHomologyCoefficientFunctor
      (C := AddCommGrpCat.{u}) n).flip.obj (excisionSourcePair X A B) ≅
      (relativeSingularHomologyCoefficientFunctor
        (C := AddCommGrpCat.{u}) n).flip.obj (excisionTargetPair X A) :=
  excisionHomologyCoefficientNatIsoULift
    (AddCommGrpCat.of (ULift.{u} ℤ)) AddCommGrpCat.isSeparator_uliftInt
    X A B hcover n

@[simp]
public theorem excisionHomologyCoefficientNatIso_hom_app
    (X : TopCat.{w}) (A B : Set X)
    (hcover : (Set.univ : Set X) ⊆ interior A ∪ interior B)
    (n : ℕ) (R : AddCommGrpCat.{u}) :
    (excisionHomologyCoefficientNatIso X A B hcover n).hom.app R =
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R n).map
        (excisionTopPairHom X A B) := rfl

/-- Relative excision induces an isomorphism on relative homology. -/
public theorem isIso_excisionHomologyMap
    (Y : TopCat.{w}) (A B : Set Y) (R : AddCommGrpCat.{u})
    (h : (Set.univ : Set Y) ⊆ interior A ∪ interior B) (n : ℕ) :
    IsIso ((relativeSingularHomologyFunctor AddCommGrpCat.{u} R n).map
      (excisionTopPairHom Y A B)) :=
  isIso_excisionHomologyMapULift
    (AddCommGrpCat.of (ULift.{u} ℤ)) AddCommGrpCat.isSeparator_uliftInt
    Y A B R h n

/-- Homology isomorphism induced by relative excision. -/
public noncomputable def excisionHomologyIso
    (Y : TopCat.{w}) (A B : Set Y) (R : AddCommGrpCat.{u})
    (h : (Set.univ : Set Y) ⊆ interior A ∪ interior B) (n : ℕ) :
    (relativeSingularHomologyFunctor AddCommGrpCat.{u} R n).obj
        (excisionSourcePair Y A B) ≅
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R n).obj
        (excisionTargetPair Y A) :=
  excisionHomologyIsoULift
    (AddCommGrpCat.of (ULift.{u} ℤ)) AddCommGrpCat.isSeparator_uliftInt
    Y A B R h n

@[simp]
public theorem excisionHomologyIso_hom
    (Y : TopCat.{w}) (A B : Set Y) (R : AddCommGrpCat.{u})
    (h : (Set.univ : Set Y) ⊆ interior A ∪ interior B) (n : ℕ) :
    (excisionHomologyIso Y A B R h n).hom =
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R n).map
        (excisionTopPairHom Y A B) := rfl

public theorem excisionMap_quasiIso_of_closure_subset_interior
    (X : TopCat.{w}) (A U : Set X) (R : AddCommGrpCat.{u})
    (h : closure U ⊆ interior A) :
    QuasiIso ((relativeSingularChainFunctor AddCommGrpCat.{u} R).map
      (excisionTopPairHom X A Uᶜ)) :=
  excisionMap_quasiIsoULift_of_closure_subset_interior
    (AddCommGrpCat.of (ULift.{u} ℤ)) AddCommGrpCat.isSeparator_uliftInt
    X A U R h

public theorem isIso_excisionHomologyMap_of_closure_subset_interior
    (X : TopCat.{w}) (A U : Set X) (R : AddCommGrpCat.{u})
    (h : closure U ⊆ interior A) (n : ℕ) :
    IsIso ((relativeSingularHomologyFunctor AddCommGrpCat.{u} R n).map
      (excisionTopPairHom X A Uᶜ)) :=
  isIso_excisionHomologyMapULift_of_closure_subset_interior
    (AddCommGrpCat.of (ULift.{u} ℤ)) AddCommGrpCat.isSeparator_uliftInt
    X A U R h n

public noncomputable def
    excisionHomologyIso_of_closure_subset_interior
    (X : TopCat.{w}) (A U : Set X) (R : AddCommGrpCat.{u})
    (h : closure U ⊆ interior A) (n : ℕ) :
    (relativeSingularHomologyFunctor AddCommGrpCat.{u} R n).obj
        (excisionSourcePair X A Uᶜ) ≅
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R n).obj
        (excisionTargetPair X A) :=
  excisionHomologyIsoULift_of_closure_subset_interior
    (AddCommGrpCat.of (ULift.{u} ℤ)) AddCommGrpCat.isSeparator_uliftInt
    X A U R h n

@[simp]
public theorem excisionHomologyIso_of_closure_subset_interior_hom
    (X : TopCat.{w}) (A U : Set X) (R : AddCommGrpCat.{u})
    (h : closure U ⊆ interior A) (n : ℕ) :
    (excisionHomologyIso_of_closure_subset_interior X A U R h n).hom =
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R n).map
        (excisionTopPairHom X A Uᶜ) := rfl

end AddCommGrpCompatibility
end AlgebraicTopology
