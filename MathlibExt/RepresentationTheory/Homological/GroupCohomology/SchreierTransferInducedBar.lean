/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.RepresentationTheory.FiniteIndex
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierRestrictionCorestrictionArbitrary

/-!
# The induced bar resolution for finite-index transfer

Finite-index induction is both a left and a right adjoint.  It therefore
preserves the finite limits and colimits needed for homology, is additive,
and carries projective objects to projective objects.  Consequently it sends
the subgroup bar resolution to a projective resolution of the induced
trivial representation.

This file also records the normalized bar cochain obtained from the unit of
the induction--restriction adjunction.  It is the universal coefficient
cochain used to represent arbitrary Schreier transfer by a chain map into
the induced bar resolution.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Rep

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable (H : Subgroup G) [H.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- Finite-index induction is additive.  The right-adjoint structure gives
binary-product preservation, and induction preserves zero morphisms. -/
noncomputable instance indFunctorFiniteIndexAdditive :
    (indFunctor.{u} k H.subtype).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Finite-index induction preserves projective objects because restriction,
its right adjoint, preserves epimorphisms. -/
noncomputable instance indFunctorFiniteIndexPreservesProjectiveObjects :
    (indFunctor.{u} k H.subtype).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (indResAdjunction.{u} k H.subtype)

end Rep

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable (H : Subgroup G) [H.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- A finite-index right transversal has a finite type of representatives. -/
noncomputable local instance inducedBarRightTransversalFintype
    (T : H.RightTransversal) : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- The subgroup bar resolution after finite-index induction, as a
projective resolution of the induced trivial representation. -/
noncomputable def inducedBarResolution :
    ProjectiveResolution
      ((Rep.indFunctor.{u} k H.subtype).obj (Rep.trivial k H k)) :=
  (Rep.indFunctor.{u} k H.subtype).mapProjectiveResolution
    (Rep.barResolution k H)

/-- The canonical finite-index norm map from the ambient trivial
representation to the induced subgroup trivial representation. -/
noncomputable def inducedTrivialNorm :
    Rep.trivial k G k ⟶
      (Rep.indFunctor.{u} k H.subtype).obj (Rep.trivial k H k) := by
  letI : DecidableRel (QuotientGroup.rightRel H) := Classical.decRel _
  exact (Rep.resIndAdjunction.{u} k H).unit.app (Rep.trivial k G k)

section

variable (K : Type u) [Group K]

/-- The literal degree-zero bar augmentation. -/
noncomputable def barAugmentationZero :
    (Rep.barComplex k K).X 0 ⟶ Rep.trivial k K k :=
  (Rep.barComplex.isoStandardComplex k K).hom.f 0 ≫
    Rep.standardComplex.ε k K

/-- The normalized degree-zero bar basis augments to one. -/
@[simp]
theorem barAugmentationZero_barBasis :
    (barAugmentationZero (k := k) K).hom
        (barBasis (k := k) 0 Fin.elim0) = (1 : k) := by
  exact barResolution_augmentation_barBasis_zero

end

/-- The literal degree-zero augmentation after induction. -/
noncomputable def inducedBarAugmentationZero :
  (Rep.indFunctor.{u} k H.subtype).obj ((Rep.barComplex k H).X 0) ⟶
      (Rep.indFunctor.{u} k H.subtype).obj (Rep.trivial k H k) :=
  (Rep.indFunctor.{u} k H.subtype).map
    (barAugmentationZero (k := k) H)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- In degree zero, the induced bar-resolution augmentation is the literal
induction of the subgroup bar augmentation. -/
theorem inducedBarResolution_π_f_zero :
    (inducedBarResolution (k := k) H).π.f 0 =
      inducedBarAugmentationZero (k := k) H := by
  rfl

omit [H.FiniteIndex] in
/-- Induction of a coefficient morphism acts on canonical induced classes
by applying that morphism to the coefficient. -/
theorem indFunctor_map_indV_mk
    {A B : Rep k H} (f : A ⟶ B) (g : G) (a : A) :
    ((Rep.indFunctor.{u} k H.subtype).map f).hom
        (Representation.IndV.mk H.subtype A.ρ g a) =
      Representation.IndV.mk H.subtype B.ρ g (f.hom a) := by
  simp [Rep.indFunctor_map, Rep.indMap, Representation.IndV.mk]

set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse finite-index induction/coinduction comparison is a sum over
any chosen right transversal. -/
theorem coindToInd_eq_sum_rightTransversal
    (A : Rep k H) (f : Rep.coind H.subtype A)
    (T : H.RightTransversal) :
    Rep.coindToInd A f =
      ∑ t : (T : Set G),
        Representation.IndV.mk H.subtype A.ρ (t : G) (f.1 (t : G)) := by
  rw [Rep.coindToInd_apply]
  calc
    _ = ∑ q : Quotient (QuotientGroup.rightRel H),
        Representation.IndV.mk H.subtype A.ρ
          (T.2.rightQuotientEquiv q : G)
          (f.1 (T.2.rightQuotientEquiv q : G)) := by
      apply Finset.sum_congr rfl
      intro q _
      conv_lhs => rw [← T.2.mk''_rightQuotientEquiv q]
      rfl
    _ = _ := (T.2.rightQuotientEquiv.sum_comp
      (fun t : (T : Set G) ↦
        Representation.IndV.mk H.subtype A.ρ (t : G) (f.1 (t : G))))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical norm map sends one to the sum of the induced basis
vectors indexed by any right transversal. -/
theorem inducedTrivialNorm_one_eq_sum
    (T : H.RightTransversal) :
    (inducedTrivialNorm (k := k) H).hom (1 : k) =
      ∑ t : (T : Set G),
        Representation.IndV.mk H.subtype (Rep.trivial k H k).ρ
          (t : G) (1 : k) := by
  classical
  let _ : DecidableRel (QuotientGroup.rightRel H) := Classical.decRel _
  unfold inducedTrivialNorm
  rw [Rep.resIndAdjunction_unit_app]
  change Rep.coindToInd (Rep.trivial k H k)
      (((Rep.resCoindAdjunction k H.subtype).unit.app
        (Rep.trivial k G k)).hom (1 : k)) = _
  have hvalue (g : G) :
      ((((Rep.resCoindAdjunction k H.subtype).unit.app
        (Rep.trivial k G k)).hom (1 : k)).1 g) = 1 := by
    simp [Rep.resCoindAdjunction, Rep.resCoindHomEquiv,
      Rep.resCoindToHom]
  rw [coindToInd_eq_sum_rightTransversal (T := T)]
  simp_rw [hvalue]

/-- The induction-unit morphism on the degree-`n` subgroup bar object. -/
noncomputable def inducedBarUnit (n : ℕ) :
    (Rep.barComplex k H).X n ⟶
      Rep.res H.subtype
        ((Rep.indFunctor.{u} k H.subtype).obj
          ((Rep.barComplex k H).X n)) :=
  (Rep.indResAdjunction.{u} k H.subtype).unit.app
    ((Rep.barComplex k H).X n)

/-- The normalized subgroup bar cochain obtained from the unit of the
induction--restriction adjunction. -/
noncomputable def inducedBarUnitCochain (n : ℕ) :
    (Fin n → H) →
      (Rep.indFunctor.{u} k H.subtype).obj
        ((Rep.barComplex k H).X n) :=
  fun q ↦ (inducedBarUnit (k := k) H n).hom
    (barBasis (k := k) n q)

omit [H.FiniteIndex] in
/-- The normalized-basis formula for the induction-unit cochain. -/
@[simp]
theorem inducedBarUnitCochain_apply (n : ℕ) (q : Fin n → H) :
    inducedBarUnitCochain (k := k) H n q =
      (inducedBarUnit (k := k) H n).hom (barBasis (k := k) n q) :=
  rfl

omit [H.FiniteIndex] in
/-- The induction-unit cochain is the canonical induced class with ambient
group coordinate one. -/
theorem inducedBarUnitCochain_eq_indV_mk
    (n : ℕ) (q : Fin n → H) :
    inducedBarUnitCochain (k := k) H n q =
      Representation.IndV.mk H.subtype
        ((Rep.barComplex k H).X n).ρ 1 (barBasis (k := k) n q) := by
  rfl

omit [H.FiniteIndex] in
/-- Applying an ambient morphism after the induction unit is the morphism
obtained from the induction--restriction adjunction. -/
theorem hom_inducedBarUnitCochain
    (A : Rep k G) (n : ℕ)
    (phi : (Rep.indFunctor.{u} k H.subtype).obj
      ((Rep.barComplex k H).X n) ⟶ A)
    (q : Fin n → H) :
    phi.hom (inducedBarUnitCochain (k := k) H n q) =
      ((Rep.indResHomEquiv H.subtype
        ((Rep.barComplex k H).X n) A) phi).hom
          (barBasis (k := k) n q) := by
  rfl

omit [H.FiniteIndex] in
/-- The adjoint of a subgroup free-lift evaluates the universal induction
unit cochain as the original inhomogeneous cochain. -/
theorem indResHomEquiv_symm_freeLift_inducedBarUnitCochain
    (A : Rep k G) (n : ℕ) (z : (Fin n → H) → A)
    (q : Fin n → H) :
    let zHom : (Rep.barComplex k H).X n ⟶
        Rep.res H.subtype A :=
      Rep.freeLift k H (Rep.res H.subtype A) z
    let phi : (Rep.indFunctor.{u} k H.subtype).obj
        ((Rep.barComplex k H).X n) ⟶ A :=
      (Rep.indResHomEquiv H.subtype
        ((Rep.barComplex k H).X n) A).symm zHom
    phi.hom (inducedBarUnitCochain (k := k) H n q) = z q := by
  dsimp only
  rw [hom_inducedBarUnitCochain]
  rw [LinearEquiv.apply_symm_apply]
  exact freeLift_barBasis (Rep.res H.subtype A) n z q

omit [H.FiniteIndex] in
/-- Free extension of the universal induction-unit cochain is the adjunction
unit itself. -/
theorem freeLift_inducedBarUnitCochain (n : ℕ) :
    Rep.freeLift k H
        (Rep.res H.subtype
          ((Rep.indFunctor.{u} k H.subtype).obj
            ((Rep.barComplex k H).X n)))
        (inducedBarUnitCochain (k := k) H n) =
      inducedBarUnit (k := k) H n := by
  apply Rep.free_ext k H _
  intro q
  change (Rep.freeLift k H
      (Rep.res H.subtype
        ((Rep.indFunctor.{u} k H.subtype).obj
          ((Rep.barComplex k H).X n)))
      (inducedBarUnitCochain (k := k) H n)).hom
        (barBasis (k := k) n q) =
    (inducedBarUnit (k := k) H n).hom (barBasis (k := k) n q)
  rw [freeLift_barBasis]
  rfl

omit [H.FiniteIndex] in
/-- The inhomogeneous differential of the universal induction-unit cochain
is obtained by applying the induced subgroup bar differential to the next
unit cochain. -/
theorem inhomogeneous_d_inducedBarUnitCochain (n : ℕ) :
    (inhomogeneousCochains.d
      (Rep.res H.subtype
        ((Rep.indFunctor.{u} k H.subtype).obj
          ((Rep.barComplex k H).X n))) n).hom
        (inducedBarUnitCochain (k := k) H n) =
      fun q ↦
        ((Rep.indFunctor.{u} k H.subtype).map
          ((Rep.barComplex k H).d (n + 1) n)).hom
            (inducedBarUnitCochain (k := k) H (n + 1) q) := by
  let dH := (Rep.barComplex k H).d (n + 1) n
  let phi := (Rep.indFunctor.{u} k H.subtype).map dH
  have hnat := (Rep.indResAdjunction.{u} k H.subtype).unit.naturality dH
  have hbar := barComplex_d_comp_freeLift
    (Rep.res H.subtype
      ((Rep.indFunctor.{u} k H.subtype).obj
        ((Rep.barComplex k H).X n))) n
    (inducedBarUnitCochain (k := k) H n)
  have hmor : inducedBarUnit (k := k) H (n + 1) ≫
        (Rep.resFunctor H.subtype).map phi =
      Rep.freeLift k H
        (Rep.res H.subtype
          ((Rep.indFunctor.{u} k H.subtype).obj
            ((Rep.barComplex k H).X n)))
        ((inhomogeneousCochains.d
          (Rep.res H.subtype
            ((Rep.indFunctor.{u} k H.subtype).obj
              ((Rep.barComplex k H).X n))) n).hom
          (inducedBarUnitCochain (k := k) H n)) := by
    calc
      inducedBarUnit (k := k) H (n + 1) ≫
          (Rep.resFunctor H.subtype).map phi =
        dH ≫ inducedBarUnit (k := k) H n := hnat
      _ = dH ≫ Rep.freeLift k H
          (Rep.res H.subtype
            ((Rep.indFunctor.{u} k H.subtype).obj
              ((Rep.barComplex k H).X n)))
          (inducedBarUnitCochain (k := k) H n) := by
        rw [freeLift_inducedBarUnitCochain]
      _ = _ := hbar
  funext q
  have hq := congrArg (fun f ↦ f.hom (barBasis (k := k) (n + 1) q)) hmor
  change
    (inhomogeneousCochains.d
      (Rep.res H.subtype
        ((Rep.indFunctor.{u} k H.subtype).obj
          ((Rep.barComplex k H).X n))) n).hom
        (inducedBarUnitCochain (k := k) H n) q =
      phi.hom (inducedBarUnitCochain (k := k) H (n + 1) q)
  calc
    _ = (Rep.freeLift k H
          (Rep.res H.subtype
            ((Rep.indFunctor.{u} k H.subtype).obj
              ((Rep.barComplex k H).X n)))
          ((inhomogeneousCochains.d
            (Rep.res H.subtype
              ((Rep.indFunctor.{u} k H.subtype).obj
                ((Rep.barComplex k H).X n))) n).hom
            (inducedBarUnitCochain (k := k) H n))).hom
          (barBasis (k := k) (n + 1) q) := by
        rw [freeLift_barBasis]
    _ = ((Rep.resFunctor H.subtype).map phi).hom
          (inducedBarUnitCochain (k := k) H (n + 1) q) := by
        exact hq.symm
    _ = _ := rfl

/-- Degree-`n` universal chain component representing chosen-transversal
Schreier transfer into the induced subgroup bar object. -/
noncomputable def schreierTransferInducedBarComponent
    (T : H.RightTransversal) (n : ℕ) :
    (Rep.barComplex k G).X n ⟶
      (Rep.indFunctor.{u} k H.subtype).obj
        ((Rep.barComplex k H).X n) :=
  Rep.freeLift k G _
    (corestrictionCochain
      ((Rep.indFunctor.{u} k H.subtype).obj
        ((Rep.barComplex k H).X n)) T n
      (inducedBarUnitCochain (k := k) H n))

theorem schreierTransferInducedBarComponent_barBasis
    (T : H.RightTransversal) (n : ℕ)
    (g : Fin n → G) :
    (schreierTransferInducedBarComponent (k := k) H T n).hom
        (barBasis (k := k) n g) =
      corestrictionCochain
        ((Rep.indFunctor.{u} k H.subtype).obj
          ((Rep.barComplex k H).X n)) T n
        (inducedBarUnitCochain (k := k) H n) g := by
  unfold schreierTransferInducedBarComponent
  exact freeLift_barBasis _ n _ g

/-- Precomposition by the universal induced-bar component is the arbitrary
chosen-transversal Schreier transfer on every coefficient cochain. -/
theorem schreierTransferInducedBarComponent_comp_adjointFreeLift
    (A : Rep k G) (T : H.RightTransversal)
    (n : ℕ) (z : (Fin n → H) → A) :
    let zHom : (Rep.barComplex k H).X n ⟶
        Rep.res H.subtype A :=
      Rep.freeLift k H (Rep.res H.subtype A) z
    let phi : (Rep.indFunctor.{u} k H.subtype).obj
        ((Rep.barComplex k H).X n) ⟶ A :=
      (Rep.indResHomEquiv H.subtype
        ((Rep.barComplex k H).X n) A).symm zHom
    schreierTransferInducedBarComponent (k := k) H T n ≫ phi =
      Rep.freeLift k G A (corestrictionCochain A T n z) := by
  dsimp only
  apply Rep.free_ext k G A
  intro g
  change ((Rep.indResHomEquiv H.subtype
      ((Rep.barComplex k H).X n) A).symm
        (Rep.freeLift k H (Rep.res H.subtype A) z)).hom
      ((schreierTransferInducedBarComponent (k := k) H T n).hom
        (barBasis (k := k) n g)) =
    (Rep.freeLift k G A (corestrictionCochain A T n z)).hom
      (barBasis (k := k) n g)
  rw [schreierTransferInducedBarComponent_barBasis,
    freeLift_barBasis]
  have h := congrFun
    (corestrictionCochain_naturality
      ((Rep.indResHomEquiv H.subtype
        ((Rep.barComplex k H).X n) A).symm
          (Rep.freeLift k H (Rep.res H.subtype A) z))
      T n (inducedBarUnitCochain (k := k) H n)) g
  have hunit :
      (fun q : Fin n → H ↦
        ((Rep.indResHomEquiv H.subtype
          ((Rep.barComplex k H).X n) A).symm
            (Rep.freeLift k H (Rep.res H.subtype A) z)).hom
          (inducedBarUnitCochain (k := k) H n q)) = z := by
    funext q
    exact indResHomEquiv_symm_freeLift_inducedBarUnitCochain
      (k := k) H A n z q
  rw [hunit] at h
  exact h

/-- Consecutive universal induced-bar transfer components commute with the
bar differentials. -/
theorem schreierTransferInducedBarComponent_comm
    (T : H.RightTransversal) (n : ℕ) :
    schreierTransferInducedBarComponent (k := k) H T (n + 1) ≫
        (Rep.indFunctor.{u} k H.subtype).map
          ((Rep.barComplex k H).d (n + 1) n) =
      (Rep.barComplex k G).d (n + 1) n ≫
        schreierTransferInducedBarComponent (k := k) H T n := by
  let PHn := (Rep.barComplex k H).X n
  let A : Rep k G := (Rep.indFunctor.{u} k H.subtype).obj PHn
  let U := inducedBarUnitCochain (k := k) H n
  let C := corestrictionCochain A T n U
  let dH := (Rep.barComplex k H).d (n + 1) n
  let phi := (Rep.indFunctor.{u} k H.subtype).map dH
  have hunit :
      (inhomogeneousCochains.d (Rep.res H.subtype A) n).hom U =
        fun q ↦ phi.hom
          (inducedBarUnitCochain (k := k) H (n + 1) q) := by
    exact inhomogeneous_d_inducedBarUnitCochain (k := k) H n
  have hleft :
      (fun g ↦ phi.hom
        (corestrictionCochain
          ((Rep.indFunctor.{u} k H.subtype).obj
            ((Rep.barComplex k H).X (n + 1))) T (n + 1)
          (inducedBarUnitCochain (k := k) H (n + 1)) g)) =
        (inhomogeneousCochains.d A n).hom C := by
    calc
      _ = corestrictionCochain A T (n + 1)
          (fun q ↦ phi.hom
            (inducedBarUnitCochain (k := k) H (n + 1) q)) :=
        corestrictionCochain_naturality phi T (n + 1)
          (inducedBarUnitCochain (k := k) H (n + 1))
      _ = corestrictionCochain A T (n + 1)
          ((inhomogeneousCochains.d (Rep.res H.subtype A) n).hom U) := by
        rw [hunit]
      _ = (inhomogeneousCochains.d A n).hom C :=
        corestrictionCochain_d A T n U
  apply Rep.free_ext k G A
  intro g
  change phi.hom
      ((schreierTransferInducedBarComponent (k := k) H T (n + 1)).hom
        (barBasis (k := k) (n + 1) g)) =
    (schreierTransferInducedBarComponent (k := k) H T n).hom
      (((Rep.barComplex k G).d (n + 1) n).hom
        (barBasis (k := k) (n + 1) g))
  rw [schreierTransferInducedBarComponent_barBasis]
  have hg := congrFun hleft g
  rw [hg]
  have hbar := barComplex_d_comp_freeLift A n C
  have hbasis := congrArg
    (fun f ↦ f.hom (barBasis (k := k) (n + 1) g)) hbar
  calc
    (inhomogeneousCochains.d A n).hom C g =
        (Rep.freeLift k G A
          ((inhomogeneousCochains.d A n).hom C)).hom
          (barBasis (k := k) (n + 1) g) :=
      (freeLift_barBasis A (n + 1)
        ((inhomogeneousCochains.d A n).hom C) g).symm
    _ = ((Rep.barComplex k G).d (n + 1) n ≫
          Rep.freeLift k G A C).hom
          (barBasis (k := k) (n + 1) g) := hbasis.symm
    _ = (schreierTransferInducedBarComponent (k := k) H T n).hom
        (((Rep.barComplex k G).d (n + 1) n).hom
          (barBasis (k := k) (n + 1) g)) := rfl

/-- The literal chain map from the ambient bar complex to the induced
subgroup bar complex which represents arbitrary Schreier transfer. -/
noncomputable def schreierTransferInducedBarChain
    (T : H.RightTransversal) :
    Rep.barComplex k G ⟶
      ((Rep.indFunctor.{u} k H.subtype).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (Rep.barComplex k H) where
  f n := schreierTransferInducedBarComponent (k := k) H T n
  comm' i j hij := by
    rcases hij with ⟨rfl⟩
    exact schreierTransferInducedBarComponent_comm H T j

@[simp]
theorem schreierTransferInducedBarChain_f
    (T : H.RightTransversal) (n : ℕ) :
    (schreierTransferInducedBarChain (k := k) H T).f n =
      schreierTransferInducedBarComponent (k := k) H T n :=
  rfl

/-- The same transfer chain map, typed between the exact complexes carried
by the ambient and induced bar projective resolutions. -/
noncomputable def schreierTransferInducedBar
    (T : H.RightTransversal) :
    (Rep.barResolution k G).complex ⟶
      (inducedBarResolution (k := k) H).complex := by
  rw [Rep.barResolution_complex]
  change Rep.barComplex k G ⟶
    ((Rep.indFunctor.{u} k H.subtype).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (Rep.barResolution k H).complex
  rw [Rep.barResolution_complex]
  exact schreierTransferInducedBarChain (k := k) H T

set_option backward.isDefEq.respectTransparency false in
/-- On the normalized degree-zero basis, the universal transfer followed by
the induced bar augmentation is the canonical finite-index norm map. -/
theorem schreierTransferInducedBarComponent_zero_augmentation
    (T : H.RightTransversal) :
    (inducedBarAugmentationZero (k := k) H).hom
        ((schreierTransferInducedBarComponent (k := k) H T 0).hom
          (barBasis (k := k) 0 Fin.elim0)) =
      (inducedTrivialNorm (k := k) H).hom (1 : k) := by
  rw [schreierTransferInducedBarComponent_barBasis,
    corestrictionCochain_apply, map_sum]
  have hterm (t : (T : Set G)) :
      (inducedBarAugmentationZero (k := k) H).hom
          (((Rep.indFunctor.{u} k H.subtype).obj
            ((Rep.barComplex k H).X 0)).ρ (t : G)⁻¹
            (inducedBarUnitCochain (k := k) H 0
              (T.schreierFactorTuple t Fin.elim0))) =
        Representation.IndV.mk H.subtype (Rep.trivial k H k).ρ
          (t : G) (1 : k) := by
    have hempty : T.schreierFactorTuple t Fin.elim0 =
        (Fin.elim0 : Fin 0 → H) := Subsingleton.elim _ _
    rw [hempty, Rep.hom_comm_apply,
      inducedBarUnitCochain_eq_indV_mk]
    change ((Rep.indFunctor.{u} k H.subtype).obj
        (Rep.trivial k H k)).ρ (t : G)⁻¹
      ((inducedBarAugmentationZero (k := k) H).hom
          (Representation.IndV.mk H.subtype
            ((Rep.barComplex k H).X 0).ρ 1
            (barBasis (k := k) 0 Fin.elim0))) = _
    unfold inducedBarAugmentationZero
    rw [indFunctor_map_indV_mk]
    change (Representation.ind H.subtype (Rep.trivial k H k).ρ)
        ((t : G)⁻¹)
        (Representation.IndV.mk H.subtype (Rep.trivial k H k).ρ 1
          ((barAugmentationZero (k := k) H).hom
            (barBasis (k := k) 0 Fin.elim0))) = _
    rw [Representation.ind_mk]
    rw [barAugmentationZero_barBasis]
    simp
  simp_rw [hterm]
  exact (inducedTrivialNorm_one_eq_sum (k := k) H T).symm

/-- Degree-zero augmentation square for the universal induced-bar transfer
component. -/
theorem schreierTransferInducedBarComponent_zero_comp_augmentation
    (T : H.RightTransversal) :
    schreierTransferInducedBarComponent (k := k) H T 0 ≫
        inducedBarAugmentationZero (k := k) H =
      barAugmentationZero (k := k) G ≫
        inducedTrivialNorm (k := k) H := by
  apply Rep.free_ext k G _
  intro g
  have hg : g = (Fin.elim0 : Fin 0 → G) := Subsingleton.elim _ _
  subst g
  change (inducedBarAugmentationZero (k := k) H).hom
      ((schreierTransferInducedBarComponent (k := k) H T 0).hom
        (barBasis (k := k) 0 Fin.elim0)) =
    (inducedTrivialNorm (k := k) H).hom
      ((barAugmentationZero (k := k) G).hom
        (barBasis (k := k) 0 Fin.elim0))
  rw [schreierTransferInducedBarComponent_zero_augmentation,
    barAugmentationZero_barBasis]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Every chosen-transversal induced-bar transfer lifts the same canonical
finite-index norm map between the resolved trivial representations. -/
theorem schreierTransferInducedBar_comp_π
    (T : H.RightTransversal) :
    schreierTransferInducedBar (k := k) H T ≫
        (inducedBarResolution (k := k) H).π =
      (Rep.barResolution k G).π ≫
        (ChainComplex.single₀ (Rep k G)).map
          (inducedTrivialNorm (k := k) H) := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
      change schreierTransferInducedBarComponent (k := k) H T 0 ≫
          inducedBarAugmentationZero (k := k) H =
        barAugmentationZero (k := k) G ≫
          inducedTrivialNorm (k := k) H
      exact schreierTransferInducedBarComponent_zero_comp_augmentation H T
  | succ n => simp

/-- Universal induced-bar transfers attached to two right transversals are
chain homotopic, since they lift the same canonical norm map. -/
noncomputable def schreierTransferInducedBarHomotopy
    (T U : H.RightTransversal) :
    Homotopy
      (schreierTransferInducedBar (k := k) H T)
      (schreierTransferInducedBar (k := k) H U) :=
  ProjectiveResolution.liftHomotopy
    (inducedTrivialNorm (k := k) H)
    (schreierTransferInducedBar (k := k) H T)
    (schreierTransferInducedBar (k := k) H U)
    (schreierTransferInducedBar_comp_π H T)
    (schreierTransferInducedBar_comp_π H U)

end groupCohomology
