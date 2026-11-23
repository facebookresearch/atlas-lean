/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SingularHomology.ReducedCoefficientFunctor
public import MathlibExt.Topology.Sphere.StandardCover

/-!
# Coefficient-generic sphere transport module

Isolates coefficient-generic ordinary and reduced homology transport for
homeomorphisms, the IOI deformation retract, and the sphere equator.

Main APIs:
* `homeoHomologyIso R k h` and `homeoReducedHomologyIso R k h`
* `ioiHomologyIso R k Y` and `ioiReducedHomologyIso R k Y`
* `equatorHomologyIso R m k` and `reducedEquatorIso R m k`

Plus `[simp]` rfl `hom`/`inv` lemmas for the four transport isos.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicTopology

universe w v u

section HomeoTransport

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- Ordinary homology transport along a homeomorphism, via functoriality. -/
noncomputable def homeoHomologyIso (R : C) (k : ℕ) {X Y : TopCat.{w}} (h : X ≃ₜ Y) :
    ((singularHomologyFunctor C k).obj R).obj X ≅ ((singularHomologyFunctor C k).obj R).obj Y :=
  ((singularHomologyFunctor C k).obj R).mapIso (TopCat.isoOfHomeo h)

/-- Reduced homology transport along a homeomorphism, via functoriality. -/
noncomputable def homeoReducedHomologyIso (R : C) (k : ℕ) {X Y : TopCat.{w}} (h : X ≃ₜ Y) :
    reducedSingularHomology C R k X ≅ reducedSingularHomology C R k Y :=
  (reducedSingularHomologyFunctor C R k).mapIso (TopCat.isoOfHomeo h)

@[simp]
lemma homeoHomologyIso_hom (R : C) (k : ℕ) {X Y : TopCat.{w}} (h : X ≃ₜ Y) :
    (homeoHomologyIso R k h).hom =
      ((singularHomologyFunctor C k).obj R).map (TopCat.isoOfHomeo h).hom :=
  rfl

@[simp]
lemma homeoHomologyIso_inv (R : C) (k : ℕ) {X Y : TopCat.{w}} (h : X ≃ₜ Y) :
    (homeoHomologyIso R k h).inv =
      ((singularHomologyFunctor C k).obj R).map (TopCat.isoOfHomeo h).inv :=
  rfl

@[simp]
lemma homeoReducedHomologyIso_hom (R : C) (k : ℕ) {X Y : TopCat.{w}} (h : X ≃ₜ Y) :
    (homeoReducedHomologyIso R k h).hom =
      (reducedSingularHomologyFunctor C R k).map (TopCat.isoOfHomeo h).hom :=
  rfl

@[simp]
lemma homeoReducedHomologyIso_inv (R : C) (k : ℕ) {X Y : TopCat.{w}} (h : X ≃ₜ Y) :
    (homeoReducedHomologyIso R k h).inv =
      (reducedSingularHomologyFunctor C R k).map (TopCat.isoOfHomeo h).inv :=
  rfl

/-- Reduced homology transport along a homeomorphism is natural in the coefficient object. -/
theorem homeoReducedHomologyIso_hom_naturality_coefficient
    {R S : C} (a : R ⟶ S) (k : ℕ) {X Y : TopCat.{w}} (h : X ≃ₜ Y) :
    ((reducedSingularHomologyCoefficientFunctor C k).map a).app X ≫
        (homeoReducedHomologyIso S k h).hom =
      (homeoReducedHomologyIso R k h).hom ≫
        ((reducedSingularHomologyCoefficientFunctor C k).map a).app Y := by
  exact ((reducedSingularHomologyCoefficientFunctor C k).map a).naturality
    (TopCat.isoOfHomeo h).hom |>.symm

end HomeoTransport

section IOITransport

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{0} C]

/-- IOI deformation retract on ordinary homology: `Hₖ(Y × Ioi) ≅ Hₖ(Y)`. -/
noncomputable def ioiHomologyIso (R : C) (k : ℕ) (Y : TopCat.{0}) :
    ((singularHomologyFunctor C k).obj R).obj (TopCat.of (Y × ↥(Set.Ioi (0:ℝ)))) ≅
      ((singularHomologyFunctor C k).obj R).obj Y :=
  singularHomologyMapIso C k (ioiProj Y) (ioiSect Y) (ioiContraction Y)
    (by rw [ioiSect_comp_ioiProj]; exact ContinuousMap.Homotopy.refl _) R

/-- IOI deformation retract on reduced homology: `H̃ₖ(Y × Ioi) ≅ H̃ₖ(Y)`. -/
noncomputable def ioiReducedHomologyIso (R : C) (k : ℕ) (Y : TopCat.{0}) :
    reducedSingularHomology C R k (TopCat.of (Y × ↥(Set.Ioi (0:ℝ)))) ≅
      reducedSingularHomology C R k Y :=
  reducedSingularHomologyMapIso C k (ioiProj Y) (ioiSect Y) (ioiContraction Y)
    (by rw [ioiSect_comp_ioiProj]; exact ContinuousMap.Homotopy.refl _) R

@[simp]
lemma ioiHomologyIso_hom (R : C) (k : ℕ) (Y : TopCat.{0}) :
    (ioiHomologyIso R k Y).hom =
      ((singularHomologyFunctor C k).obj R).map (ioiProj Y) :=
  rfl

@[simp]
lemma ioiHomologyIso_inv (R : C) (k : ℕ) (Y : TopCat.{0}) :
    (ioiHomologyIso R k Y).inv =
      ((singularHomologyFunctor C k).obj R).map (ioiSect Y) :=
  rfl

@[simp]
lemma ioiReducedHomologyIso_hom (R : C) (k : ℕ) (Y : TopCat.{0}) :
    (ioiReducedHomologyIso R k Y).hom =
      (reducedSingularHomologyFunctor C R k).map (ioiProj Y) :=
  rfl

@[simp]
lemma ioiReducedHomologyIso_inv (R : C) (k : ℕ) (Y : TopCat.{0}) :
    (ioiReducedHomologyIso R k Y).inv =
      (reducedSingularHomologyFunctor C R k).map (ioiSect Y) :=
  rfl

/-- Equator iso for ordinary homology: `Hₖ(S^{m+1} cover intersection) ≅ Hₖ(S^m)`. -/
noncomputable def equatorHomologyIso (R : C) (m k : ℕ) :
    ((singularHomologyFunctor C k).obj R).obj
        (TopCat.of ↥(sphereCoverA (m + 1) ∩ sphereCoverB (m + 1))) ≅
      ((singularHomologyFunctor C k).obj R).obj (TopCat.sphere.{0} m) :=
  homeoHomologyIso R k (equatorHomeo m) ≪≫
    ioiHomologyIso R k (TopCat.of ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)) ≪≫
    homeoHomologyIso R k
      (Homeomorph.ulift (X := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1))).symm

/-- Equator iso for reduced homology: `H̃ₖ(S^{m+1} cover intersection) ≅ H̃ₖ(S^m)`. -/
noncomputable def reducedEquatorIso (R : C) (m k : ℕ) :
    reducedSingularHomology C R k
        (TopCat.of ↥(sphereCoverA (m + 1) ∩ sphereCoverB (m + 1))) ≅
      reducedSingularHomology C R k (TopCat.sphere.{0} m) :=
  homeoReducedHomologyIso R k (equatorHomeo m) ≪≫
    ioiReducedHomologyIso R k (TopCat.of ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)) ≪≫
    homeoReducedHomologyIso R k
      (Homeomorph.ulift (X := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1))).symm

end IOITransport

end AlgebraicTopology
