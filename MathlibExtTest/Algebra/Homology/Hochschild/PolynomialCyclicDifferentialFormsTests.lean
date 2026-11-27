/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Codex
module

public import MathlibExt.Algebra.Homology.Hochschild.CyclicHomologyOne
public import MathlibExt.Algebra.Homology.Hochschild.AdjacentBarCoefficientComparison
public import MathlibExt.Algebra.Homology.Hochschild.PolynomialDifferentialFormComplexComparison
public import Mathlib.Order.Fin.Basic
public import Mathlib.Tactic.Ring

/-!
# Polynomial cyclic classes and differential forms

Let `A = ℚ[X,Y]`. The cyclic class of `X ⊗ Y` corresponds to `[X dY]`
in `Ω¹(A/ℚ)/dA` and is nonzero: its two polynomial coordinates have curl
one, whereas exact differentials have curl zero. The class of `d(X²)`
vanishes although `d(X²) = 2X dX`.

The polynomial Koszul-to-Bar comparison represents the Hochschild class
by the same tensor `X ⊗ Y`. The HKR comparison sends it to `X dY`.
The oriented coordinate of `dX ∧ dY` is one, and the coordinate of
`d(X² + Y) ∧ d(XY)` is the Jacobian determinant `2X² - Y`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open ModuleCat.Algebra.Hochschild
open ModuleCat.Algebra.Hochschild.PolynomialDiagonal
open scoped TensorProduct

namespace PolynomialCyclicDifferentialFormsTests

abbrev A := MvPolynomial (Fin 2) ℚ
abbrev Ω := KaehlerDifferential ℚ A
abbrev X : A := MvPolynomial.X 0
abbrev Y : A := MvPolynomial.X 1
abbrev HH := Symmetric.chainComplex ℚ A A

abbrev rawXY : A ⊗[ℚ] TensorPower ℚ 1 A :=
  X ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ (fun _ : Fin 1 => Y)

abbrev freeXY : A ⊗[ℚ] (⋀[ℚ]^1 (Fin 2 →₀ ℚ)) :=
  X ⊗ₜ[ℚ] exteriorPower.ιMulti ℚ 1
    (fun _ : Fin 1 => Finsupp.single (1 : Fin 2) (1 : ℚ))

abbrev formXY : A ⊗[A] (⋀[A]^1 Ω) :=
  X ⊗ₜ[A] exteriorPower.ιMulti A 1
    (fun _ : Fin 1 => KaehlerDifferential.D ℚ A Y)

abbrev hcXY : NonUnital.cyclicHomology ℚ A 1 :=
  (cyclicOneClass ℚ A).hom rawXY

abbrev hhXY : HH.homology 1 :=
  polynomialAntisymmetricExteriorClass ℚ (Fin 2) A 1 freeXY

abbrev yColumn : Set.powersetCard (Fin 2) 1 :=
  Set.powersetCard.ofFinEmbEquiv (Fin.succOrderEmb 1)

abbrev bothColumns : Set.powersetCard (Fin 2) 2 :=
  Set.powersetCard.ofFinEmbEquiv ((OrderIso.refl (Fin 2)).toOrderEmbedding)

abbrev basisTwo : ⋀[A]^2 Ω :=
  exteriorPower.ιMulti A 2
    (fun j : Fin 2 => KaehlerDifferential.D ℚ A (MvPolynomial.X j))

abbrev jacobianWord : Fin 2 → A := ![X ^ 2 + Y, X * Y]

private lemma yColumn_selector (j : Fin 1) :
    Set.powersetCard.ofFinEmbEquiv.symm yColumn j = (1 : Fin 2) := by
  calc
    _ = Fin.succOrderEmb 1 j :=
      congrArg (fun e : Fin 1 ↪o Fin 2 => e j)
        (Equiv.symm_apply_apply Set.powersetCard.ofFinEmbEquiv (Fin.succOrderEmb 1))
    _ = 1 := by
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rfl

private lemma bothColumns_selector (j : Fin 2) :
    Set.powersetCard.ofFinEmbEquiv.symm bothColumns j = j :=
  congrArg (fun e : Fin 2 ↪o Fin 2 => e j)
    (Equiv.symm_apply_apply Set.powersetCard.ofFinEmbEquiv
      ((OrderIso.refl (Fin 2)).toOrderEmbedding))

private lemma differential_class_zero (f : A) :
    kaehlerClass ℚ A (KaehlerDifferential.D ℚ A f) = 0 := by
  change (Submodule.Quotient.mk (KaehlerDifferential.D ℚ A f) :
    KaehlerExactQuotient ℚ A) = 0
  exact (Submodule.Quotient.mk_eq_zero
    (LinearMap.range (KaehlerDifferential.D ℚ A).toLinearMap)).mpr ⟨f, rfl⟩

private lemma xy_form_class_ne_zero :
    kaehlerClass ℚ A (X • KaehlerDifferential.D ℚ A Y) ≠ 0 := by
  intro hz
  change (Submodule.Quotient.mk (X • KaehlerDifferential.D ℚ A Y) :
    KaehlerExactQuotient ℚ A) = 0 at hz
  have hmem : X • KaehlerDifferential.D ℚ A Y ∈
      LinearMap.range (KaehlerDifferential.D ℚ A).toLinearMap :=
    (Submodule.Quotient.mk_eq_zero
      (LinearMap.range (KaehlerDifferential.D ℚ A).toLinearMap)).mp hz
  obtain ⟨f, hf⟩ := hmem
  change KaehlerDifferential.D ℚ A f = X • KaehlerDifferential.D ℚ A Y at hf
  have hx : MvPolynomial.pderiv (0 : Fin 2) f = 0 := by
    have h := congrArg
      (fun ω : Ω => (KaehlerDifferential.mvPolynomialBasis ℚ (Fin 2)).repr ω 0) hf
    simpa [KaehlerDifferential.mvPolynomialBasis_repr_apply, map_smul,
      Finsupp.smul_apply, smul_eq_mul, X, Y] using h
  have hy : MvPolynomial.pderiv (1 : Fin 2) f = X := by
    have h := congrArg
      (fun ω : Ω => (KaehlerDifferential.mvPolynomialBasis ℚ (Fin 2)).repr ω 1) hf
    simpa [KaehlerDifferential.mvPolynomialBasis_repr_apply, map_smul,
      Finsupp.smul_apply, smul_eq_mul, X, Y] using h
  have hc := MvPolynomial.pderiv_comm (0 : Fin 2) (1 : Fin 2) f
  rw [hy, hx] at hc
  have hOne : (1 : A) = 0 := by simpa [X] using hc
  exact one_ne_zero hOne

private lemma signed_xy :
    polynomialSignedRepresentative ℚ (Fin 2) A 1 freeXY = rawXY := by
  have hCoordinates :
      (KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv ℚ (Fin 2) A 1).symm
        formXY = freeXY :=
    KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv_symm_tmul_basis
      ℚ (Fin 2) A 1 X (fun _ : Fin 1 => (1 : Fin 2))
  have hComparison :
      ((polynomialDifferentialFormComparison ℚ (Fin 2) A).inv.f 1).hom
        (ULift.up formXY) = polynomialSignedRepresentative ℚ (Fin 2) A 1 freeXY :=
    (polynomialDifferentialFormComparison_inv_f_up ℚ (Fin 2) A 1 formXY).trans
      (congrArg (polynomialSignedRepresentative ℚ (Fin 2) A 1) hCoordinates)
  have hWord :
      ((polynomialDifferentialFormComparison ℚ (Fin 2) A).inv.f 1).hom
        (ULift.up formXY) = rawXY := by
    have h := polynomialDifferentialFormComparison_inv_f_basis
      ℚ (Fin 2) A 1 X (fun _ : Fin 1 => (1 : Fin 2))
    rw [Fintype.sum_subsingleton _ (1 : Equiv.Perm (Fin 1))] at h
    simpa [formXY, rawXY, Y] using h
  exact hComparison.symm.trans hWord

private lemma raw_xy_cycle : (HH.sc 1).g.hom rawXY = 0 := by
  have h := polynomialSignedRepresentative_cycle ℚ (Fin 2) A 1 freeXY
  change (HH.sc 1).g.hom
    (polynomialSignedRepresentative ℚ (Fin 2) A 1 freeXY) = 0 at h
  exact (congrArg (HH.sc 1).g.hom signed_xy).symm.trans h

private lemma hkr_xy :
    (((polynomialDifferentialFormHomologyIso ℚ (Fin 2) A 1).hom).hom hhXY).down =
      formXY := by
  rw [polynomialDifferentialFormHomologyIso_hom_down]
  change KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv ℚ (Fin 2) A 1
    (symmetricHochschildFreeExteriorEquiv ℚ (Fin 2) A 1
      (polynomialAntisymmetricExteriorClass ℚ (Fin 2) A 1 freeXY)) = formXY
  rw [polynomialAntisymmetricExteriorClass_coordinates]
  exact KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv_tmul_basis
    ℚ (Fin 2) A 1 X (fun _ : Fin 1 => (1 : Fin 2))

private lemma form_xy_coordinate :
    KaehlerDifferential.mvPolynomialCoefficientFormCoordinate ℚ (Fin 2) A 1 yColumn
      formXY = X := by
  simpa only [yColumn_selector, Y, formXY] using
    KaehlerDifferential.mvPolynomialCoefficientFormCoordinate_basis
      ℚ (Fin 2) A 1 yColumn X

private lemma basis_two_coordinate :
    KaehlerDifferential.mvPolynomialFormCoordinate ℚ (Fin 2) 2 bothColumns basisTwo = 1 := by
  simpa only [bothColumns_selector, basisTwo] using
    KaehlerDifferential.mvPolynomialFormCoordinate_basis ℚ (Fin 2) 2 bothColumns

/-- The universal differential of `X²` is the nonconstant form `2X dX`. -/
example : KaehlerDifferential.D ℚ A (X ^ 2) =
    (2 * X) • KaehlerDifferential.D ℚ A X := by
  rw [pow_two, (KaehlerDifferential.D ℚ A).leibniz, two_mul, add_smul]

/-- The exact differential `d(X²)` vanishes in the ground-linear quotient `Ω¹/dA`. -/
example : kaehlerClass ℚ A (KaehlerDifferential.D ℚ A (X ^ 2)) = 0 :=
  differential_class_zero (X ^ 2)

/-- The cyclic class of the tensor `X ⊗ Y` maps to `[X dY]`. -/
example : cyclicHomologyOneLinearEquiv ℚ A hcXY =
    kaehlerClass ℚ A (X • KaehlerDifferential.D ℚ A Y) :=
  cyclicHomologyOneLinearEquiv_class_tprod ℚ A X (fun _ : Fin 1 => Y)

/-- The class of `X ⊗ Y` in degree-one cyclic homology is nonzero. -/
example : hcXY ≠ 0 := by
  intro h
  have he := cyclicHomologyOneLinearEquiv_class_tprod ℚ A X (fun _ : Fin 1 => Y)
  have hz : cyclicHomologyOneLinearEquiv ℚ A hcXY = 0 :=
    (congrArg (cyclicHomologyOneLinearEquiv ℚ A) h).trans (map_zero _)
  exact xy_form_class_ne_zero (he.symm.trans hz)

/-- The cyclic class of `1 ⊗ X²` vanishes because its image is exact. -/
example : (cyclicOneClass ℚ A).hom
    ((1 : A) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ (fun _ : Fin 1 => X ^ 2)) = 0 := by
  apply (cyclicHomologyOneLinearEquiv ℚ A).injective
  have h := cyclicHomologyOneLinearEquiv_class_tprod
    ℚ A (1 : A) (fun _ : Fin 1 => X ^ 2)
  simpa only [one_smul, differential_class_zero, map_zero] using h

/-- The signed polynomial Koszul-to-Bar representative is the literal tensor `X ⊗ Y`. -/
example : polynomialSignedRepresentative ℚ (Fin 2) A 1 freeXY = rawXY := signed_xy

/-- The tensor `X ⊗ Y` satisfies the degree-one Hochschild cycle equation. -/
example : (HH.sc 1).g.hom rawXY = 0 := raw_xy_cycle

/-- The class constructed through the polynomial resolution is the class of that tensor cycle. -/
example : hhXY = HomologicalComplex.moduleCatCycleClass HH 1 rawXY raw_xy_cycle := by
  simpa only [signed_xy] using
    polynomialAntisymmetricExteriorClass_eq_cycle ℚ (Fin 2) A 1 freeXY

/-- The polynomial HKR homology map sends the class of `X ⊗ Y` to the coefficient form `X dY`. -/
example : (((polynomialDifferentialFormHomologyIso ℚ (Fin 2) A 1).hom).hom hhXY).down =
    formXY := hkr_xy

/-- The `dY` coordinate of that HKR image is the polynomial `X`. -/
example : KaehlerDifferential.mvPolynomialCoefficientFormCoordinate ℚ (Fin 2) A 1 yColumn
    ((((polynomialDifferentialFormHomologyIso ℚ (Fin 2) A 1).hom).hom hhXY).down) = X :=
  (congrArg (KaehlerDifferential.mvPolynomialCoefficientFormCoordinate
    ℚ (Fin 2) A 1 yColumn) hkr_xy).trans form_xy_coordinate

/-- The same tensor cycle has a nonzero class in Hochschild homology. -/
example : hhXY ≠ 0 := by
  intro h
  have hz : (((polynomialDifferentialFormHomologyIso ℚ (Fin 2) A 1).hom).hom hhXY).down = 0 :=
    (polynomialDifferentialFormHomologyIso_hom_down ℚ (Fin 2) A 1 hhXY).trans
      ((congrArg (symmetricHochschildDifferentialFormEquiv ℚ (Fin 2) A 1) h).trans
        (map_zero _))
  have hf : formXY = 0 := hkr_xy.symm.trans hz
  have hX : X = 0 := form_xy_coordinate.symm.trans
    ((congrArg (KaehlerDifferential.mvPolynomialCoefficientFormCoordinate
      ℚ (Fin 2) A 1 yColumn) hf).trans (map_zero _))
  exact MvPolynomial.X_ne_zero (0 : Fin 2) hX

/-- The enveloping-algebra derived comparison carries the nonzero class of `X ⊗ Y`
to a nonzero degree-one derived tensor class. -/
example :
    letI := Symmetric.opModule A A
    letI := Symmetric.actionsComm A A
    letI := Symmetric.kOpComm ℚ A A
    letI := Symmetric.kOpTower ℚ A A
    ((AdjacentBar.coefficientHochschildHomologyIsoDerived ℚ A A 1).hom).hom hhXY ≠ 0 := by
  letI := Symmetric.opModule A A
  letI := Symmetric.actionsComm A A
  letI := Symmetric.kOpComm ℚ A A
  letI := Symmetric.kOpTower ℚ A A
  let e := AdjacentBar.coefficientHochschildHomologyIsoDerived ℚ A A 1
  intro hz
  have hxy : hhXY = 0 := e.toLinearEquiv.injective
    (hz.trans (map_zero e.hom.hom).symm)
  have hzForm : (((polynomialDifferentialFormHomologyIso ℚ (Fin 2) A 1).hom).hom hhXY).down = 0 :=
    (polynomialDifferentialFormHomologyIso_hom_down ℚ (Fin 2) A 1 hhXY).trans
      ((congrArg (symmetricHochschildDifferentialFormEquiv ℚ (Fin 2) A 1) hxy).trans
        (map_zero _))
  have hf : formXY = 0 := hkr_xy.symm.trans hzForm
  have hX : X = 0 := form_xy_coordinate.symm.trans
    ((congrArg (KaehlerDifferential.mvPolynomialCoefficientFormCoordinate
      ℚ (Fin 2) A 1 yColumn) hf).trans (map_zero _))
  exact MvPolynomial.X_ne_zero (0 : Fin 2) hX

/-- The oriented `dX ∧ dY` coordinate is one. -/
example : KaehlerDifferential.mvPolynomialFormCoordinate ℚ (Fin 2) 2 bothColumns
    basisTwo = 1 := basis_two_coordinate

/-- The two-variable differential wedge is nonzero. -/
example : basisTwo ≠ 0 := by
  intro h
  have hOne : (1 : A) = 0 := basis_two_coordinate.symm.trans
    ((congrArg (KaehlerDifferential.mvPolynomialFormCoordinate ℚ (Fin 2) 2 bothColumns) h).trans
      (map_zero _))
  exact one_ne_zero hOne

/-- The form `d(X²+Y) ∧ d(XY)` has Jacobian coordinate `2X²-Y`. -/
example : KaehlerDifferential.mvPolynomialFormCoordinate ℚ (Fin 2) 2 bothColumns
    (exteriorPower.ιMulti A 2 (fun i => KaehlerDifferential.D ℚ A (jacobianWord i))) =
      2 * X ^ 2 - Y := by
  rw [KaehlerDifferential.mvPolynomialFormCoordinate_differentials]
  simp [bothColumns_selector, jacobianWord, Matrix.det_fin_two,
    MvPolynomial.pderiv_pow, MvPolynomial.pderiv_mul, X, Y] <;> ring

end PolynomialCyclicDifferentialFormsTests
