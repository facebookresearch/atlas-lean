/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.StandardSimplexPolynomialCotangent
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.Data.ZMod.Basic

/-!
# Polynomial simplex comparison with nonzero torsion coefficients

The integer polynomial algebra has a universe-one lifted singleton variable.
Its variable-wise standard one-simplex resolution compares to the canonical
polynomial resolution, carrying the specified generator to a nonzero element.
The target prism has different faces on the formal generator indexed by zero,
and the source cotangent model has a nonzero variable-differential homology class.

The coefficient module is `ℤ/4ℤ` in universe zero, with the polynomial variable
acting by zero. Its unit is nonzero and has four-torsion, and the coefficient
model homotopy equivalence applies to this module.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial TensorProduct

namespace CommAlgCat.StandardSimplexPolynomialCotangentTest

open StandardSimplexPolynomialCotangent

universe u v

private theorem prism_zero_apply {k : Type u} [CommRing k] {A : CommAlgCat.{max u v} k}
    {X Y : SimplicialObject (Over A)} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) (x : (X.obj (op ⦋0⦌)).left) :
    (SimplicialObject.δ Y (0 : Fin 2)).left.hom ((H.h (0 : Fin 1)).left.hom x) =
      (g.app (op ⦋0⦌)).left.hom x := by
  have h := congrArg (fun z : X.obj (op ⦋0⦌) ⟶ Y.obj (op ⦋0⦌) => z.left.hom x)
    (H.h_zero_comp_δ_zero 0)
  exact h

private theorem prism_last_apply {k : Type u} [CommRing k] {A : CommAlgCat.{max u v} k}
    {X Y : SimplicialObject (Over A)} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) (x : (X.obj (op ⦋0⦌)).left) :
    (SimplicialObject.δ Y (1 : Fin 2)).left.hom ((H.h (0 : Fin 1)).left.hom x) =
      (f.app (op ⦋0⦌)).left.hom x := by
  have h := congrArg (fun z : X.obj (op ⦋0⦌) ⟶ Y.obj (op ⦋0⦌) => z.left.hom x)
    (H.h_last_comp_δ_last 0)
  exact h

private theorem composed_zero {k : Type u} [CommRing k] {A : CommAlgCat.{max u v} k}
    {X Y Z W : Over A} (f : X ⟶ Y) (g : Y ⟶ Z) (s : Z ⟶ W) (x : X.left)
    (h : f.left.hom x = 0) : (f ≫ g ≫ s).left.hom x = 0 := by
  change s.left.hom (g.left.hom (f.left.hom x)) = 0
  rw [h, map_zero, map_zero]

/--
The singleton variable type lifted to universe one.
-/
abbrev V := ULift.{1} Unit
/--
The distinguished element of the lifted singleton variable type.
-/
def «variable» : V := ULift.up ()
/--
The integer polynomial algebra on the lifted singleton variable type.
-/
abbrev A := StandardSimplexPolynomialCotangent.algebra ℤ V
/--
The source augmented polynomial model built variable-wise from the standard
one-simplex.
-/
abbrev P := sourceResolution ℤ V 1
/--
The canonical augmented polynomial model of the fixture algebra.
-/
abbrev Q := canonicalResolution ℤ V
/--
The polynomial indeterminate associated to the chosen lifted variable.
-/
def originalVariable : A := MvPolynomial.X «variable»
/--
The degree-zero generator of the variable-wise standard one-simplex source
associated to the chosen variable.
-/
def originalGenerator : P.left.obj (op ⦋0⦌) := sourceGenerator ℤ V 1 «variable»

/--
The specified polynomial indeterminate is nonzero.
-/
theorem originalVariable_ne_zero : originalVariable ≠ 0 := MvPolynomial.X_ne_zero _

/--
The degree-zero algebra comparison sends the specified source generator to
a nonzero element.
-/
theorem forward_originalGenerator_ne_zero :
    ((algebraForward ℤ V 1).left.app (op ⦋0⦌)).hom originalGenerator ≠ 0 := by
  intro h
  have hh := congrArg (fun f => f.hom originalGenerator)
    (NatTrans.congr_app (algebraForward ℤ V 1).w (op ⦋0⦌))
  change (Q.hom.app (op ⦋0⦌)).hom
    (((algebraForward ℤ V 1).left.app (op ⦋0⦌)).hom originalGenerator) =
      (P.hom.app (op ⦋0⦌)).hom originalGenerator at hh
  rw [h, map_zero] at hh
  have hg := sourceGenerator_augmentation ℤ V 1 «variable»
  change (P.hom.app (op ⦋0⦌)).hom originalGenerator = originalVariable at hg
  rw [hg] at hh
  exact originalVariable_ne_zero hh.symm

/--
The canonical target's degree-zero polynomial indeterminate indexed by the
zero element of the fixture algebra.
-/
def ghostVariable : Q.left.obj (op ⦋0⦌) := MvPolynomial.X (0 : A)
/--
The formal target indeterminate indexed by zero is nonzero.
-/
theorem ghostVariable_ne_zero : ghostVariable ≠ 0 := MvPolynomial.X_ne_zero _

private theorem backward_ghost_zero :
    ((overBackward ℤ V 1).app (op ⦋0⦌)).left.hom ghostVariable = 0 := by
  let ε := ((polynomialResolution ℤ A).overPoint (targetPointMap ℤ V)).hom.app (op ⦋0⦌)
  let q := (pointIso ℤ V 1).inv.app (op ⦋0⦌)
  let s := (sourceOverExtra ℤ V 1).section_.app (op ⦋0⦌)
  have hε : ε.left.hom ghostVariable = 0 := by
    change ((polynomialResolution ℤ A).hom.app (op ⦋0⦌)).hom
      (polynomialResolutionGenerator ℤ A 0 (0 : A)) = 0
    exact polynomialResolution_augmentation_zero_generator.{0, 1} ℤ A (0 : A)
  change (ε ≫ q ≫ s).left.hom ghostVariable = 0
  exact composed_zero ε q s ghostVariable hε

/--
The zero face of the target prism image of the formal zero-index generator
is zero.
-/
theorem target_prism_zero_face :
    (Q.left.δ (0 : Fin 2)).hom
      (((targetPrism ℤ V 1).h (0 : Fin 1)).left.hom ghostVariable) = 0 := by
  have h := prism_zero_apply.{0, 1} (targetPrism ℤ V 1) ghostVariable
  change _ = ((overForward ℤ V 1).app (op ⦋0⦌)).left.hom
    (((overBackward ℤ V 1).app (op ⦋0⦌)).left.hom ghostVariable) at h
  exact h.trans ((congrArg ((overForward ℤ V 1).app (op ⦋0⦌)).left.hom
    backward_ghost_zero).trans (map_zero _))

/--
The one face of the target prism image is the original formal zero-index generator.
-/
theorem target_prism_one_face :
    (Q.left.δ (1 : Fin 2)).hom
      (((targetPrism ℤ V 1).h (0 : Fin 1)).left.hom ghostVariable) = ghostVariable :=
  prism_last_apply.{0, 1} (targetPrism ℤ V 1) ghostVariable

/--
The target prism image of the formal zero-index generator is nonzero.
-/
theorem target_prism_nonzero :
    ((targetPrism ℤ V 1).h (0 : Fin 1)).left.hom ghostVariable ≠ 0 := by
  intro h
  have hh := prism_last_apply.{0, 1} (targetPrism ℤ V 1) ghostVariable
  let δ := (SimplicialObject.δ (Over.lift Q.left Q.hom) (1 : Fin 2)).left
  change δ.hom (((targetPrism ℤ V 1).h (0 : Fin 1)).left.hom ghostVariable) = ghostVariable at hh
  have hz : δ.hom (((targetPrism ℤ V 1).h (0 : Fin 1)).left.hom ghostVariable) = 0 :=
    (congrArg δ.hom h).trans (map_zero δ.hom)
  exact ghostVariable_ne_zero (hh.symm.trans hz)

/--
The Kähler differential over `ℤ` of the fixture polynomial indeterminate
is nonzero.
-/
theorem originalDifferential_ne_zero : KaehlerDifferential.D ℤ A originalVariable ≠ 0 := by
  change KaehlerDifferential.D ℤ (MvPolynomial V ℤ) (MvPolynomial.X «variable») ≠ 0
  intro h
  let E := KaehlerDifferential.mvPolynomialBasis ℤ V
  have hh := congrArg (fun ω => E.repr ω «variable») h
  have hv : E.repr (KaehlerDifferential.D ℤ (MvPolynomial V ℤ)
      (MvPolynomial.X «variable»)) «variable» = (1 : MvPolynomial V ℤ) :=
    (congrArg (fun x : V →₀ MvPolynomial V ℤ => x «variable»)
      (KaehlerDifferential.mvPolynomialBasis_repr_D_X ℤ V «variable»)).trans
        Finsupp.single_eq_same
  have hz : E.repr (0 : KaehlerDifferential ℤ (MvPolynomial V ℤ)) «variable» = 0 :=
    (congrArg (fun x : V →₀ MvPolynomial V ℤ => x «variable»)
      (map_zero E.repr)).trans Finsupp.zero_apply
  exact one_ne_zero (hv.symm.trans (hh.trans hz))

/--
The isomorphism from degree-zero homology of the source normalized cotangent
model to the Kähler differential module of the fixture algebra.
-/
def actualHomologyZeroIso :
    (((normalizedMooreComplex (ModuleCat.{1} A)).obj (cotangentSimplicial ℤ A P)).homology 0) ≅
      ModuleCat.of A (KaehlerDifferential ℤ A) :=
  ((cotangentHomotopyEquiv ℤ V 1).trans
    (polynomialCotangentHomotopyEquivKaehler ℤ A V (Iso.refl _))).toHomologyIso 0 ≪≫
      HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0
        (ModuleCat.of A (KaehlerDifferential ℤ A))

/--
The degree-zero source cotangent homology class corresponding to the variable
differential.
-/
def actualHomologyZeroClass := actualHomologyZeroIso.inv.hom (KaehlerDifferential.D ℤ A originalVariable)

/--
The source homology class corresponding to the variable differential is nonzero.
-/
theorem actualHomologyZeroClass_ne_zero : actualHomologyZeroClass ≠ 0 := by
  intro h
  have hh := congrArg (fun f => f.hom (KaehlerDifferential.D ℤ A originalVariable)) actualHomologyZeroIso.inv_hom_id
  change actualHomologyZeroIso.hom.hom actualHomologyZeroClass = KaehlerDifferential.D ℤ A originalVariable at hh
  rw [h, map_zero] at hh
  exact originalDifferential_ne_zero hh.symm

/--
The universe-zero module `ℤ/4ℤ` over the polynomial algebra, with integer
reduction modulo four and every polynomial variable evaluated at zero.
-/
def torsionCoefficients : ModuleCat.{0} A := by
  let φ : A →+* ZMod 4 := MvPolynomial.eval₂Hom (Int.castRingHom (ZMod 4)) (fun _ => 0)
  letI : Module A (ZMod 4) := Module.compHom (ZMod 4) φ
  exact ModuleCat.of A (ZMod 4)

/--
The coefficient element `1 : ℤ/4ℤ`.
-/
def coefficientOne : torsionCoefficients := (1 : ZMod 4)

/--
The unit of the coefficient module `ℤ/4ℤ` is nonzero.
-/
theorem coefficientOne_ne_zero : coefficientOne ≠ 0 := by
  change (1 : ZMod 4) ≠ 0
  decide

/--
Four times the coefficient unit is zero.
-/
theorem coefficientOne_four_torsion : (4 : ℕ) • coefficientOne = 0 := by
  change (4 : ℕ) • (1 : ZMod 4) = 0
  decide

/--
The standard-simplex polynomial cotangent model comparison with the specified
universe-zero modulo-four coefficient module.
-/
def actualCoefficientEquivalence := coefficientHomotopyEquiv ℤ V 1 torsionCoefficients

end CommAlgCat.StandardSimplexPolynomialCotangentTest

end
