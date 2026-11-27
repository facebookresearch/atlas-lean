/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialCotangentPrism
public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialSplitting
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.Tactic.NormNum

/-!
# Nonzero polynomial cotangent contraction coordinates

The ground ring is `ℤ` in universe zero and the polynomial variable type is
a universe-one lift of a singleton. The canonical algebra prism has zero
and nonzero faces on the formal generator indexed by zero. The cotangent
augmentation takes the specified differential tensor to the nonzero differential
of the polynomial variable; its degree-zero homology class is nonzero and
positive cotangent homology vanishes.

A free simplicial algebra on the constant singleton set also carries a compatible
polynomial splitting. Doubling its generator gives a nonzero value and the
stated degree-zero degeneracy identity.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial TensorProduct

namespace CommAlgCat.PolynomialCotangentContractionTest

/--
The singleton variable type lifted to universe one.
-/
abbrev V := ULift.{1} Unit
/--
The integer polynomial algebra on the lifted singleton variable type.
-/
abbrev A : CommAlgCat.{1} ℤ := CommAlgCat.of ℤ (MvPolynomial V ℤ)
/--
The specified identity polynomial presentation of the algebra `A`.
-/
def coordinates : A ≅ CommAlgCat.of ℤ (MvPolynomial V ℤ) := Iso.refl _
/--
The sole element of the lifted singleton variable type.
-/
def polynomialVariable : V := ULift.up ()
/--
The polynomial indeterminate associated to the chosen lifted variable.
-/
def originalVariable : A := MvPolynomial.X polynomialVariable
/--
The degree-zero polynomial-resolution indeterminate indexed by the zero element
of `A`.
-/
def zeroVariable : (polynomialResolution ℤ A).left.obj (op ⦋0⦌) := MvPolynomial.X (0 : A)

/--
The formal resolution indeterminate indexed by zero is a nonzero polynomial.
-/
theorem zeroVariable_ne_zero : zeroVariable ≠ 0 := MvPolynomial.X_ne_zero _

/--
The algebra prism determined by the polynomial presentation of `A`.
-/
def actualPrism := polynomialResolutionPrismOfPresentation ℤ V A coordinates

/--
The zero face of the prism image of the zero-indexed formal generator is zero.
-/
theorem actualPrism_zero_face :
    ((polynomialResolution ℤ A).left.δ (0 : Fin 2)).hom
      ((actualPrism.h (0 : Fin 1)).hom zeroVariable) = 0 := by
  let a := (polynomialResolution ℤ A).hom.app (op ⦋0⦌)
  let s := (polynomialResolutionSectionOfPresentation ℤ V A coordinates).app (op ⦋0⦌)
  have hface : ((polynomialResolution ℤ A).left.δ (0 : Fin 2)).hom
      ((actualPrism.h (0 : Fin 1)).hom zeroVariable) = s.hom (a.hom zeroVariable) :=
    congrArg (fun f => f.hom zeroVariable) (actualPrism.h_zero_comp_δ_zero 0)
  have haugmentation : a.hom zeroVariable = 0 := by
    exact polynomialResolution_augmentation_zero_generator.{0, 1} ℤ A (0 : A)
  exact hface.trans ((congrArg s.hom haugmentation).trans s.hom.map_zero)

/--
The one face of that prism image is the original zero-indexed formal generator.
-/
theorem actualPrism_one_face :
    ((polynomialResolution ℤ A).left.δ (1 : Fin 2)).hom
      ((actualPrism.h (0 : Fin 1)).hom zeroVariable) = zeroVariable :=
  congrArg (fun f => f.hom zeroVariable) (actualPrism.h_last_comp_δ_last 0)

/--
The prism image of the zero-indexed formal generator is nonzero.
-/
theorem actualPrism_nonzero : (actualPrism.h (0 : Fin 1)).hom zeroVariable ≠ 0 := by
  intro h
  have hface := actualPrism_one_face
  rw [h, map_zero] at hface
  exact zeroVariable_ne_zero hface.symm

/--
The Kähler differential over `ℤ` of the fixture polynomial variable is nonzero.
-/
theorem originalDifferential_ne_zero : KaehlerDifferential.D ℤ A originalVariable ≠ 0 := by
  intro h
  have hh := congrArg (fun ω => (KaehlerDifferential.mvPolynomialBasis ℤ V).repr ω polynomialVariable) h
  simpa only [originalVariable, KaehlerDifferential.mvPolynomialBasis_repr_D_X,
    Finsupp.single_eq_same, map_zero, Finsupp.zero_apply, one_ne_zero] using hh

/--
The degree-zero cotangent tensor with coefficient one and differential of the
resolution generator associated to the fixture polynomial variable.
-/
def actualCotangentTensor : (polynomialCotangentAugmented ℤ A (Over.mk (𝟙 A))).left.obj (op ⦋0⦌) :=
  cotangentTensor ℤ A (Over.mk ((polynomialResolution ℤ A).hom.app (op ⦋0⦌))) 1
    (polynomialResolutionGenerator ℤ A 0 originalVariable)

/--
The cotangent augmentation and terminal-module identification send the specified
tensor to the Kähler differential of the fixture polynomial variable.
-/
theorem actualCotangentTensor_value :
    (cotangentTerminalIso ℤ A).hom.hom
      (((polynomialCotangentAugmented ℤ A (Over.mk (𝟙 A))).hom.app (op ⦋0⦌)).hom actualCotangentTensor) =
      KaehlerDifferential.D ℤ A originalVariable := by
  change ((cotangentKaehlerAugmentation ℤ A).app (op ⦋0⦌)).hom actualCotangentTensor = _
  have h := cotangentKaehlerAugmentation_tensor ℤ A 0 1
    (polynomialResolutionGenerator ℤ A 0 originalVariable)
  change ((cotangentKaehlerAugmentation ℤ A).app (op ⦋0⦌)).hom actualCotangentTensor =
    (1 : A) • KaehlerDifferential.D ℤ A
      (((polynomialResolution ℤ A).hom.app (op ⦋0⦌)).hom
        (polynomialResolutionGenerator ℤ A 0 originalVariable)) at h
  have haugmentation : ((polynomialResolution ℤ A).hom.app (op ⦋0⦌)).hom
      (polynomialResolutionGenerator ℤ A 0 originalVariable) = originalVariable := by
    exact polynomialResolution_augmentation_zero_generator.{0, 1} ℤ A originalVariable
  exact h.trans ((congrArg (fun a : A => (1 : A) • KaehlerDifferential.D ℤ A a) haugmentation).trans
    (one_smul A (KaehlerDifferential.D ℤ A originalVariable)))

/--
The specified degree-zero cotangent tensor is nonzero.
-/
theorem actualCotangentTensor_ne_zero : actualCotangentTensor ≠ 0 := by
  intro h
  have hh := actualCotangentTensor_value
  let C : ModuleCat.{1} A := (polynomialCotangentAugmented.{0, 1} ℤ A (Over.mk (𝟙 A))).left.obj (op ⦋0⦌)
  let T : ModuleCat.{1} A := (polynomialCotangentAugmented.{0, 1} ℤ A (Over.mk (𝟙 A))).right
  let q : C ⟶ T := (polynomialCotangentAugmented.{0, 1} ℤ A (Over.mk (𝟙 A))).hom.app (op ⦋0⦌)
  let E := cotangentTerminalIso.{0, 1} ℤ A
  have hq0 : q.hom (0 : C) = 0 := q.hom.map_zero
  have hzero : E.hom.hom (q.hom (0 : C)) = 0 :=
    (congrArg E.hom.hom hq0).trans E.hom.hom.map_zero
  have hvalue : E.hom.hom (q.hom actualCotangentTensor) = 0 :=
    (congrArg (fun x : C => E.hom.hom (q.hom x)) h).trans hzero
  exact originalDifferential_ne_zero (hh.symm.trans hvalue)

/--
The cotangent prism obtained from the polynomial presentation of `A`.
-/
def actualCotangentPrism := polynomialCotangentPrismOfPresentation ℤ V A coordinates

/--
The degree-zero cotangent prism sends the specified cotangent tensor to a
nonzero element.
-/
theorem actualCotangentPrism_nonzero :
    (actualCotangentPrism.h (0 : Fin 1)).hom actualCotangentTensor ≠ 0 := by
  intro h
  let P := (polynomialCotangentSimplicialFunctor.{0, 1} ℤ A).obj (Over.mk (𝟙 A))
  let i : Fin 1 := ⟨0, by decide⟩
  let j : Fin 2 := ⟨1, by decide⟩
  let d : P.obj (op ⦋1⦌) ⟶ P.obj (op ⦋0⦌) := P.δ j
  have hi : Fin.last 0 = i := Fin.ext rfl
  have hj : Fin.last (0 + 1) = j := Fin.ext rfl
  have hEnd : actualCotangentPrism.h i ≫ d = 𝟙 (P.obj (op ⦋0⦌)) := by
    have hh := actualCotangentPrism.h_last_comp_δ_last 0
    rw [hi, hj] at hh
    exact hh
  have hValue : d.hom ((actualCotangentPrism.h i).hom actualCotangentTensor) = actualCotangentTensor :=
    (congrArg (fun f => f.hom actualCotangentTensor) hEnd).trans (ModuleCat.id_apply _ _)
  have hz : d.hom ((actualCotangentPrism.h i).hom actualCotangentTensor) = 0 :=
    (congrArg d.hom h).trans d.hom.map_zero
  exact actualCotangentTensor_ne_zero (hValue.symm.trans hz)

/--
The constant-diagram prism comparison followed by the constant normalization
map is the canonical polynomial cotangent normalized augmentation.
-/
theorem actualNormalizedPrism_recoversCanonicalAugmentation :
    (polynomialCotangentPrismConstantHomotopyEquiv ℤ V A coordinates).hom ≫
      (cotangentWeightZeroCoefficientHomotopyEquiv ℤ A (cotangent ℤ A (Over.mk (𝟙 A)))).hom =
        polynomialCotangentNormalizedAugmentation ℤ A (Over.mk (𝟙 A)) :=
  polynomialCotangentPrismConstantHomotopyEquiv_augmentation ℤ V A coordinates

/--
The isomorphism from degree-zero cotangent homology of `A` to its Kähler
differential module over `ℤ`.
-/
def actualHomologyZeroIso : (cotangentComplex ℤ A).homology 0 ≅
    ModuleCat.of A (KaehlerDifferential ℤ A) :=
  (polynomialCotangentHomotopyEquivKaehler ℤ A V coordinates.symm).toHomologyIso 0 ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0
      (ModuleCat.of A (KaehlerDifferential ℤ A))

/--
The degree-zero cotangent homology element corresponding to the differential
of the fixture polynomial variable.
-/
def actualHomologyZeroClass : (cotangentComplex ℤ A).homology 0 :=
  actualHomologyZeroIso.inv.hom
    (KaehlerDifferential.D ℤ A originalVariable)

/--
The degree-zero homology class corresponding to the variable differential
is nonzero.
-/
theorem actualHomologyZeroClass_ne_zero : actualHomologyZeroClass ≠ 0 := by
  intro h
  let E := actualHomologyZeroIso
  have hh := congrArg (fun f => f.hom (KaehlerDifferential.D ℤ A originalVariable)) E.inv_hom_id
  change E.hom.hom actualHomologyZeroClass = KaehlerDifferential.D ℤ A originalVariable at hh
  rw [h, map_zero] at hh
  exact originalDifferential_ne_zero hh.symm

/--
The cotangent complex of the polynomial fixture has zero homology in every
positive degree.
-/
theorem actualPositiveHomology_isZero (n : ℕ) :
    IsZero ((cotangentComplex ℤ A).homology (n + 1)) := by
  have hz : IsZero (((ChainComplex.single₀ (ModuleCat.{1} A)).obj
      (ModuleCat.of A (KaehlerDifferential ℤ A))).homology (n + 1)) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact ChainComplex.exactAt_succ_single_obj _ n
  exact hz.of_iso ((polynomialCotangentHomotopyEquivKaehler ℤ A V coordinates.symm).toHomologyIso (n + 1))

/--
The constant simplicial set on the universe-one lifted singleton.
-/
def S : SSet.{1} := (SimplicialObject.const (Type 1)).obj V
/--
The simplicial algebra obtained by applying the free integer polynomial algebra
functor to the constant lifted singleton simplicial set.
-/
def freeSimplicial : SimplicialObject (CommAlgCat.{1} ℤ) := S ⋙ CommAlgCat.free.{0, 1} ℤ
/--
The compatible polynomial splitting induced by the underlying constant
simplicial set.
-/
def compatibleGenerators : PolynomialSplitting.{0, 1} ℤ freeSimplicial := polynomialSplittingOfSSet.{0, 1} ℤ S
/--
The prescription taking each compatible polynomial generator to twice its
polynomial indeterminate.
-/
def scaledGenerators (n : ℕ) (x : compatibleGenerators.variables n) : freeSimplicial.obj (op ⦋n⦌) :=
  2 * MvPolynomial.X x.val
/--
The chosen lifted variable regarded as a nondegenerate zero-simplex of the
constant simplicial set.
-/
def nondegenerateVariable : S.nonDegenerate 0 :=
  ⟨polynomialVariable, by
    rw [SSet.nonDegenerate_zero]
    exact Set.mem_univ _⟩

/--
The prescribed degree-zero polynomial map sends the chosen indeterminate
to twice that indeterminate.
-/
theorem scaled_zero_value :
    (PolynomialSplitting.degreeMap compatibleGenerators scaledGenerators (op ⦋0⦌)).hom
        (MvPolynomial.X polynomialVariable) =
      2 * MvPolynomial.X polynomialVariable := by
  let F : freeSimplicial.obj (op ⦋0⦌) →ₐ[ℤ] freeSimplicial.obj (op ⦋0⦌) :=
    (PolynomialSplitting.degreeMap compatibleGenerators scaledGenerators (op ⦋0⦌)).hom
  have h := congrArg (fun f => f.hom (MvPolynomial.X nondegenerateVariable))
    (PolynomialSplitting.distinguished_degreeMap compatibleGenerators scaledGenerators 0)
  have hRestriction : F (MvPolynomial.X polynomialVariable) =
      MvPolynomial.aeval (scaledGenerators 0)
        (MvPolynomial.X nondegenerateVariable : MvPolynomial (S.nonDegenerate 0) ℤ) := by
    have hx : MvPolynomial.rename (R := ℤ) (fun x : S.nonDegenerate 0 => x.val)
        (MvPolynomial.X nondegenerateVariable) = MvPolynomial.X polynomialVariable :=
      MvPolynomial.rename_X _ nondegenerateVariable
    have hNative : F (MvPolynomial.rename (R := ℤ) (fun x : S.nonDegenerate 0 => x.val)
        (MvPolynomial.X nondegenerateVariable)) =
        MvPolynomial.aeval (scaledGenerators 0)
        (MvPolynomial.X nondegenerateVariable : MvPolynomial (S.nonDegenerate 0) ℤ) := h
    exact (congrArg F hx).symm.trans hNative
  have hEval : MvPolynomial.aeval (scaledGenerators 0)
        (MvPolynomial.X nondegenerateVariable : MvPolynomial (S.nonDegenerate 0) ℤ) =
      scaledGenerators 0 nondegenerateVariable := MvPolynomial.aeval_X (scaledGenerators 0) nondegenerateVariable
  exact hRestriction.trans hEval

/--
The value of the prescribed degree-zero map on the chosen indeterminate
is nonzero.
-/
theorem scaled_zero_nonzero :
    (PolynomialSplitting.degreeMap compatibleGenerators scaledGenerators (op ⦋0⦌)).hom
        (MvPolynomial.X polynomialVariable) ≠ 0 := by
  rw [scaled_zero_value]
  intro h
  let E : MvPolynomial V ℤ →+* ℤ := MvPolynomial.eval (fun _ : V => (1 : ℤ))
  have hh := congrArg E h
  have hX : E (MvPolynomial.X polynomialVariable) = 1 := MvPolynomial.eval_X polynomialVariable
  have hTwoConstant : E (2 : MvPolynomial V ℤ) = (2 : ℤ) := map_ofNat E 2
  have hTwo : E (2 * MvPolynomial.X polynomialVariable) = (2 : ℤ) :=
    (E.map_mul _ _).trans ((congrArg₂ (fun a b : ℤ => a * b) hTwoConstant hX).trans (mul_one 2))
  have hZero : (2 : ℤ) = 0 := hTwo.symm.trans (hh.trans E.map_zero)
  exact (by decide : (2 : ℤ) ≠ 0) hZero

/--
The degree-zero and degree-one prescribed polynomial maps commute with
the source degeneracy from degree zero to degree one.
-/
theorem scaled_original_degeneracy :
    freeSimplicial.σ (0 : Fin 1) ≫ PolynomialSplitting.degreeMap compatibleGenerators scaledGenerators (op ⦋1⦌) =
      PolynomialSplitting.degreeMap compatibleGenerators scaledGenerators (op ⦋0⦌) ≫ freeSimplicial.σ (0 : Fin 1) :=
  PolynomialSplitting.degreeMap_epi_naturality compatibleGenerators scaledGenerators
    (SimplexCategory.σ (0 : Fin 1)).op

end CommAlgCat.PolynomialCotangentContractionTest

end
