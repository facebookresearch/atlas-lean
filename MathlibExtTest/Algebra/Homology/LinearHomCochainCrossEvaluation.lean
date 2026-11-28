/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Homology.LinearHomCochainCrossEvaluation
public import MathlibExt.Algebra.Homology.LinearHomCochainHomologyComparisonModuleCat
public import MathlibExt.Algebra.Homology.CochainGradedPairingHomologyLaws
public import MathlibExt.Algebra.Homology.ChainGradedPairingHomology
import Mathlib.Algebra.Homology.SingleHomology

/-!
# Concrete values of external Hom cross-evaluation

Single complexes over the integers in odd degrees one and three give an independent
representative calculation of the external evaluation value nine. Exchanging factors gives
four, and inserting an extra Koszul sign gives negative nine. Generic comparison and
homotopy formulas retain the actual chain, coefficient, cycle and cohomology maps.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace HomologicalComplex

variable (R : Type u) [CommRing R]

/-- The monoidal structure on chain complexes of `R`-modules. -/
noncomputable local instance crossEvaluationTestMonoidalCategory :
    MonoidalCategory (ChainComplex (ModuleCat.{u} R) ℕ) :=
  HomologicalComplex.monoidalCategory
    (ModuleCat.{u} R) (ComplexShape.down ℕ)

/-- Endpoint consistency: specialising the homotopy cross-evaluation theorem
to identity cross and coproduct maps recovers the tensor evaluation theorem.
This pins the relative orientation of the two endpoints — the external
cohomology product sits in the left tensor factor and the homology cross
product in the right factor, both before the factor evaluations — since the
derivation only typechecks with that placement. -/
example {K₁ K₂ : ChainComplex (ModuleCat.{u} R) ℕ} [K₁.HasTensor K₂]
    (M N L : ModuleCat.{u} R) (mu : M ⊗ N ⟶ L) (p q : ℕ) :
    (((linearHomCochainGradedPairing R
        (𝟙 (tensorObj K₁ K₂)) mu).pairHomology p q) ⊗ₘ
      (ChainGradedPairing.pairHomology
        (𝟙 (tensorObj K₁ K₂))
        (ChainGradedPairing.homologyDescentData
          (𝟙 (tensorObj K₁ K₂))) p q)) ≫
      linearHomCochainEvaluationHomology R (tensorObj K₁ K₂) L (p + q) =
    tensorμ
        (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj
          (op K₁)).homology p)
        (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) N).obj
          (op K₂)).homology q)
        (K₁.homology p) (K₂.homology q) ≫
      (linearHomCochainEvaluationHomology R K₁ M p ⊗ₘ
        linearHomCochainEvaluationHomology R K₂ N q) ≫ mu := by
  have h := linearHomCochainCrossEvaluation_of_homotopy R
    (𝟙 (tensorObj K₁ K₂)) (𝟙 (tensorObj K₁ K₂)) (𝟙 (tensorObj K₁ K₂))
    (_root_.Homotopy.ofEq (by simp)) M N L mu p q
  simpa using h

/-- Degree-zero boundary of the tensor evaluation: at `p = q = 0` the
total degree is `0`, with no hidden successor shift. -/
example {K₁ K₂ : ChainComplex (ModuleCat.{u} R) ℕ} [K₁.HasTensor K₂]
    (M N L : ModuleCat.{u} R) (mu : M ⊗ N ⟶ L) :
    (((linearHomCochainGradedPairing R
        (𝟙 (tensorObj K₁ K₂)) mu).pairHomology 0 0) ⊗ₘ
      (ChainGradedPairing.pairHomology
        (𝟙 (tensorObj K₁ K₂))
        (ChainGradedPairing.homologyDescentData
          (𝟙 (tensorObj K₁ K₂))) 0 0)) ≫
      linearHomCochainEvaluationHomology R (tensorObj K₁ K₂) L 0 =
    tensorμ
        (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj
          (op K₁)).homology 0)
        (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) N).obj
          (op K₂)).homology 0)
        (K₁.homology 0) (K₂.homology 0) ≫
      (linearHomCochainEvaluationHomology R K₁ M 0 ⊗ₘ
        linearHomCochainEvaluationHomology R K₂ N 0) ≫ mu := by
  simpa using linearHomCochainTensorEvaluation R M N L mu 0 0

/-! ## Concrete single-complex numerics over `ℤ`

The two chain complexes are singles with value `ℤ × ℤ` in the unequal odd
degrees `1` and `3` (total degree `4`).  The cocycles are
`(a, b) ↦ a + 2b` and `(a, b) ↦ 3a + b`, the cycles are `(1, 1)` and
`(1, 0)`, and the coefficient pairing is multiplication, so the tensor
evaluation on the pure tensor of the four classes is `3 * 3 = 9`.
Exchanging the factors would give `(1 + 2 * 0) * (3 * 1 + 1) = 4`, and a
spurious Koszul sign `(-1) ^ (1 * 3)` would give `-9`, so the value pins
factor order, total degree, and sign conventions.  The computation goes
through representatives, the comparison's factorisation on cycles, and
the `ModuleCat` uncurry identification, without invoking the tensor
evaluation or cross-evaluation theorems under test. -/

/-- The linear Hom-cochain functor over `ℤ` uses `ModuleCat.instLinear`.
Its comparison and cycle descent use the same linear structure, which may
differ from the `Linear.preadditiveIntLinear` instance selected by synthesis. -/
private abbrev LHFℤ (M : ModuleCat ℤ) :=
  @linearHomCochainComplexFunctor ℤ _ (ModuleCat ℤ) _ _
    ModuleCat.instLinear M

/-- Cycle descent over `ℤ` at the fixed `ModuleCat` linear structure. -/
private abbrev cycleDescℤ :=
  @linearHomCochainCycleDesc ℤ _ (ModuleCat ℤ) _ _
    ModuleCat.instLinear

/-- The cycles comparison over `ℤ` at the fixed `ModuleCat` linear
structure. -/
private abbrev cyclesComparisonℤ :=
  @linearHomCochainCyclesComparison ℤ _ (ModuleCat ℤ) _ _
    ModuleCat.instLinear

private abbrev A2 : ModuleCat ℤ := ModuleCat.of ℤ (ℤ × ℤ)

private abbrev Z1 : ModuleCat ℤ := ModuleCat.of ℤ ℤ

/-- `(a, b) ↦ a + 2b`. -/
private noncomputable def phiLin1 : (ℤ × ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.fst ℤ ℤ ℤ + 2 • LinearMap.snd ℤ ℤ ℤ

/-- `(a, b) ↦ 3a + b`. -/
private noncomputable def phiLin2 : (ℤ × ℤ) →ₗ[ℤ] ℤ :=
  3 • LinearMap.fst ℤ ℤ ℤ + LinearMap.snd ℤ ℤ ℤ

/-- The single chain complex with `ℤ × ℤ` in degree `1`. -/
private abbrev K1 : ChainComplex (ModuleCat ℤ) ℕ :=
  (HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 1).obj A2

/-- The single chain complex with `ℤ × ℤ` in degree `3`. -/
private abbrev K2 : ChainComplex (ModuleCat ℤ) ℕ :=
  (HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 3).obj A2

/-- The degree-`1` cochain given by `phiLin1`. -/
private abbrev phi1 : K1.X 1 ⟶ Z1 :=
  (singleObjXSelf (ComplexShape.down ℕ) 1 A2).hom ≫ ModuleCat.ofHom phiLin1

/-- The degree-`3` cochain given by `phiLin2`. -/
private abbrev psi2 : K2.X 3 ⟶ Z1 :=
  (singleObjXSelf (ComplexShape.down ℕ) 3 A2).hom ≫ ModuleCat.ofHom phiLin2

/-- The degree-`1` chain cycle given by `(1, 1)`. -/
private abbrev x1 : K1.cycles 1 :=
  (singleObjCyclesSelfIso (ComplexShape.down ℕ) 1 A2).inv.hom (1, 1)

/-- The degree-`3` chain cycle given by `(1, 0)`. -/
private abbrev y2 : K2.cycles 3 :=
  (singleObjCyclesSelfIso (ComplexShape.down ℕ) 3 A2).inv.hom (1, 0)

/-- The Hom-cochain complex of `K1` with coefficients `ℤ`. -/
private abbrev D1 : CochainComplex (ModuleCat ℤ) ℕ :=
  (LHFℤ Z1).obj (op K1)

/-- The Hom-cochain complex of `K2` with coefficients `ℤ`. -/
private abbrev D2 : CochainComplex (ModuleCat ℤ) ℕ :=
  (LHFℤ Z1).obj (op K2)

private lemma D1_sc_g : (D1.sc 1).g = 0 := by
  simp only [shortComplexFunctor_obj_g]
  change ((@linearYoneda ℤ _ (ModuleCat ℤ) _ _
    ModuleCat.instLinear).obj Z1).map (K1.d _ _).op = 0
  rw [single_obj_d]
  simp only [op_zero, Functor.map_zero]

private lemma D2_sc_g : (D2.sc 3).g = 0 := by
  simp only [shortComplexFunctor_obj_g]
  change ((@linearYoneda ℤ _ (ModuleCat ℤ) _ _
    ModuleCat.instLinear).obj Z1).map (K2.d _ _).op = 0
  rw [single_obj_d]
  simp only [op_zero, Functor.map_zero]

/-- The cochain cycle corresponding to `phi1`. -/
private noncomputable def z1 : D1.cycles 1 :=
  (@asIso _ _ _ _ (D1.iCycles 1)
    (ShortComplex.isIso_iCycles (D1.sc 1) D1_sc_g)).inv.hom phi1

/-- The cochain cycle corresponding to `psi2`. -/
private noncomputable def z2 : D2.cycles 3 :=
  (@asIso _ _ _ _ (D2.iCycles 3)
    (ShortComplex.isIso_iCycles (D2.sc 3) D2_sc_g)).inv.hom psi2

private lemma iC_z1 : (D1.iCycles 1).hom z1 = phi1 := by
  change (D1.iCycles 1).hom ((@asIso _ _ _ _ (D1.iCycles 1)
    (ShortComplex.isIso_iCycles (D1.sc 1) D1_sc_g)).inv.hom phi1) = phi1
  exact ConcreteCategory.congr_hom
    (@asIso _ _ _ _ (D1.iCycles 1)
      (ShortComplex.isIso_iCycles (D1.sc 1) D1_sc_g)).inv_hom_id phi1

private lemma iC_z2 : (D2.iCycles 3).hom z2 = psi2 := by
  change (D2.iCycles 3).hom ((@asIso _ _ _ _ (D2.iCycles 3)
    (ShortComplex.isIso_iCycles (D2.sc 3) D2_sc_g)).inv.hom psi2) = psi2
  exact ConcreteCategory.congr_hom
    (@asIso _ _ _ _ (D2.iCycles 3)
      (ShortComplex.isIso_iCycles (D2.sc 3) D2_sc_g)).inv_hom_id psi2

private lemma phi1_x1 : phi1.hom ((K1.iCycles 1).hom x1) = 3 := by
  rw [show (K1.iCycles 1).hom x1 =
    (singleObjXSelf (ComplexShape.down ℕ) 1 A2).inv.hom (1, 1) from
    ConcreteCategory.congr_hom
      (singleObjCyclesSelfIso_inv_iCycles (ComplexShape.down ℕ) 1 A2) (1, 1)]
  show ((singleObjXSelf (ComplexShape.down ℕ) 1 A2).hom ≫
      ModuleCat.ofHom phiLin1).hom
    ((singleObjXSelf (ComplexShape.down ℕ) 1 A2).inv.hom (1, 1)) = 3
  rw [ModuleCat.comp_apply]
  rw [show (singleObjXSelf (ComplexShape.down ℕ) 1 A2).hom.hom
      ((singleObjXSelf (ComplexShape.down ℕ) 1 A2).inv.hom (1, 1)) = (1, 1) from
    ConcreteCategory.congr_hom
      (singleObjXSelf (ComplexShape.down ℕ) 1 A2).inv_hom_id (1, 1)]
  rfl

private lemma psi2_y2 : psi2.hom ((K2.iCycles 3).hom y2) = 3 := by
  rw [show (K2.iCycles 3).hom y2 =
    (singleObjXSelf (ComplexShape.down ℕ) 3 A2).inv.hom (1, 0) from
    ConcreteCategory.congr_hom
      (singleObjCyclesSelfIso_inv_iCycles (ComplexShape.down ℕ) 3 A2) (1, 0)]
  show ((singleObjXSelf (ComplexShape.down ℕ) 3 A2).hom ≫
      ModuleCat.ofHom phiLin2).hom
    ((singleObjXSelf (ComplexShape.down ℕ) 3 A2).inv.hom (1, 0)) = 3
  rw [ModuleCat.comp_apply]
  rw [show (singleObjXSelf (ComplexShape.down ℕ) 3 A2).hom.hom
      ((singleObjXSelf (ComplexShape.down ℕ) 3 A2).inv.hom (1, 0)) = (1, 0) from
    ConcreteCategory.congr_hom
      (singleObjXSelf (ComplexShape.down ℕ) 3 A2).inv_hom_id (1, 0)]
  rfl

/-- Multiplication `ℤ ⊗ ℤ ⟶ ℤ`. -/
private abbrev muZ : Z1 ⊗ Z1 ⟶ Z1 := ModuleCat.ofHom (TensorProduct.lid ℤ ℤ)

/-- On pure tensors of representative classes, the tensor evaluation
composite is evaluation on the paired cycle classes. -/
private theorem tensorEvaluation_single_factor :
    ((((linearHomCochainGradedPairing ℤ
        (𝟙 (tensorObj K1 K2)) muZ).pairHomology 1 3) ⊗ₘ
      (ChainGradedPairing.pairHomology
        (𝟙 (tensorObj K1 K2))
        (ChainGradedPairing.homologyDescentData
          (𝟙 (tensorObj K1 K2))) 1 3)) ≫
      linearHomCochainEvaluationHomology ℤ (tensorObj K1 K2) Z1 (1 + 3)).hom
    ((((D1.homologyπ 1).hom z1) ⊗ₜ[ℤ] ((D2.homologyπ 3).hom z2)) ⊗ₜ[ℤ]
      (((K1.homologyπ 1).hom x1) ⊗ₜ[ℤ] ((K2.homologyπ 3).hom y2))) =
  (linearHomCochainEvaluationHomology ℤ (tensorObj K1 K2) Z1 (1 + 3)).hom
    ((((LHFℤ Z1).obj
        (op (tensorObj K1 K2))).homologyπ (1 + 3)).hom
        (((linearHomCochainGradedPairing ℤ (𝟙 (tensorObj K1 K2)) muZ).pairCycles
          1 3).hom (z1 ⊗ₜ[ℤ] z2)) ⊗ₜ[ℤ]
      ((tensorObj K1 K2).homologyπ (1 + 3)).hom
        ((ChainGradedPairing.pairCycles (𝟙 (tensorObj K1 K2))
          (ChainGradedPairing.homologyDescentData (𝟙 (tensorObj K1 K2)))
          1 3).hom (x1 ⊗ₜ[ℤ] y2))) := by
  have hcup := HomologicalComplex.CochainGradedPairing.pairHomology_π_apply ℤ
    (linearHomCochainGradedPairing ℤ (𝟙 (tensorObj K1 K2)) muZ) 1 3 z1 z2
  have hcross := ConcreteCategory.congr_hom
    (ChainGradedPairing.tensor_homologyπ_comp_pairHomology (𝟙 (tensorObj K1 K2))
      (ChainGradedPairing.homologyDescentData (𝟙 (tensorObj K1 K2))) 1 3)
    (x1 ⊗ₜ[ℤ] y2)
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at hcross
  exact congrArg
    (linearHomCochainEvaluationHomology ℤ (tensorObj K1 K2) Z1 (1 + 3)).hom
    (congrArg₂ (TensorProduct.tmul ℤ) hcup hcross)

/-- The comparison on the tensor complex, with internal-hom codomain. -/
private noncomputable abbrev cT :
    (((LHFℤ Z1).obj
        (op (tensorObj K1 K2))).homology (1 + 3)) ⟶
      (ihom ((tensorObj K1 K2).homology (1 + 3))).obj Z1 :=
  linearHomCochainHomologyComparisonModuleCat ℤ (tensorObj K1 K2) Z1 (1 + 3)

/-- Evaluation on the paired cycle classes is `3 * 3 = 9`: the external
cohomology product pairs `phi1` with `x1` and `psi2` with `y2` (not the
other way around), in total degree `1 + 3`, with no extra sign. -/
private theorem tensorEvaluation_single_eval :
    (linearHomCochainEvaluationHomology ℤ (tensorObj K1 K2) Z1 (1 + 3)).hom
    ((((LHFℤ Z1).obj
        (op (tensorObj K1 K2))).homologyπ (1 + 3)).hom
        (((linearHomCochainGradedPairing ℤ (𝟙 (tensorObj K1 K2)) muZ).pairCycles
          1 3).hom (z1 ⊗ₜ[ℤ] z2)) ⊗ₜ[ℤ]
      ((tensorObj K1 K2).homologyπ (1 + 3)).hom
        ((ChainGradedPairing.pairCycles (𝟙 (tensorObj K1 K2))
          (ChainGradedPairing.homologyDescentData (𝟙 (tensorObj K1 K2)))
          1 3).hom (x1 ⊗ₜ[ℤ] y2))) = 9 := by
  have hswap : (linearHomCochainEvaluationHomology ℤ (tensorObj K1 K2) Z1 (1 + 3)).hom
        ((((LHFℤ Z1).obj
            (op (tensorObj K1 K2))).homologyπ (1 + 3)).hom
            (((linearHomCochainGradedPairing ℤ (𝟙 (tensorObj K1 K2)) muZ).pairCycles
              1 3).hom (z1 ⊗ₜ[ℤ] z2)) ⊗ₜ[ℤ]
          ((tensorObj K1 K2).homologyπ (1 + 3)).hom
            ((ChainGradedPairing.pairCycles (𝟙 (tensorObj K1 K2))
              (ChainGradedPairing.homologyDescentData (𝟙 (tensorObj K1 K2)))
              1 3).hom (x1 ⊗ₜ[ℤ] y2))) =
      ((β_ ((tensorObj K1 K2).homology (1 + 3))
          (((LHFℤ Z1).obj
            (op (tensorObj K1 K2))).homology (1 + 3))).hom ≫
        linearHomCochainEvaluationHomology ℤ (tensorObj K1 K2) Z1 (1 + 3)).hom
        (((tensorObj K1 K2).homologyπ (1 + 3)).hom
            ((ChainGradedPairing.pairCycles (𝟙 (tensorObj K1 K2))
              (ChainGradedPairing.homologyDescentData (𝟙 (tensorObj K1 K2)))
              1 3).hom (x1 ⊗ₜ[ℤ] y2)) ⊗ₜ[ℤ]
          (((LHFℤ Z1).obj
            (op (tensorObj K1 K2))).homologyπ (1 + 3)).hom
            (((linearHomCochainGradedPairing ℤ (𝟙 (tensorObj K1 K2)) muZ).pairCycles
              1 3).hom (z1 ⊗ₜ[ℤ] z2))) :=
    congrArg (linearHomCochainEvaluationHomology ℤ (tensorObj K1 K2) Z1 (1 + 3)).hom
      (ModuleCat.MonoidalCategory.braiding_hom_apply
        (((tensorObj K1 K2).homologyπ (1 + 3)).hom
          ((ChainGradedPairing.pairCycles (𝟙 (tensorObj K1 K2))
            (ChainGradedPairing.homologyDescentData (𝟙 (tensorObj K1 K2)))
            1 3).hom (x1 ⊗ₜ[ℤ] y2)))
        ((((LHFℤ Z1).obj
            (op (tensorObj K1 K2))).homologyπ (1 + 3)).hom
          (((linearHomCochainGradedPairing ℤ (𝟙 (tensorObj K1 K2)) muZ).pairCycles
            1 3).hom (z1 ⊗ₜ[ℤ] z2)))).symm
  have hU := ConcreteCategory.congr_hom
    (linearHomCochainHomologyComparisonModuleCat_uncurry ℤ (tensorObj K1 K2) Z1 (1 + 3))
    (((tensorObj K1 K2).homologyπ (1 + 3)).hom
        ((ChainGradedPairing.pairCycles (𝟙 (tensorObj K1 K2))
          (ChainGradedPairing.homologyDescentData (𝟙 (tensorObj K1 K2)))
          1 3).hom (x1 ⊗ₜ[ℤ] y2)) ⊗ₜ[ℤ]
      (((LHFℤ Z1).obj
        (op (tensorObj K1 K2))).homologyπ (1 + 3)).hom
        (((linearHomCochainGradedPairing ℤ (𝟙 (tensorObj K1 K2)) muZ).pairCycles
          1 3).hom (z1 ⊗ₜ[ℤ] z2)))
  have hunc : (MonoidalClosed.uncurry cT).hom
        (((tensorObj K1 K2).homologyπ (1 + 3)).hom
            ((ChainGradedPairing.pairCycles (𝟙 (tensorObj K1 K2))
              (ChainGradedPairing.homologyDescentData (𝟙 (tensorObj K1 K2)))
              1 3).hom (x1 ⊗ₜ[ℤ] y2)) ⊗ₜ[ℤ]
          (((LHFℤ Z1).obj
            (op (tensorObj K1 K2))).homologyπ (1 + 3)).hom
            (((linearHomCochainGradedPairing ℤ (𝟙 (tensorObj K1 K2)) muZ).pairCycles
              1 3).hom (z1 ⊗ₜ[ℤ] z2))) =
      ((linearHomCochainHomologyComparisonModuleCat ℤ (tensorObj K1 K2) Z1 (1 + 3)).hom
          ((((LHFℤ Z1).obj
            (op (tensorObj K1 K2))).homologyπ (1 + 3)).hom
            (((linearHomCochainGradedPairing ℤ (𝟙 (tensorObj K1 K2)) muZ).pairCycles
              1 3).hom (z1 ⊗ₜ[ℤ] z2)))).hom
        (((tensorObj K1 K2).homologyπ (1 + 3)).hom
          ((ChainGradedPairing.pairCycles (𝟙 (tensorObj K1 K2))
            (ChainGradedPairing.homologyDescentData (𝟙 (tensorObj K1 K2)))
            1 3).hom (x1 ⊗ₜ[ℤ] y2))) :=
    ModuleCat.monoidalClosed_uncurry cT _ _
  have hπT : (((LHFℤ Z1).obj
          (op (tensorObj K1 K2))).homologyπ (1 + 3)) ≫
        linearHomCochainHomologyComparisonModuleCat ℤ (tensorObj K1 K2) Z1 (1 + 3) =
      cyclesComparisonℤ (tensorObj K1 K2) Z1 (1 + 3) := by
    apply ShortComplex.π_descHomology
  have hcompcup :
      (linearHomCochainHomologyComparisonModuleCat ℤ (tensorObj K1 K2) Z1 (1 + 3)).hom
          ((((LHFℤ Z1).obj
            (op (tensorObj K1 K2))).homologyπ (1 + 3)).hom
            (((linearHomCochainGradedPairing ℤ (𝟙 (tensorObj K1 K2)) muZ).pairCycles
              1 3).hom (z1 ⊗ₜ[ℤ] z2))) =
        cycleDescℤ (tensorObj K1 K2) Z1 (1 + 3)
          (((linearHomCochainGradedPairing ℤ (𝟙 (tensorObj K1 K2)) muZ).pairCycles
            1 3).hom (z1 ⊗ₜ[ℤ] z2)) := by
    have h := ConcreteCategory.congr_hom hπT
      (((linearHomCochainGradedPairing ℤ (𝟙 (tensorObj K1 K2)) muZ).pairCycles
        1 3).hom (z1 ⊗ₜ[ℤ] z2))
    rw [ModuleCat.comp_apply] at h
    refine h.trans ?_
    exact (@linearHomCochainCyclesComparison_hom_apply ℤ _ (ModuleCat ℤ) _ _
      ModuleCat.instLinear (tensorObj K1 K2)
      Z1 (1 + 3) _).symm
  have hfac : (cycleDescℤ (tensorObj K1 K2) Z1 (1 + 3)
          (((linearHomCochainGradedPairing ℤ (𝟙 (tensorObj K1 K2)) muZ).pairCycles
            1 3).hom (z1 ⊗ₜ[ℤ] z2))).hom
        (((tensorObj K1 K2).homologyπ (1 + 3)).hom
          ((ChainGradedPairing.pairCycles (𝟙 (tensorObj K1 K2))
            (ChainGradedPairing.homologyDescentData (𝟙 (tensorObj K1 K2)))
            1 3).hom (x1 ⊗ₜ[ℤ] y2))) =
      ((((LHFℤ Z1).obj
          (op (tensorObj K1 K2))).iCycles (1 + 3)).hom
          (((linearHomCochainGradedPairing ℤ (𝟙 (tensorObj K1 K2)) muZ).pairCycles
            1 3).hom (z1 ⊗ₜ[ℤ] z2))).hom
        (((tensorObj K1 K2).iCycles (1 + 3)).hom
          ((ChainGradedPairing.pairCycles (𝟙 (tensorObj K1 K2))
            (ChainGradedPairing.homologyDescentData (𝟙 (tensorObj K1 K2)))
            1 3).hom (x1 ⊗ₜ[ℤ] y2))) := by
    have h := ConcreteCategory.congr_hom
      (@linearHomCochainCycleDesc_fac ℤ _ (ModuleCat ℤ) _ _
        ModuleCat.instLinear (tensorObj K1 K2) Z1 (1 + 3)
        (((linearHomCochainGradedPairing ℤ (𝟙 (tensorObj K1 K2)) muZ).pairCycles
          1 3).hom (z1 ⊗ₜ[ℤ] z2)))
      ((ChainGradedPairing.pairCycles (𝟙 (tensorObj K1 K2))
          (ChainGradedPairing.homologyDescentData (𝟙 (tensorObj K1 K2)))
          1 3).hom (x1 ⊗ₜ[ℤ] y2))
    rw [ModuleCat.comp_apply] at h
    exact h.trans (ModuleCat.comp_apply _ _ _)
  have hcupi : (((LHFℤ Z1).obj
          (op (tensorObj K1 K2))).iCycles (1 + 3)).hom
        (((linearHomCochainGradedPairing ℤ (𝟙 (tensorObj K1 K2)) muZ).pairCycles
          1 3).hom (z1 ⊗ₜ[ℤ] z2)) =
      linearHomPairingDesc ℤ muZ 1 3 phi1 psi2 := by
    have h := ConcreteCategory.congr_hom
      ((linearHomCochainGradedPairing ℤ (𝟙 (tensorObj K1 K2)) muZ).pairCycles_i 1 3)
      (z1 ⊗ₜ[ℤ] z2)
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply,
      ModuleCat.MonoidalCategory.tensorHom_tmul, iC_z1, iC_z2] at h
    have hpair : ((linearHomCochainGradedPairing ℤ (𝟙 (tensorObj K1 K2)) muZ).pair
          1 3).hom (phi1 ⊗ₜ[ℤ] psi2) =
        linearHomPairingDesc ℤ muZ 1 3 phi1 psi2 := by
      have ht := linearHomCochainPair_tmul ℤ (𝟙 (tensorObj K1 K2)) muZ 1 3
        phi1 psi2
      rw [HomologicalComplex.id_f, Category.id_comp] at ht
      rwa [linearHomCochainGradedPairing_pair]
    exact h.trans hpair
  have hinclcup :
      (((LHFℤ Z1).obj
          (op (tensorObj K1 K2))).iCycles (1 + 3)).hom
          (((linearHomCochainGradedPairing ℤ (𝟙 (tensorObj K1 K2)) muZ).pairCycles
            1 3).hom (z1 ⊗ₜ[ℤ] z2)) =
        linearHomPairingDesc ℤ muZ 1 3 phi1 psi2 :=
    hcupi
  have hcrossi : ((tensorObj K1 K2).iCycles (1 + 3)).hom
        ((ChainGradedPairing.pairCycles (𝟙 (tensorObj K1 K2))
          (ChainGradedPairing.homologyDescentData (𝟙 (tensorObj K1 K2)))
          1 3).hom (x1 ⊗ₜ[ℤ] y2)) =
      (ιTensorObj K1 K2 1 3 (1 + 3) rfl).hom
        (((K1.iCycles 1).hom x1) ⊗ₜ[ℤ] ((K2.iCycles 3).hom y2)) := by
    have h := ConcreteCategory.congr_hom
      (ChainGradedPairing.pairCycles_i (𝟙 (tensorObj K1 K2))
        (ChainGradedPairing.homologyDescentData (𝟙 (tensorObj K1 K2))) 1 3)
      (x1 ⊗ₜ[ℤ] y2)
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply,
      ModuleCat.MonoidalCategory.tensorHom_tmul] at h
    have hpairι : ChainGradedPairing.pair (𝟙 (tensorObj K1 K2)) 1 3 =
        ιTensorObj K1 K2 1 3 (1 + 3) rfl := by
      unfold ChainGradedPairing.pair
      rw [HomologicalComplex.id_f, Category.comp_id]
    rwa [hpairι] at h
  have hdesc : (linearHomPairingDesc ℤ muZ 1 3 phi1 psi2).hom
        ((ιTensorObj K1 K2 1 3 (1 + 3) rfl).hom
          (((K1.iCycles 1).hom x1) ⊗ₜ[ℤ] ((K2.iCycles 3).hom y2))) =
      muZ.hom (phi1.hom ((K1.iCycles 1).hom x1) ⊗ₜ[ℤ]
        psi2.hom ((K2.iCycles 3).hom y2)) := by
    have h := ConcreteCategory.congr_hom
      (ιTensorObj_comp_linearHomPairingDesc ℤ muZ 1 3 1 3 rfl phi1 psi2)
      (((K1.iCycles 1).hom x1) ⊗ₜ[ℤ] ((K2.iCycles 3).hom y2))
    rw [dite_eq_left rfl, ModuleCat.comp_apply, ModuleCat.comp_apply,
      ModuleCat.MonoidalCategory.tensorHom_tmul] at h
    exact h
  have hmu : muZ.hom ((3 : Z1) ⊗ₜ[ℤ] (3 : Z1)) = 9 := by
    show TensorProduct.lid ℤ ℤ ((3 : ℤ) ⊗ₜ[ℤ] (3 : ℤ)) = 9
    rw [TensorProduct.lid_tmul]
    rfl
  exact hswap.trans (hU.symm.trans (hunc.trans
    ((congrArg (fun f : (tensorObj K1 K2).homology (1 + 3) ⟶ Z1 =>
        f.hom (((tensorObj K1 K2).homologyπ (1 + 3)).hom
          ((ChainGradedPairing.pairCycles (𝟙 (tensorObj K1 K2))
            (ChainGradedPairing.homologyDescentData (𝟙 (tensorObj K1 K2)))
            1 3).hom (x1 ⊗ₜ[ℤ] y2)))) hcompcup).trans
      (hfac.trans
        ((congrArg (fun f : (tensorObj K1 K2).X (1 + 3) ⟶ Z1 =>
            f.hom (((tensorObj K1 K2).iCycles (1 + 3)).hom
              ((ChainGradedPairing.pairCycles (𝟙 (tensorObj K1 K2))
                (ChainGradedPairing.homologyDescentData (𝟙 (tensorObj K1 K2)))
                1 3).hom (x1 ⊗ₜ[ℤ] y2)))) hinclcup).trans
          ((congrArg (linearHomPairingDesc ℤ muZ 1 3 phi1 psi2).hom hcrossi).trans
            (hdesc.trans
              ((congrArg muZ.hom
                  (congrArg₂ (TensorProduct.tmul ℤ) phi1_x1 psi2_y2)).trans
                hmu))))))))

/-- The tensor evaluation composite evaluates the pure tensor of the four
representative classes to `9`, in degrees `1` and `3`. -/
example : ((((linearHomCochainGradedPairing ℤ
        (𝟙 (tensorObj K1 K2)) muZ).pairHomology 1 3) ⊗ₘ
      (ChainGradedPairing.pairHomology
        (𝟙 (tensorObj K1 K2))
        (ChainGradedPairing.homologyDescentData
          (𝟙 (tensorObj K1 K2))) 1 3)) ≫
      linearHomCochainEvaluationHomology ℤ (tensorObj K1 K2) Z1 (1 + 3)).hom
    ((((D1.homologyπ 1).hom z1) ⊗ₜ[ℤ] ((D2.homologyπ 3).hom z2)) ⊗ₜ[ℤ]
      (((K1.homologyπ 1).hom x1) ⊗ₜ[ℤ] ((K2.homologyπ 3).hom y2))) = 9 :=
  tensorEvaluation_single_factor.trans tensorEvaluation_single_eval

/-- The same numeric for the cross evaluation with identity cross product,
coproduct, and diagonal: the composite is the tensor evaluation above. -/
example : ((((linearHomCochainGradedPairing ℤ
        (𝟙 (tensorObj K1 K2)) muZ).pairHomology 1 3) ⊗ₘ
      (ChainGradedPairing.pairHomology
        (𝟙 (tensorObj K1 K2))
        (ChainGradedPairing.homologyDescentData
          (𝟙 (tensorObj K1 K2))) 1 3 ≫
        (tensorObj K1 K2).homologyMap (𝟙 (tensorObj K1 K2)) (1 + 3))) ≫
      linearHomCochainEvaluationHomology ℤ (tensorObj K1 K2) Z1 (1 + 3)).hom
    ((((D1.homologyπ 1).hom z1) ⊗ₜ[ℤ] ((D2.homologyπ 3).hom z2)) ⊗ₜ[ℤ]
      (((K1.homologyπ 1).hom x1) ⊗ₜ[ℤ] ((K2.homologyπ 3).hom y2))) = 9 := by
  simpa only [HomologicalComplex.homologyMap_id, Category.comp_id] using
    tensorEvaluation_single_factor.trans tensorEvaluation_single_eval

end HomologicalComplex

end
