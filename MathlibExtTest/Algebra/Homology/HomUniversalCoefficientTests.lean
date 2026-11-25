/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChainComplex.HomUniversalCoefficient
public import Mathlib.Algebra.Category.ModuleCat.Images
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.FreeModule.PID
public meta import Mathlib.Tactic.NormNum
public meta import Lean.Elab.Tactic.Omega

/-!
# Full-product universal coefficients for finite integer complexes

The chain complex has `ℤ²` in degree zero, `ℤ` in degree minus one, and
differential `(a, b) ↦ 2a`. The coefficient cochain complex has `ℤ` in
degrees minus one and zero, with differential `z ↦ 2z`. Every other term
is zero. Finite coordinate modules are free, and the actual differential
images are projective by the submodule theorem over the PID `ℤ`.

The full Hom differential has negative postcomposition from degree minus
two to minus one and positive postcomposition from minus one to zero.
Degree-zero cohomology has the two parity coordinates: the Ext coordinate
from the cokernel `ℤ/2` and the Hom coordinate from the free kernel `ℤ`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits HomologicalComplex
open CategoryTheory.Abelian
open ChainComplex

namespace MathlibExtTest.Algebra.Homology.HomUniversalCoefficient

private abbrev V (n : ℕ) : ModuleCat.{0} ℤ := ModuleCat.of ℤ (Fin n → ℤ)

private def chainRank (p : ℤ) : ℕ := if p = 0 then 2 else if p = -1 then 1 else 0

private def coefficientRank (q : ℤ) : ℕ := if q = -1 ∨ q = 0 then 1 else 0

private def chainTerm (p : ℤ) : ModuleCat.{0} ℤ := V (chainRank p)

private def coefficientTerm (q : ℤ) : ModuleCat.{0} ℤ := V (coefficientRank q)

private def twiceFirst : V 2 ⟶ V 1 :=
  ModuleCat.ofHom
    { toFun x _ := 2 * x 0
      map_add' x y := by
        funext i
        simp only [Pi.add_apply, mul_add]
      map_smul' r x := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_left_comm 2 r (x 0) }

private def secondCoordinate : V 2 ⟶ V 1 :=
  ModuleCat.ofHom
    { toFun x _ := x 1
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

private def chainStep (p : ℤ) : chainTerm (p + 1) ⟶ chainTerm p :=
  if h : p = -1 then by subst p; exact twiceFirst else 0

private def coefficientStep (q : ℤ) : coefficientTerm q ⟶ coefficientTerm (q + 1) :=
  if h : q = -1 then by subst q; exact (2 : ℤ) • 𝟙 (V 1) else 0

private lemma chainStep_square (p : ℤ) : chainStep (p + 1) ≫ chainStep p = 0 := by
  by_cases h : p = -1
  · subst p
    simp [chainStep]
  · simp [chainStep, h]

private lemma coefficientStep_square (q : ℤ) :
    coefficientStep q ≫ coefficientStep (q + 1) = 0 := by
  by_cases h : q = -1
  · subst q
    simp [coefficientStep]
  · simp [coefficientStep, h]

private def P : ChainComplex (ModuleCat.{0} ℤ) ℤ :=
  ChainComplex.of chainTerm chainStep chainStep_square

private def Q : CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  CochainComplex.of coefficientTerm coefficientStep coefficientStep_square

private lemma projectiveTerms (p : ℤ) : Projective (P.X p) :=
  ModuleCat.projective_of_free (Pi.basisFun ℤ (Fin (chainRank p)))

private lemma projectiveImages (p : ℤ) : Projective (Abelian.image (P.d p (p - 1))) := by
  let f := P.d p (p - 1)
  obtain ⟨r, ⟨b⟩⟩ := Submodule.nonempty_basis_of_pid
    (Pi.basisFun ℤ (Fin (chainRank (p - 1)))) f.hom.range
  let e : Abelian.image f ≅ ModuleCat.of ℤ f.hom.range :=
    Abelian.imageIsoImage f ≪≫ ModuleCat.imageIsoRange f
  exact Projective.of_iso e.symm (ModuleCat.projective_of_free b)

private lemma projectiveCycles (p : ℤ) : Projective (P.cycles p) := by
  letI : Projective (P.X p) := projectiveTerms p
  letI : Projective (Abelian.image (P.d p ((ComplexShape.down ℤ).next p))) := by
    simpa only [ChainComplex.next] using projectiveImages p
  exact HomologicalComplex.projective_cycles P p

private abbrev UCT := homUniversalCoefficientSequence P Q 0 projectiveTerms projectiveImages

example : P.X 0 = V 2 := rfl

example : P.X (-1) = V 1 := rfl

example : P.X (-2) = V 0 := rfl

example : Q.X (-1) = V 1 := rfl

example : Q.X 0 = V 1 := rfl

example : Q.X 1 = V 0 := rfl

example : P.d 0 (-1) = twiceFirst := by
  change ChainComplex.of.d chainTerm chainStep 0 (-1) = twiceFirst
  rw [show (0 : ℤ) = -1 + 1 by omega, ChainComplex.of_d]
  rfl

example : Q.d (-1) 0 = (2 : ℤ) • 𝟙 (V 1) := by
  change CochainComplex.of.d coefficientTerm coefficientStep (-1) 0 = _
  rw [show (0 : ℤ) = -1 + 1 by omega, CochainComplex.of_d]
  rfl

example : twiceFirst (fun _ => 1) 0 = 2 := rfl

example : (fun _ : Fin 1 => (1 : ℤ)) ∉ LinearMap.range twiceFirst.hom := by
  rintro ⟨x, hx⟩
  have h : 2 * x 0 = 1 := congrFun hx 0
  omega

private def degreeMinusTwoFamily (r : ℤ) : P.X (-r) ⟶ Q.X (r + (-2)) :=
  if h : r = 1 then by subst r; exact 𝟙 (V 1) else 0

private def degreeMinusOneFamily (r : ℤ) : P.X (-r) ⟶ Q.X (r + (-1)) :=
  if h : r = 1 then by subst r; exact 𝟙 (V 1)
  else if h : r = 0 then by subst r; exact secondCoordinate else 0

private def degreeMinusTwo := (homCochainPiEquiv P Q (-2)).symm degreeMinusTwoFamily

private def degreeMinusOne := (homCochainPiEquiv P Q (-1)).symm degreeMinusOneFamily

example : (homCochainPiEquiv P Q (-2)) degreeMinusTwo 1 = 𝟙 (V 1) := by
  simp [degreeMinusTwo, degreeMinusTwoFamily]

example : (homCochainPiEquiv P Q (-1)) degreeMinusOne 0 = secondCoordinate := by
  simp [degreeMinusOne, degreeMinusOneFamily]

example : degreeMinusTwo.v 1 (-1) (by omega) (fun _ => 4) 0 = 4 := by
  simp [degreeMinusTwo, homCochainPiEquiv_symm_v, degreeMinusTwoFamily,
    HomologicalComplex.XIsoOfEq]

example : degreeMinusOne.v 0 (-1) (by omega) (fun i => if i = 0 then 3 else 5) 0 = 5 := by
  simp [degreeMinusOne, homCochainPiEquiv_symm_v, degreeMinusOneFamily,
    HomologicalComplex.XIsoOfEq, secondCoordinate]

example :
    ((((homCochainComplex P Q).d (-2) (-1)).hom degreeMinusTwo).v
      1 0 (by omega)) (fun _ => 4) 0 = -8 := by
  rw [homCochainComplex_d_v P Q (-2) (-1) (by omega) degreeMinusTwo 1 0 (by omega)]
  norm_num [degreeMinusTwo, homCochainPiEquiv_symm_v, degreeMinusTwoFamily,
    P, Q, chainTerm, coefficientTerm, chainRank, coefficientRank,
    ChainComplex.of.d, CochainComplex.of.d, chainStep, coefficientStep,
    cochainComplexEquivalence, HomologicalComplex.restriction, HomologicalComplex.XIsoOfEq]

example :
    ((((homCochainComplex P Q).d (-2) (-1)).hom degreeMinusTwo).v
      0 (-1) (by omega)) (fun i => if i = 0 then 3 else 5) 0 = 6 := by
  rw [homCochainComplex_d_v P Q (-2) (-1) (by omega) degreeMinusTwo 0 (-1) (by omega)]
  norm_num [degreeMinusTwo, homCochainPiEquiv_symm_v, degreeMinusTwoFamily,
    P, Q, chainTerm, coefficientTerm, chainRank, coefficientRank,
    ChainComplex.of.d, CochainComplex.of.d, chainStep, coefficientStep, twiceFirst,
    cochainComplexEquivalence, HomologicalComplex.restriction, HomologicalComplex.XIsoOfEq]

example :
    ((((homCochainComplex P Q).d (-1) 0).hom degreeMinusOne).v
      0 0 (by omega)) (fun i => if i = 0 then 3 else 5) 0 = 16 := by
  rw [homCochainComplex_d_v P Q (-1) 0 (by omega) degreeMinusOne 0 0 (by omega)]
  norm_num [degreeMinusOne, homCochainPiEquiv_symm_v, degreeMinusOneFamily,
    P, Q, chainTerm, coefficientTerm, chainRank, coefficientRank,
    ChainComplex.of.d, CochainComplex.of.d, chainStep, coefficientStep,
    twiceFirst, secondCoordinate, cochainComplexEquivalence,
    HomologicalComplex.restriction, HomologicalComplex.XIsoOfEq]

example : UCT.ShortExact :=
  homUniversalCoefficientSequence_shortExact P Q 0 projectiveTerms projectiveImages

example : UCT.X₁ =
    (letI := HasExt.standard (ModuleCat.{0} ℤ)
      AddCommGrpCat.of (∀ p : ℤ, Ext.{1} (P.homology p) (Q.homology (-1 - p)) 1)) := rfl

example : UCT.X₂ =
    AddCommGrpCat.uliftFunctor.{1, 0}.obj ((homCochainComplex P Q).homology 0) := rfl

example : UCT.X₃ = AddCommGrpCat.uliftFunctor.{1, 0}.obj
    (AddCommGrpCat.of (∀ p : ℤ, P.homology p ⟶ Q.homology (0 - p))) := rfl

example :
    (AddCommGrpCat.uliftIntPiIso.{0, 1} (fun _ : ℤ => AddCommGrpCat.of ℤ)).hom
      (ULift.up (fun p : ℤ => p)) (-3) = ULift.up (-3 : ℤ) := rfl

private def sourceMap : P ⟶ P := (3 : ℤ) • 𝟙 P

private def coefficientMap : Q ⟶ Q := (-1 : ℤ) • 𝟙 Q

example :
    ((((homCochainComplexMap sourceMap coefficientMap).f (-1)).hom degreeMinusOne).v
      0 (-1) (by omega)) (fun i => if i = 0 then 3 else 5) 0 = -15 := by
  rw [homCochainComplexMap_v sourceMap coefficientMap (-1) 0 (-1) (by omega)]
  norm_num [sourceMap, coefficientMap, degreeMinusOne, homCochainPiEquiv_symm_v,
    degreeMinusOneFamily, secondCoordinate, cochainComplexEquivalence,
    HomologicalComplex.restriction, HomologicalComplex.XIsoOfEq]

private def uctMap : UCT ⟶ UCT :=
  homUniversalCoefficientSequenceMap sourceMap coefficientMap 0
    projectiveTerms projectiveImages projectiveTerms projectiveImages

example : uctMap.τ₂ = AddCommGrpCat.uliftFunctor.{1, 0}.map
    (HomologicalComplex.homologyMap (homCochainComplexMap sourceMap coefficientMap) 0) :=
  homUniversalCoefficientSequenceMap_τ₂ sourceMap coefficientMap 0
    projectiveTerms projectiveImages projectiveTerms projectiveImages

example (e : UCT.X₁) :
    letI := HasExt.standard (ModuleCat.{0} ℤ)
    uctMap.τ₁ e (-1) =
      ((Ext.mk₀ (HomologicalComplex.homologyMap sourceMap (-1))).comp (e (-1))
        (zero_add 1)).comp (Ext.mk₀ (HomologicalComplex.homologyMap coefficientMap 0))
          (add_zero 1) := by
  simpa using homUniversalCoefficientSequenceMap_τ₁_apply sourceMap coefficientMap 0
    projectiveTerms projectiveImages projectiveTerms projectiveImages e (-1)

example (k : UCT.X₃) :
    uctMap.τ₃ k = ULift.up (fun p : ℤ =>
      HomologicalComplex.homologyMap sourceMap p ≫ k.down p ≫
        HomologicalComplex.homologyMap coefficientMap (0 - p)) := by
  simpa using homUniversalCoefficientSequenceMap_τ₃_apply sourceMap coefficientMap 0
    projectiveTerms projectiveImages projectiveTerms projectiveImages k

example (k : UCT.X₃) :
    (uctMap.τ₃ k).down 0 = HomologicalComplex.homologyMap sourceMap 0 ≫ k.down 0 ≫
      HomologicalComplex.homologyMap coefficientMap 0 := by
  have h := homUniversalCoefficientSequenceMap_τ₃_apply sourceMap coefficientMap 0
    projectiveTerms projectiveImages projectiveTerms projectiveImages k
  exact congrArg (fun z : UCT.X₃ => z.down 0) h

section EndpointRepresentatives

local instance : HasExt.{1} (ModuleCat.{0} ℤ) := HasExt.standard (ModuleCat.{0} ℤ)

example :
    (homUctImagesCohomologyIso P Q (-1) 0 (by omega) projectiveImages).hom ≫
      (homUctProductPresentation P (fun p => Q.homology (-1 - p))).g ≫
      (homUniversalCoefficientSequenceEngine P Q 0 projectiveTerms projectiveImages).f =
        AddCommGrpCat.uliftFunctor.{1, 0}.map
          (HomologicalComplex.homologyMap (homCyclesSequence P Q).f 0) := by
  simpa using homUniversalCoefficientSequenceEngine_left_representative
    P Q 0 projectiveTerms projectiveImages

example :
    let hZ : ∀ p : ℤ, Projective (P.cycles p) :=
      projectiveCycles
    (homUniversalCoefficientSequenceEngine P Q 0 projectiveTerms projectiveImages).g ≫
      homUctHomKernelInclusion P (fun p => Q.homology (0 - p)) =
        AddCommGrpCat.uliftFunctor.{1, 0}.map
          (HomologicalComplex.homologyMap (homCyclesSequence P Q).g 0) ≫
            (homUctCyclesCohomologyIso P Q 0 hZ).hom := by
  simpa using homUniversalCoefficientSequenceEngine_right_representative
    P Q 0 projectiveTerms projectiveImages

end EndpointRepresentatives

end MathlibExtTest.Algebra.Homology.HomUniversalCoefficient
