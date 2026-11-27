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

private abbrev chainRank (p : ℤ) : ℕ := if p = 0 then 2 else if p = -1 then 1 else 0

private abbrev coefficientRank (q : ℤ) : ℕ := if q = -1 ∨ q = 0 then 1 else 0

private abbrev chainTerm (p : ℤ) : ModuleCat.{0} ℤ := V (chainRank p)

private abbrev coefficientTerm (q : ℤ) : ModuleCat.{0} ℤ := V (coefficientRank q)

private abbrev twiceFirst : V 2 ⟶ V 1 :=
  ModuleCat.ofHom
    { toFun x _ := 2 * x 0
      map_add' x y := by
        funext i
        simp only [Pi.add_apply, mul_add]
      map_smul' r x := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_left_comm 2 r (x 0) }

private abbrev secondCoordinate : V 2 ⟶ V 1 :=
  ModuleCat.ofHom
    { toFun x _ := x 1
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

private abbrev chainStep (p : ℤ) : chainTerm (p + 1) ⟶ chainTerm p :=
  if h : p = -1 then by subst p; exact twiceFirst else 0

private abbrev coefficientStep (q : ℤ) : coefficientTerm q ⟶ coefficientTerm (q + 1) :=
  if h : q = -1 then by subst q; exact (2 : ℤ) • 𝟙 (V 1) else 0

private lemma chainStep_square (p : ℤ) : chainStep (p + 1) ≫ chainStep p = 0 := by
  by_cases h : p = -1
  · subst p
    change (0 : V 0 ⟶ V 2) ≫ twiceFirst = 0
    exact CategoryTheory.Limits.zero_comp
  · have hs : chainStep p = 0 := dite_eq_right h
    rw [hs]
    exact CategoryTheory.Limits.comp_zero

private lemma coefficientStep_square (q : ℤ) :
    coefficientStep q ≫ coefficientStep (q + 1) = 0 := by
  by_cases h : q = -1
  · subst q
    change ((2 : ℤ) • 𝟙 (V 1)) ≫ (0 : V 1 ⟶ V 0) = 0
    exact CategoryTheory.Limits.comp_zero
  · have hs : coefficientStep q = 0 := dite_eq_right h
    rw [hs]
    exact CategoryTheory.Limits.zero_comp

private abbrev P : ChainComplex (ModuleCat.{0} ℤ) ℤ :=
  ChainComplex.of chainTerm chainStep chainStep_square

private abbrev Q : CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  CochainComplex.of coefficientTerm coefficientStep coefficientStep_square

private lemma reindexedP_d (i j : ℤ) :
    ((cochainComplexEquivalence (ModuleCat.{0} ℤ)).functor.obj P).d i j =
      P.d (-i) (-j) := rfl

private lemma p_d_zero_neg_one : P.d 0 (-1) = twiceFirst := by
  have hindex : (-1 : ℤ) + 1 = 0 := by omega
  let statement (i : ℤ) : Prop := HEq (P.d i (-1)) twiceFirst
  have hstep : HEq (chainStep (-1)) twiceFirst := by
    simp only [chainStep, dite_eq_left]
    rfl
  have hbase : statement ((-1 : ℤ) + 1) :=
    (heq_of_eq (ChainComplex.of_d chainTerm chainStep (-1))).trans hstep
  have hzero : statement 0 := Eq.mp (congrArg statement hindex) hbase
  exact eq_of_heq hzero

private lemma p_d_neg_one_neg_two : P.d (-1) (-2) = 0 := by
  let statement (i : ℤ) : Prop := P.d i (-2) = 0
  have hbase : statement ((-2 : ℤ) + 1) := by
    simpa only [statement, P, chainStep,
      dite_eq_right (by decide : (-2 : ℤ) ≠ -1)] using
      (ChainComplex.of_d chainTerm chainStep (-2))
  exact Eq.mp (congrArg statement (by omega : (-2 : ℤ) + 1 = -1)) hbase

private lemma q_d_neg_one_zero_heq :
    HEq (Q.d (-1) 0) ((2 : ℤ) • 𝟙 (V 1)) := by
  let statement (j : ℤ) : Prop := HEq (Q.d (-1) j) ((2 : ℤ) • 𝟙 (V 1))
  have hstep : HEq (coefficientStep (-1)) ((2 : ℤ) • 𝟙 (V 1)) := by
    simp only [coefficientStep, dite_eq_left]
    rfl
  have hbase : statement ((-1 : ℤ) + 1) :=
    (heq_of_eq (CochainComplex.of_d coefficientTerm coefficientStep (-1))).trans hstep
  exact Eq.mp (congrArg statement (by omega : (-1 : ℤ) + 1 = 0)) hbase

private lemma q_d_neg_two_neg_one : Q.d (-2) (-1) = 0 := by
  let statement (j : ℤ) : Prop := Q.d (-2) j = 0
  have hbase : statement ((-2 : ℤ) + 1) := by
    simpa only [statement, Q, coefficientStep,
      dite_eq_right (by decide : (-2 : ℤ) ≠ -1)] using
      (CochainComplex.of_d coefficientTerm coefficientStep (-2))
  exact Eq.mp (congrArg statement (by omega : (-2 : ℤ) + 1 = -1)) hbase

private lemma p_X_coordinate (i : ℤ) : P.X i = V (chainRank i) := rfl

private lemma q_X_coordinate (i : ℤ) : Q.X i = V (coefficientRank i) := rfl

private lemma reindexedP_X_coordinate (i : ℤ) :
    ((cochainComplexEquivalence (ModuleCat.{0} ℤ)).functor.obj P).X i =
      V (chainRank (-i)) := rfl

private lemma transportHom_eq_of_heq
    {A B A' B' : ModuleCat.{0} ℤ} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f g) :
    (eqToIso hA).inv ≫ f ≫ (eqToIso hB).hom = g := by
  subst A'
  subst B'
  simpa only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id] using eq_of_heq h

private lemma transportHom_function_heq
    {A B A' B' : ModuleCat.{0} ℤ} (hA : A = A') (hB : B = B') (f : A ⟶ B) :
    HEq (⇑(((eqToIso hA).inv ≫ f ≫ (eqToIso hB).hom).hom)) (⇑f.hom) := by
  subst A'
  subst B'
  simp only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id]
  rfl

private lemma zeroHom_heq
    {A B A' B' : ModuleCat.{0} ℤ} (hA : A = A') (hB : B = B') :
    HEq (0 : A ⟶ B) (0 : A' ⟶ B') := by
  subst A'
  subst B'
  rfl

private lemma differential_heq
    {K : CochainComplex (ModuleCat.{0} ℤ) ℤ} {i i' j j' : ℤ}
    (hi : i = i') (hj : j = j') : HEq (K.d i j) (K.d i' j') := by
  subst i'
  subst j'
  rfl

private lemma chainDifferential_heq
    {K : ChainComplex (ModuleCat.{0} ℤ) ℤ} {i i' j j' : ℤ}
    (hi : i = i') (hj : j = j') : HEq (K.d i j) (K.d i' j') := by
  subst i'
  subst j'
  rfl

private lemma comp_XIsoOfEq_heq
    {K : CochainComplex (ModuleCat.{0} ℤ) ℤ} {i j : ℤ}
    {A : ModuleCat.{0} ℤ} (h : i = j) (f : A ⟶ K.X i) :
    HEq (f ≫ (K.XIsoOfEq h).hom) f := by
  subst j
  simpa only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    Category.comp_id] using (show HEq f f from HEq.rfl)

private lemma cochainComponent_heq
    {K L : CochainComplex (ModuleCat.{0} ℤ) ℤ} {n i i' j j' : ℤ}
    (z : CochainComplex.HomComplex.Cochain K L n)
    (hi : i = i') (hj : j = j') (h : i + n = j) (h' : i' + n = j') :
    HEq (z.v i j h) (z.v i' j' h') := by
  subst i'
  subst j'
  rfl

private lemma smulId_heq {A B : ModuleCat.{0} ℤ} (h : A = B) (n : ℤ) :
    HEq (n • 𝟙 A) (n • 𝟙 B) := by
  subst B
  rfl

private lemma transportHom_sum_comp
    {A B C D A' B' C' D' : ModuleCat.{0} ℤ}
    (eA : A ≅ A') (eB : B ≅ B') (eC : C ≅ C') (eD : D ≅ D')
    (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ D) (k : D ⟶ C) (u : ℤˣ) :
    eA.inv ≫ (f ≫ g + u • (h ≫ k)) ≫ eC.hom =
      (eA.inv ≫ f ≫ eB.hom) ≫ (eB.inv ≫ g ≫ eC.hom) +
        u • ((eA.inv ≫ h ≫ eD.hom) ≫ (eD.inv ≫ k ≫ eC.hom)) := by
  simp only [Preadditive.comp_add, Preadditive.add_comp, Linear.comp_units_smul,
    Linear.units_smul_comp, Category.assoc, Iso.hom_inv_id_assoc]

private lemma transportHom_triple_comp
    {A B A' B' : ModuleCat.{0} ℤ} (eA : A ≅ A') (eB : B ≅ B')
    (f : A ⟶ A) (g : A ⟶ B) (h : B ⟶ B) :
    eA.inv ≫ (f ≫ g ≫ h) ≫ eB.hom =
      (eA.inv ≫ f ≫ eA.hom) ≫ (eA.inv ≫ g ≫ eB.hom) ≫
        (eB.inv ≫ h ≫ eB.hom) := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private lemma p_coordinate {i : ℤ} {n : ℕ} (h : chainRank i = n) : P.X i = V n :=
  (p_X_coordinate i).trans (congrArg V h)

private lemma q_coordinate {i : ℤ} {n : ℕ} (h : coefficientRank i = n) : Q.X i = V n :=
  (q_X_coordinate i).trans (congrArg V h)

private lemma reindexedP_coordinate {i : ℤ} {n : ℕ} (h : chainRank (-i) = n) :
    ((cochainComplexEquivalence (ModuleCat.{0} ℤ)).functor.obj P).X i = V n :=
  (reindexedP_X_coordinate i).trans (congrArg V h)

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
  let _ : Projective (P.X p) := projectiveTerms p
  have hnext : (ComplexShape.down ℤ).next p = p - 1 :=
    (ComplexShape.down ℤ).next_eq' (ComplexShape.down_mk p (p - 1) (by omega))
  let _ : Projective (Abelian.image (P.d p ((ComplexShape.down ℤ).next p))) :=
    Eq.mpr (congrArg (fun j : ℤ => Projective (Abelian.image (P.d p j))) hnext)
      (projectiveImages p)
  exact HomologicalComplex.projective_cycles P p

private abbrev UCT := homUniversalCoefficientSequence P Q 0 projectiveTerms projectiveImages

example : P.X 0 = V 2 := rfl

example : P.X (-1) = V 1 := rfl

example : P.X (-2) = V 0 := rfl

example : Q.X (-1) = V 1 := rfl

example : Q.X 0 = V 1 := rfl

example : Q.X 1 = V 0 := rfl

example : P.d 0 (-1) = twiceFirst := p_d_zero_neg_one

example : Q.d (-1) 0 = (2 : ℤ) • 𝟙 (V 1) :=
  CochainComplex.of_d coefficientTerm coefficientStep (-1)

example : twiceFirst (fun _ => 1) 0 = 2 := rfl

example : (fun _ : Fin 1 => (1 : ℤ)) ∉ LinearMap.range twiceFirst.hom := by
  rintro ⟨x, hx⟩
  have h : 2 * x 0 = 1 := congrFun hx 0
  omega

private abbrev degreeMinusTwoFamily (r : ℤ) : P.X (-r) ⟶ Q.X (r + (-2)) :=
  if h : r = 1 then by subst r; exact 𝟙 (V 1) else 0

private abbrev degreeMinusOneFamily (r : ℤ) : P.X (-r) ⟶ Q.X (r + (-1)) :=
  if h : r = 1 then by subst r; exact 𝟙 (V 1)
  else if h : r = 0 then by subst r; exact secondCoordinate else 0

private abbrev degreeMinusTwo := (homCochainPiEquiv P Q (-2)).symm degreeMinusTwoFamily

private abbrev degreeMinusOne := (homCochainPiEquiv P Q (-1)).symm degreeMinusOneFamily

example : (homCochainPiEquiv P Q (-2)) degreeMinusTwo 1 = 𝟙 (V 1) := by
  rw [AddEquiv.apply_symm_apply]
  rfl

example : (homCochainPiEquiv P Q (-1)) degreeMinusOne 0 = secondCoordinate := by
  rw [AddEquiv.apply_symm_apply]
  rfl

example : (degreeMinusTwo.v 1 (-1) (by omega)).hom
    (fun _ : Fin 1 => (4 : ℤ)) (0 : Fin 1) = 4 := by
  rw [homCochainPiEquiv_symm_v]
  rfl

example : (degreeMinusOne.v 0 (-1) (by omega)).hom
    (fun i : Fin 2 => if i = 0 then (3 : ℤ) else 5) (0 : Fin 1) = 5 := by
  rw [homCochainPiEquiv_symm_v]
  rfl

private lemma degreeMinusTwo_one_heq :
    HEq (degreeMinusTwo.v 1 (-1) (by omega)) (𝟙 (V 1)) := by
  have h := homCochainPiEquiv_symm_v P Q (-2) degreeMinusTwoFamily 1 (-1) (by omega)
  have h' := comp_XIsoOfEq_heq (K := Q) (by omega : (1 : ℤ) + (-2) = -1)
    (degreeMinusTwoFamily 1)
  have hf : HEq (degreeMinusTwoFamily 1) (𝟙 (V 1)) := by
    simp only [degreeMinusTwoFamily, dite_eq_left]
    rfl
  exact (heq_of_eq h).trans (h'.trans hf)

private lemma degreeMinusTwo_two_heq :
    HEq (degreeMinusTwo.v 2 0 (by omega)) (0 : V 0 ⟶ V 1) := by
  have h := homCochainPiEquiv_symm_v P Q (-2) degreeMinusTwoFamily 2 0 (by omega)
  have h' := comp_XIsoOfEq_heq (K := Q) (by omega : (2 : ℤ) + (-2) = 0)
    (degreeMinusTwoFamily 2)
  have hf : degreeMinusTwoFamily 2 = 0 := dite_eq_right (by decide : (2 : ℤ) ≠ 1)
  have hz := zeroHom_heq
    (p_coordinate (i := -2) (n := 0) (by norm_num [chainRank]))
    (q_coordinate (i := 0) (n := 1) (by norm_num [coefficientRank]))
  exact (heq_of_eq h).trans (h'.trans ((heq_of_eq hf).trans hz))

private lemma degreeMinusTwo_zero_heq :
    HEq (degreeMinusTwo.v 0 (-2) (by omega)) (0 : V 2 ⟶ V 0) := by
  have h := homCochainPiEquiv_symm_v P Q (-2) degreeMinusTwoFamily 0 (-2) (by omega)
  have h' := comp_XIsoOfEq_heq (K := Q) (by omega : (0 : ℤ) + (-2) = -2)
    (degreeMinusTwoFamily 0)
  have hf : degreeMinusTwoFamily 0 = 0 := dite_eq_right (by decide : (0 : ℤ) ≠ 1)
  have hz := zeroHom_heq
    (p_coordinate (i := 0) (n := 2) (by norm_num [chainRank]))
    (q_coordinate (i := -2) (n := 0) (by norm_num [coefficientRank]))
  exact (heq_of_eq h).trans (h'.trans ((heq_of_eq hf).trans hz))

private lemma degreeMinusOne_one_heq :
    HEq (degreeMinusOne.v 1 0 (by omega)) (𝟙 (V 1)) := by
  have h := homCochainPiEquiv_symm_v P Q (-1) degreeMinusOneFamily 1 0 (by omega)
  have h' := comp_XIsoOfEq_heq (K := Q) (by omega : (1 : ℤ) + (-1) = 0)
    (degreeMinusOneFamily 1)
  have hf : HEq (degreeMinusOneFamily 1) (𝟙 (V 1)) := by
    simp only [degreeMinusOneFamily, dite_eq_left]
    rfl
  exact (heq_of_eq h).trans (h'.trans hf)

private lemma degreeMinusOne_zero_heq :
    HEq (degreeMinusOne.v 0 (-1) (by omega)) secondCoordinate := by
  have h := homCochainPiEquiv_symm_v P Q (-1) degreeMinusOneFamily 0 (-1) (by omega)
  have h' := comp_XIsoOfEq_heq (K := Q) (by omega : (0 : ℤ) + (-1) = -1)
    (degreeMinusOneFamily 0)
  have hf : HEq (degreeMinusOneFamily 0) secondCoordinate := by
    simp only [degreeMinusOneFamily, dite_eq_right (by decide : (0 : ℤ) ≠ 1),
      dite_eq_left]
    rfl
  exact (heq_of_eq h).trans (h'.trans hf)

private lemma reindexed_d_zero_one_heq :
    HEq (((cochainComplexEquivalence (ModuleCat.{0} ℤ)).functor.obj P).d 0 1)
      twiceFirst := by
  have h := heq_of_eq (reindexedP_d 0 1)
  have h' := chainDifferential_heq (K := P) (by omega : -(0 : ℤ) = 0)
    (rfl : -(1 : ℤ) = -1)
  exact h.trans (h'.trans (heq_of_eq p_d_zero_neg_one))

private lemma reindexed_d_one_two_heq :
    HEq (((cochainComplexEquivalence (ModuleCat.{0} ℤ)).functor.obj P).d 1 2)
      (0 : V 1 ⟶ V 0) := by
  have h := heq_of_eq (reindexedP_d 1 2)
  have hp := heq_of_eq p_d_neg_one_neg_two
  have hz := zeroHom_heq
    (p_coordinate (i := -1) (n := 1) (by norm_num [chainRank]))
    (p_coordinate (i := -2) (n := 0) (by norm_num [chainRank]))
  exact h.trans (hp.trans hz)

example :
    ((((homCochainComplex P Q).d (-2) (-1)).hom degreeMinusTwo).v
      1 0 (by omega)).hom (fun _ : Fin 1 => (4 : ℤ)) (0 : Fin 1) = -8 := by
  let K := (cochainComplexEquivalence (ModuleCat.{0} ℤ)).functor.obj P
  let f := (((homCochainComplex P Q).d (-2) (-1)).hom degreeMinusTwo).v 1 0 (by omega)
  let dP := K.d 1 (1 + 1)
  let zB := degreeMinusTwo.v (1 + 1) 0 (by omega)
  let zD := degreeMinusTwo.v 1 (0 - 1) (by omega)
  let dQ := Q.d (0 - 1) 0
  have hA : K.X 1 = V 1 :=
    reindexedP_coordinate (by norm_num [chainRank])
  have hB : K.X (1 + 1) = V 0 :=
    reindexedP_coordinate (by norm_num [chainRank])
  have hC : Q.X 0 = V 1 := q_coordinate (by norm_num [coefficientRank])
  have hD : Q.X (0 - 1) = V 1 :=
    q_coordinate (by norm_num [coefficientRank])
  let eA := eqToIso hA
  let eB := eqToIso hB
  let eC := eqToIso hC
  let eD := eqToIso hD
  have hdP : HEq dP ((0 : V 1 ⟶ V 0)) := by
    exact (differential_heq (K := K) rfl (by omega : (1 : ℤ) + 1 = 2)).trans
      reindexed_d_one_two_heq
  have hzB : HEq zB ((0 : V 0 ⟶ V 1)) := by
    exact (cochainComponent_heq degreeMinusTwo (by omega : (1 : ℤ) + 1 = 2)
      rfl (by omega) (by omega)).trans degreeMinusTwo_two_heq
  have hzD : HEq zD (𝟙 (V 1)) := by
    exact (cochainComponent_heq degreeMinusTwo rfl
      (by omega : (0 : ℤ) - 1 = -1) (by omega) (by omega)).trans degreeMinusTwo_one_heq
  have hdQ : HEq dQ ((2 : ℤ) • 𝟙 (V 1)) := by
    exact (differential_heq (K := Q) (by omega : (0 : ℤ) - 1 = -1) rfl).trans
      q_d_neg_one_zero_heq
  have hdPcoord : eA.inv ≫ dP ≫ eB.hom = (0 : V 1 ⟶ V 0) :=
    transportHom_eq_of_heq hA hB dP ((0 : V 1 ⟶ V 0)) hdP
  have hzBcoord : eB.inv ≫ zB ≫ eC.hom = (0 : V 0 ⟶ V 1) :=
    transportHom_eq_of_heq hB hC zB ((0 : V 0 ⟶ V 1)) hzB
  have hzDcoord : eA.inv ≫ zD ≫ eD.hom = 𝟙 (V 1) :=
    transportHom_eq_of_heq hA hD zD (𝟙 (V 1)) hzD
  have hdQcoord : eD.inv ≫ dQ ≫ eC.hom = (2 : ℤ) • 𝟙 (V 1) :=
    transportHom_eq_of_heq hD hC dQ ((2 : ℤ) • 𝟙 (V 1)) hdQ
  have hcoords : eA.inv ≫ f ≫ eC.hom =
      (eA.inv ≫ dP ≫ eB.hom) ≫ (eB.inv ≫ zB ≫ eC.hom) +
        ((-1) : ℤ).negOnePow •
          ((eA.inv ≫ zD ≫ eD.hom) ≫ (eD.inv ≫ dQ ≫ eC.hom)) :=
    (congrArg (fun a : K.X 1 ⟶ Q.X 0 => eA.inv ≫ a ≫ eC.hom)
      (homCochainComplex_d_v P Q (-2) (-1) (by omega) degreeMinusTwo 1 0 (by omega))).trans
        (transportHom_sum_comp eA eB eC eD dP zB zD dQ ((-1) : ℤ).negOnePow)
  have hfunction : (⇑((eA.inv ≫ f ≫ eC.hom).hom)) = (⇑f.hom) :=
    eq_of_heq (transportHom_function_heq hA hC f)
  calc
    f.hom (fun _ : Fin 1 => (4 : ℤ)) (0 : Fin 1) =
        (eA.inv ≫ f ≫ eC.hom).hom (fun _ : Fin 1 => (4 : ℤ)) (0 : Fin 1) :=
      (congrFun (congrFun hfunction (fun _ : Fin 1 => (4 : ℤ))) (0 : Fin 1)).symm
    _ = -8 := by
      rw [hcoords, hdPcoord, hzBcoord, hzDcoord, hdQcoord]
      norm_num [ModuleCat.hom_comp, ModuleCat.hom_add, ModuleCat.hom_zsmul,
        ModuleCat.hom_neg, ModuleCat.hom_zero, ModuleCat.hom_id, ModuleCat.hom_ofHom,
        twiceFirst, secondCoordinate, LinearMap.comp_apply, LinearMap.add_apply,
        LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply,
        Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.neg_apply, smul_eq_mul]
      rfl

example :
    ((((homCochainComplex P Q).d (-2) (-1)).hom degreeMinusTwo).v
      0 (-1) (by omega)).hom
        (fun i : Fin 2 => if i = 0 then (3 : ℤ) else 5) (0 : Fin 1) = 6 := by
  let K := (cochainComplexEquivalence (ModuleCat.{0} ℤ)).functor.obj P
  let f := (((homCochainComplex P Q).d (-2) (-1)).hom degreeMinusTwo).v 0 (-1) (by omega)
  let dP := K.d 0 (0 + 1)
  let zB := degreeMinusTwo.v (0 + 1) (-1) (by omega)
  let zD := degreeMinusTwo.v 0 ((-1) - 1) (by omega)
  let dQ := Q.d ((-1) - 1) (-1)
  have hA : K.X 0 = V 2 :=
    reindexedP_coordinate (by norm_num [chainRank])
  have hB : K.X (0 + 1) = V 1 :=
    reindexedP_coordinate (by norm_num [chainRank])
  have hC : Q.X (-1) = V 1 := q_coordinate (by norm_num [coefficientRank])
  have hD : Q.X ((-1) - 1) = V 0 :=
    q_coordinate (by norm_num [coefficientRank])
  let eA := eqToIso hA
  let eB := eqToIso hB
  let eC := eqToIso hC
  let eD := eqToIso hD
  have hdP : HEq dP (twiceFirst) := by
    exact (differential_heq (K := K) rfl (by omega : (0 : ℤ) + 1 = 1)).trans
      reindexed_d_zero_one_heq
  have hzB : HEq zB (𝟙 (V 1)) := by
    exact (cochainComponent_heq degreeMinusTwo (by omega : (0 : ℤ) + 1 = 1)
      rfl (by omega) (by omega)).trans degreeMinusTwo_one_heq
  have hzD : HEq zD ((0 : V 2 ⟶ V 0)) := by
    exact (cochainComponent_heq degreeMinusTwo rfl
      (by omega : (-1 : ℤ) - 1 = -2) (by omega) (by omega)).trans degreeMinusTwo_zero_heq
  have hdQ : HEq dQ ((0 : V 0 ⟶ V 1)) := by
    have hz := (heq_of_eq q_d_neg_two_neg_one).trans (zeroHom_heq
      (q_coordinate (i := -2) (n := 0) (by norm_num [coefficientRank]))
      (q_coordinate (i := -1) (n := 1) (by norm_num [coefficientRank])))
    exact (differential_heq (K := Q) (by omega : (-1 : ℤ) - 1 = -2) rfl).trans hz
  have hdPcoord : eA.inv ≫ dP ≫ eB.hom = twiceFirst :=
    transportHom_eq_of_heq hA hB dP (twiceFirst) hdP
  have hzBcoord : eB.inv ≫ zB ≫ eC.hom = 𝟙 (V 1) :=
    transportHom_eq_of_heq hB hC zB (𝟙 (V 1)) hzB
  have hzDcoord : eA.inv ≫ zD ≫ eD.hom = (0 : V 2 ⟶ V 0) :=
    transportHom_eq_of_heq hA hD zD ((0 : V 2 ⟶ V 0)) hzD
  have hdQcoord : eD.inv ≫ dQ ≫ eC.hom = (0 : V 0 ⟶ V 1) :=
    transportHom_eq_of_heq hD hC dQ ((0 : V 0 ⟶ V 1)) hdQ
  have hcoords : eA.inv ≫ f ≫ eC.hom =
      (eA.inv ≫ dP ≫ eB.hom) ≫ (eB.inv ≫ zB ≫ eC.hom) +
        ((-1) : ℤ).negOnePow •
          ((eA.inv ≫ zD ≫ eD.hom) ≫ (eD.inv ≫ dQ ≫ eC.hom)) :=
    (congrArg (fun a : K.X 0 ⟶ Q.X (-1) => eA.inv ≫ a ≫ eC.hom)
      (homCochainComplex_d_v P Q (-2) (-1) (by omega) degreeMinusTwo 0 (-1) (by omega))).trans
        (transportHom_sum_comp eA eB eC eD dP zB zD dQ ((-1) : ℤ).negOnePow)
  have hfunction : (⇑((eA.inv ≫ f ≫ eC.hom).hom)) = (⇑f.hom) :=
    eq_of_heq (transportHom_function_heq hA hC f)
  calc
    f.hom (fun i : Fin 2 => if i = 0 then (3 : ℤ) else 5) (0 : Fin 1) =
        (eA.inv ≫ f ≫ eC.hom).hom (fun i : Fin 2 => if i = 0 then (3 : ℤ) else 5) (0 : Fin 1) :=
      (congrFun (congrFun hfunction (fun i : Fin 2 => if i = 0 then (3 : ℤ) else 5)) (0 : Fin 1)).symm
    _ = 6 := by
      rw [hcoords, hdPcoord, hzBcoord, hzDcoord, hdQcoord]
      norm_num [ModuleCat.hom_comp, ModuleCat.hom_add, ModuleCat.hom_zsmul,
        ModuleCat.hom_neg, ModuleCat.hom_zero, ModuleCat.hom_id, ModuleCat.hom_ofHom,
        twiceFirst, secondCoordinate, LinearMap.comp_apply, LinearMap.add_apply,
        LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply,
        Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.neg_apply, smul_eq_mul]

example :
    ((((homCochainComplex P Q).d (-1) 0).hom degreeMinusOne).v
      0 0 (by omega)).hom
        (fun i : Fin 2 => if i = 0 then (3 : ℤ) else 5) (0 : Fin 1) = 16 := by
  let K := (cochainComplexEquivalence (ModuleCat.{0} ℤ)).functor.obj P
  let f := (((homCochainComplex P Q).d (-1) 0).hom degreeMinusOne).v 0 0 (by omega)
  let dP := K.d 0 (0 + 1)
  let zB := degreeMinusOne.v (0 + 1) 0 (by omega)
  let zD := degreeMinusOne.v 0 (0 - 1) (by omega)
  let dQ := Q.d (0 - 1) 0
  have hA : K.X 0 = V 2 :=
    reindexedP_coordinate (by norm_num [chainRank])
  have hB : K.X (0 + 1) = V 1 :=
    reindexedP_coordinate (by norm_num [chainRank])
  have hC : Q.X 0 = V 1 := q_coordinate (by norm_num [coefficientRank])
  have hD : Q.X (0 - 1) = V 1 :=
    q_coordinate (by norm_num [coefficientRank])
  let eA := eqToIso hA
  let eB := eqToIso hB
  let eC := eqToIso hC
  let eD := eqToIso hD
  have hdP : HEq dP (twiceFirst) := by
    exact (differential_heq (K := K) rfl (by omega : (0 : ℤ) + 1 = 1)).trans
      reindexed_d_zero_one_heq
  have hzB : HEq zB (𝟙 (V 1)) := by
    exact (cochainComponent_heq degreeMinusOne (by omega : (0 : ℤ) + 1 = 1)
      rfl (by omega) (by omega)).trans degreeMinusOne_one_heq
  have hzD : HEq zD (secondCoordinate) := by
    exact (cochainComponent_heq degreeMinusOne rfl
      (by omega : (0 : ℤ) - 1 = -1) (by omega) (by omega)).trans degreeMinusOne_zero_heq
  have hdQ : HEq dQ ((2 : ℤ) • 𝟙 (V 1)) := by
    exact (differential_heq (K := Q) (by omega : (0 : ℤ) - 1 = -1) rfl).trans
      q_d_neg_one_zero_heq
  have hdPcoord : eA.inv ≫ dP ≫ eB.hom = twiceFirst :=
    transportHom_eq_of_heq hA hB dP (twiceFirst) hdP
  have hzBcoord : eB.inv ≫ zB ≫ eC.hom = 𝟙 (V 1) :=
    transportHom_eq_of_heq hB hC zB (𝟙 (V 1)) hzB
  have hzDcoord : eA.inv ≫ zD ≫ eD.hom = secondCoordinate :=
    transportHom_eq_of_heq hA hD zD (secondCoordinate) hzD
  have hdQcoord : eD.inv ≫ dQ ≫ eC.hom = (2 : ℤ) • 𝟙 (V 1) :=
    transportHom_eq_of_heq hD hC dQ ((2 : ℤ) • 𝟙 (V 1)) hdQ
  have hcoords : eA.inv ≫ f ≫ eC.hom =
      (eA.inv ≫ dP ≫ eB.hom) ≫ (eB.inv ≫ zB ≫ eC.hom) +
        (0 : ℤ).negOnePow •
          ((eA.inv ≫ zD ≫ eD.hom) ≫ (eD.inv ≫ dQ ≫ eC.hom)) :=
    (congrArg (fun a : K.X 0 ⟶ Q.X 0 => eA.inv ≫ a ≫ eC.hom)
      (homCochainComplex_d_v P Q (-1) 0 (by omega) degreeMinusOne 0 0 (by omega))).trans
        (transportHom_sum_comp eA eB eC eD dP zB zD dQ (0 : ℤ).negOnePow)
  have hfunction : (⇑((eA.inv ≫ f ≫ eC.hom).hom)) = (⇑f.hom) :=
    eq_of_heq (transportHom_function_heq hA hC f)
  calc
    f.hom (fun i : Fin 2 => if i = 0 then (3 : ℤ) else 5) (0 : Fin 1) =
        (eA.inv ≫ f ≫ eC.hom).hom (fun i : Fin 2 => if i = 0 then (3 : ℤ) else 5) (0 : Fin 1) :=
      (congrFun (congrFun hfunction (fun i : Fin 2 => if i = 0 then (3 : ℤ) else 5)) (0 : Fin 1)).symm
    _ = 16 := by
      rw [hcoords, hdPcoord, hzBcoord, hzDcoord, hdQcoord]
      norm_num [ModuleCat.hom_comp, ModuleCat.hom_add, ModuleCat.hom_zsmul,
        ModuleCat.hom_neg, ModuleCat.hom_zero, ModuleCat.hom_id, ModuleCat.hom_ofHom,
        twiceFirst, secondCoordinate, LinearMap.comp_apply, LinearMap.add_apply,
        LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply,
        Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.neg_apply, smul_eq_mul]

example : UCT.ShortExact :=
  homUniversalCoefficientSequence_shortExact P Q 0 projectiveTerms projectiveImages

example :
    letI := HasExt.standard (ModuleCat.{0} ℤ)
    UCT.X₁ = AddCommGrpCat.of
      (∀ p : ℤ, Ext.{1} (P.homology p) (Q.homology (-1 - p)) 1) := rfl

example : UCT.X₂ =
    AddCommGrpCat.uliftFunctor.{1, 0}.obj ((homCochainComplex P Q).homology 0) := rfl

example : UCT.X₃ = AddCommGrpCat.uliftFunctor.{1, 0}.obj
    (AddCommGrpCat.of (∀ p : ℤ, P.homology p ⟶ Q.homology (0 - p))) := rfl

example :
    (AddCommGrpCat.uliftIntPiIso.{0, 1} (fun _ : ℤ => AddCommGrpCat.of ℤ)).hom
      (ULift.up (fun p : ℤ => p)) (-3) = ULift.up (-3 : ℤ) := rfl

private abbrev sourceMap : P ⟶ P := (3 : ℤ) • 𝟙 P

private abbrev coefficientMap : Q ⟶ Q := (-1 : ℤ) • 𝟙 Q

private lemma reindexedSourceMap_f (i : ℤ) :
    ((cochainComplexEquivalence (ModuleCat.{0} ℤ)).functor.map sourceMap).f i =
      (3 : ℤ) • 𝟙 (P.X (-i)) := rfl

private lemma coefficientMap_f (i : ℤ) :
    coefficientMap.f i = (-1 : ℤ) • 𝟙 (Q.X i) := rfl

example :
    ((((homCochainComplexMap sourceMap coefficientMap).f (-1)).hom degreeMinusOne).v
      0 (-1) (by omega)).hom
        (fun i : Fin 2 => if i = 0 then (3 : ℤ) else 5) (0 : Fin 1) = -15 := by
  let K := (cochainComplexEquivalence (ModuleCat.{0} ℤ)).functor.obj P
  let f := (((homCochainComplexMap sourceMap coefficientMap).f (-1)).hom degreeMinusOne).v
    0 (-1) (by omega)
  let a := ((cochainComplexEquivalence (ModuleCat.{0} ℤ)).functor.map sourceMap).f 0
  let z := degreeMinusOne.v 0 (-1) (by omega)
  let b := coefficientMap.f (-1)
  have hA : K.X 0 = V 2 := reindexedP_coordinate (by norm_num [chainRank])
  have hB : Q.X (-1) = V 1 := q_coordinate (by norm_num [coefficientRank])
  let eA := eqToIso hA
  let eB := eqToIso hB
  have ha : HEq a ((3 : ℤ) • 𝟙 (V 2)) :=
    (heq_of_eq (reindexedSourceMap_f 0)).trans
      (smulId_heq (p_coordinate (i := -0) (n := 2) (by norm_num [chainRank])) 3)
  have hz : HEq z secondCoordinate := degreeMinusOne_zero_heq
  have hb : HEq b ((-1 : ℤ) • 𝟙 (V 1)) :=
    (heq_of_eq (coefficientMap_f (-1))).trans (smulId_heq hB (-1))
  have hacoord : eA.inv ≫ a ≫ eA.hom = (3 : ℤ) • 𝟙 (V 2) :=
    transportHom_eq_of_heq hA hA a ((3 : ℤ) • 𝟙 (V 2)) ha
  have hzcoord : eA.inv ≫ z ≫ eB.hom = secondCoordinate :=
    transportHom_eq_of_heq hA hB z secondCoordinate hz
  have hbcoord : eB.inv ≫ b ≫ eB.hom = (-1 : ℤ) • 𝟙 (V 1) :=
    transportHom_eq_of_heq hB hB b ((-1 : ℤ) • 𝟙 (V 1)) hb
  have hcoords : eA.inv ≫ f ≫ eB.hom =
      (eA.inv ≫ a ≫ eA.hom) ≫ (eA.inv ≫ z ≫ eB.hom) ≫
        (eB.inv ≫ b ≫ eB.hom) :=
    (congrArg (fun k : K.X 0 ⟶ Q.X (-1) => eA.inv ≫ k ≫ eB.hom)
      (homCochainComplexMap_v sourceMap coefficientMap (-1) 0 (-1) (by omega)
        degreeMinusOne)).trans (transportHom_triple_comp eA eB a z b)
  have hfunction : (⇑((eA.inv ≫ f ≫ eB.hom).hom)) = (⇑f.hom) :=
    eq_of_heq (transportHom_function_heq hA hB f)
  calc
    f.hom (fun i : Fin 2 => if i = 0 then (3 : ℤ) else 5) (0 : Fin 1) =
        (eA.inv ≫ f ≫ eB.hom).hom
          (fun i : Fin 2 => if i = 0 then (3 : ℤ) else 5) (0 : Fin 1) :=
      (congrFun (congrFun hfunction
        (fun i : Fin 2 => if i = 0 then (3 : ℤ) else 5)) (0 : Fin 1)).symm
    _ = -15 := by
      rw [hcoords, hacoord, hzcoord, hbcoord]
      norm_num [ModuleCat.hom_comp, ModuleCat.hom_zsmul, ModuleCat.hom_neg,
        ModuleCat.hom_id, ModuleCat.hom_ofHom, secondCoordinate,
        LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
        Pi.smul_apply, Pi.mul_apply, Pi.neg_apply, smul_eq_mul]
      rfl

private abbrev uctMap : UCT ⟶ UCT :=
  homUniversalCoefficientSequenceMap sourceMap coefficientMap 0
    projectiveTerms projectiveImages projectiveTerms projectiveImages

private lemma homologyEndomorphism_heq
    {K : CochainComplex (ModuleCat.{0} ℤ) ℤ} (f : K ⟶ K)
    {i j : ℤ} (h : i = j) :
    HEq (HomologicalComplex.homologyMap f i) (HomologicalComplex.homologyMap f j) := by
  subst j
  rfl

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
  letI : HasExt.{1} (ModuleCat.{0} ℤ) := HasExt.standard (ModuleCat.{0} ℤ)
  have postComp_heq {A B B' : ModuleCat.{0} ℤ} (hB : B = B')
      (x : Ext.{1} A B 1) (y : Ext.{1} A B' 1) (hxy : HEq x y)
      (f : B ⟶ B) (g : B' ⟶ B') (hfg : HEq f g) :
      HEq (x.comp (Ext.mk₀ f) (add_zero 1))
        (y.comp (Ext.mk₀ g) (add_zero 1)) := by
    subst B'
    cases hxy
    cases hfg
    rfl
  have hdegree : (0 : ℤ) - 1 - (-1) = 0 := by omega
  have h := homUniversalCoefficientSequenceMap_τ₁_apply sourceMap coefficientMap 0
    projectiveTerms projectiveImages projectiveTerms projectiveImages e (-1)
  have hobject : Q.homology ((0 : ℤ) - 1 - (-1)) = Q.homology 0 :=
    congrArg (fun j : ℤ => HomologicalComplex.homology Q j) hdegree
  have hmap := homologyEndomorphism_heq coefficientMap hdegree
  have hpost := postComp_heq hobject
    ((Ext.mk₀ (HomologicalComplex.homologyMap sourceMap (-1))).comp (e (-1)) (zero_add 1))
    ((Ext.mk₀ (HomologicalComplex.homologyMap sourceMap (-1))).comp (e (-1)) (zero_add 1))
    HEq.rfl
    (HomologicalComplex.homologyMap coefficientMap ((0 : ℤ) - 1 - (-1)))
    (HomologicalComplex.homologyMap coefficientMap 0) hmap
  exact h.trans (eq_of_heq hpost)

example (k : UCT.X₃) :
    uctMap.τ₃ k = ULift.up (fun p : ℤ =>
      HomologicalComplex.homologyMap sourceMap p ≫ k.down p ≫
        HomologicalComplex.homologyMap coefficientMap (0 - p)) := by
  simpa only [uctMap] using homUniversalCoefficientSequenceMap_τ₃_apply sourceMap coefficientMap 0
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
