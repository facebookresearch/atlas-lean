/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Elasticity.WeakAndVirtualWork
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Elasticity.WeakAndVirtualWork`

* a constant-rigidity bar under a nonzero uniform load: the weak solution has the classical
  midspan displacement;
* a positive two-valued rigidity: the existence theorem applies;
* inadmissible data: zero rigidity under a unit load, and a traction end;
* a constant uniaxial stress on a box: the opposing face tractions, their works, the internal
  virtual work, a wrong normal, the virtual work identity itself, and simple shear.
-/

@[expose] public section

namespace PhyslibExtTest.Elasticity.WeakAndVirtualWork

open scoped Matrix
open MeasureTheory _root_.Elasticity _root_.Elasticity.WeakAndVirtualWork
  _root_.Elasticity.PrismaticMembers

/-! ## A. Constant rigidity -/

-- Nonzero fixture `EA = 2`, `L = 3`, `q = 4`: a weak solution exists and its midspan
-- displacement is the classical `q L ^ 2 / (8 EA) = 9 / 4`.
example :
    ∃ u : WeakH10On 3, IsWeakBarSolution (fun _ => 2) (fun _ => 4) u ∧ u.toFun (3 / 2) = 9 / 4 := by
  obtain ⟨u, hu, -⟩ := weakBar_exists_unique (L := 3) (EA := fun _ => 2) (q := fun _ => 4)
    (EAmin := 2) (EAmax := 2) (by norm_num) (by norm_num) aestronglyMeasurable_const
    (Filter.Eventually.of_forall fun _ => ⟨le_rfl, le_rfl⟩) (memLp_const 4)
  refine ⟨u, hu, ?_⟩
  rw [hu.eqOn_axialDisplacement (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩]
  norm_num [axialDisplacement]

-- Every weak solution of that bar vanishes at both ends.
example (u : WeakH10On 3) (_hu : IsWeakBarSolution (fun _ => 2) (fun _ => 4) u) :
    u.toFun 0 = 0 ∧ u.toFun 3 = 0 :=
  u.toFun_zero_and_length (by norm_num)

/-! ## B. Piecewise constant rigidity -/

-- The rigidity `1` on `x < 1` and `2` on `x ≥ 1`, on a bar of length `2` under the unit load,
-- satisfies the hypotheses of the existence theorem, so a weak solution exists.
example : ∃ u : WeakH10On 2, IsWeakBarSolution (stepRigidity 1 2 1) (fun _ => 1) u := by
  obtain ⟨hpos, hmeas, hbd⟩ := stepRigidity_admissible (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 2) 1 2
  obtain ⟨u, hu, -⟩ := weakBar_exists_unique (by norm_num) hpos hmeas hbd (memLp_const 1)
  exact ⟨u, hu⟩

/-! ## C. Inadmissible data -/

-- Zero rigidity under the unit load on `[0, 2]` has no weak solution.
example (u : WeakH10On 2) : ¬ IsWeakBarSolution (fun _ => 0) (fun _ => 1) u :=
  not_isWeakBarSolution_zero_rigidity (by norm_num) u

-- The negative rigidity `-1 - x` has no positive almost-everywhere lower bound on `[0, 2]`.
example : ¬ ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 2)), (1 : ℝ) ≤ -1 - x ∧ -1 - x ≤ 1 :=
  not_ae_lowerBound_of_nonpos (EA := fun x => -1 - x) (by norm_num)
    (fun _ hx => by linarith [hx.1]) (by norm_num)

-- A traction end: the fixed-free displacement with `EA = 2`, `L = 3`, `q = 4` is represented by
-- no element of `H¹₀(0, 3)`.
example :
    ¬ ∃ v : WeakH10On 3, Set.EqOn v.toFun (fixedFreeDisplacement 2 3 4) (Set.Icc 0 3) :=
  not_exists_weakH10On_eqOn_fixedFree (by norm_num) (by norm_num) (by norm_num)

/-! ## D. Virtual work on a box -/

/-- Fixture box `[1, 3] × [0, 1] × [0, 1]`, lower corner. -/
def fixtureLo : Fin 3 → ℝ := ![1, 0, 0]

/-- Fixture box `[1, 3] × [0, 1] × [0, 1]`, upper corner. -/
def fixtureHi : Fin 3 → ℝ := ![3, 1, 1]

/-- The constant uniaxial stress `diag (3, 0, 0)`. -/
def uniaxialStress : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ :=
  fun _ => Matrix.diagonal ![3, 0, 0]

/-- The virtual displacement `v x = (x₀, 0, 0)`. -/
def uniaxialDisplacement : (Fin 3 → ℝ) → Fin 3 → ℝ :=
  affineDisplacement (Matrix.diagonal ![1, 0, 0]) 0

/-- The fixture box is ordered: `fixtureLo ≤ fixtureHi`. -/
private lemma fixture_le : fixtureLo ≤ fixtureHi := by
  intro i
  fin_cases i <;> simp [fixtureLo, fixtureHi]

/-- The area of the two faces of the fixture box normal to `eᵢ`. -/
private lemma fixture_face_area (i : Fin 3) :
    volume.real (Set.Icc (fixtureLo ∘ i.succAbove) (fixtureHi ∘ i.succAbove)) =
      ∏ k : Fin 2, (fixtureHi (i.succAbove k) - fixtureLo (i.succAbove k)) := by
  rw [Measure.real, Real.volume_Icc_pi_toReal (a := fixtureLo ∘ i.succAbove)
    (b := fixtureHi ∘ i.succAbove) (fun k => fixture_le _)]
  rfl

/-- The face `x₀ = 3` of the fixture box does the work `9`. -/
private lemma fixture_upperFaceWork :
    upperFaceWork fixtureLo fixtureHi uniaxialStress uniaxialDisplacement 0 = 9 := by
  unfold upperFaceWork
  rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => (9 : ℝ)) fun y _ => by
    simp [traction, uniaxialStress, uniaxialDisplacement, affineDisplacement, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, fixtureHi]
    norm_num]
  rw [setIntegral_const, fixture_face_area, Fin.prod_univ_two]
  simp [fixtureLo, fixtureHi]

/-- The internal virtual work of the fixture is `3 · 2 = 6`. -/
private lemma fixture_internalWork :
    ∫ x in Set.Icc fixtureLo fixtureHi, ∑ i, ∑ j, uniaxialStress x i j *
      smallStrain (displacementGradient uniaxialDisplacement x) i j = 6 := by
  have hdG : ∀ x, displacementGradient uniaxialDisplacement x = Matrix.diagonal ![1, 0, 0] :=
    fun x => displacementGradient_affine _ _ x
  have hvol : volume.real (Set.Icc fixtureLo fixtureHi) = 2 := by
    rw [Measure.real, Real.volume_Icc_pi_toReal fixture_le, Fin.prod_univ_three]
    simp [fixtureLo, fixtureHi]
    norm_num
  rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => (3 : ℝ)) fun x _ => by
    simp [hdG, uniaxialStress, smallStrain_apply, Fin.sum_univ_three]]
  rw [setIntegral_const, hvol]
  norm_num

-- A nonzero constant stress with actual opposing face tractions: on the faces `x₀ = 3` and
-- `x₀ = 1` the tractions are `(3, 0, 0)` and `(-3, 0, 0)` and do the works `9` and `-3`; the other
-- four faces do no work; the internal virtual work is `6 = 9 - 3`.
example :
    traction (uniaxialStress 0) (Pi.single 0 1) = ![3, 0, 0] ∧
      traction (uniaxialStress 0) (-Pi.single 0 1) = ![-3, 0, 0] ∧
      upperFaceWork fixtureLo fixtureHi uniaxialStress uniaxialDisplacement 0 = 9 ∧
      lowerFaceWork fixtureLo fixtureHi uniaxialStress uniaxialDisplacement 0 = -3 ∧
      (∀ i ≠ 0, upperFaceWork fixtureLo fixtureHi uniaxialStress uniaxialDisplacement i = 0 ∧
        lowerFaceWork fixtureLo fixtureHi uniaxialStress uniaxialDisplacement i = 0) ∧
      ∫ x in Set.Icc fixtureLo fixtureHi, ∑ i, ∑ j, uniaxialStress x i j *
          smallStrain (displacementGradient uniaxialDisplacement x) i j = 6 ∧
      boxTractionWork fixtureLo fixtureHi uniaxialStress uniaxialDisplacement = 6 := by
  have hL0 : lowerFaceWork fixtureLo fixtureHi uniaxialStress uniaxialDisplacement 0 = -3 := by
    unfold lowerFaceWork
    rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => (-3 : ℝ)) fun y _ => by
      simp [traction, uniaxialStress, uniaxialDisplacement, affineDisplacement, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three, fixtureLo]]
    rw [setIntegral_const, fixture_face_area, Fin.prod_univ_two]
    simp [fixtureLo, fixtureHi]
  have hother : ∀ i ≠ (0 : Fin 3),
      upperFaceWork fixtureLo fixtureHi uniaxialStress uniaxialDisplacement i = 0 ∧
        lowerFaceWork fixtureLo fixtureHi uniaxialStress uniaxialDisplacement i = 0 := by
    intro i hi
    have htr : ∀ z : Fin 3 → ℝ, ∀ s : ℝ,
        traction (uniaxialStress z) (s • Pi.single i 1) = 0 := by
      intro z s
      fin_cases i
      · exact absurd rfl hi
      · ext k; fin_cases k <;> simp [traction, uniaxialStress, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three]
      · ext k; fin_cases k <;> simp [traction, uniaxialStress, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three]
    constructor
    · unfold upperFaceWork
      have := htr 0 1
      simp only [one_smul] at this
      simp [uniaxialStress, this] at *
    · unfold lowerFaceWork
      have := htr 0 (-1)
      simp only [neg_one_smul] at this
      simp [uniaxialStress, this] at *
  refine ⟨?_, ?_, fixture_upperFaceWork, hL0, hother, fixture_internalWork, ?_⟩
  · ext k; fin_cases k <;> simp [traction, uniaxialStress, Matrix.mulVec, dotProduct,
      Matrix.diagonal_apply, Pi.single_apply]
  · ext k; fin_cases k <;> simp [traction, uniaxialStress, Matrix.mulVec, dotProduct,
      Matrix.diagonal_apply, Pi.single_apply]
  · rw [boxTractionWork, Fin.sum_univ_three, fixture_upperFaceWork, hL0, (hother 1 (by decide)).1,
      (hother 1 (by decide)).2, (hother 2 (by decide)).1, (hother 2 (by decide)).2]
    norm_num

-- A wrong normal gives a wrong work term: with the inward normal `+e₀` on the face `x₀ = 1`
-- its work is `3` instead of `-3`, so, the other four faces doing no work, the face sum would be
-- `9 + 3 = 12`, not the internal virtual work `6`.
example :
    upperFaceWork fixtureLo fixtureHi uniaxialStress uniaxialDisplacement 0 +
        (∫ y in Set.Icc (fixtureLo ∘ (0 : Fin 3).succAbove) (fixtureHi ∘ (0 : Fin 3).succAbove),
          traction (uniaxialStress ((0 : Fin 3).insertNth (fixtureLo 0) y)) (Pi.single 0 1) ⬝ᵥ
            uniaxialDisplacement ((0 : Fin 3).insertNth (fixtureLo 0) y)) = 12 ∧
      (12 : ℝ) ≠ ∫ x in Set.Icc fixtureLo fixtureHi, ∑ i, ∑ j, uniaxialStress x i j *
          smallStrain (displacementGradient uniaxialDisplacement x) i j := by
  have hin :
      (∫ y in Set.Icc (fixtureLo ∘ (0 : Fin 3).succAbove) (fixtureHi ∘ (0 : Fin 3).succAbove),
      traction (uniaxialStress ((0 : Fin 3).insertNth (fixtureLo 0) y)) (Pi.single 0 1) ⬝ᵥ
        uniaxialDisplacement ((0 : Fin 3).insertNth (fixtureLo 0) y)) = 3 := by
    rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => (3 : ℝ)) fun y _ => by
      simp [traction, uniaxialStress, uniaxialDisplacement, affineDisplacement, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three, fixtureLo]]
    rw [setIntegral_const, fixture_face_area, Fin.prod_univ_two]
    simp [fixtureLo, fixtureHi]
  rw [fixture_upperFaceWork, hin, fixture_internalWork]
  norm_num

-- The identity applies to the fixture with zero body force: the internal virtual work equals
-- the face sum.
example :
    ∫ x in Set.Icc fixtureLo fixtureHi, ∑ i, ∑ j, uniaxialStress x i j *
        smallStrain (displacementGradient uniaxialDisplacement x) i j =
      (∫ x in Set.Icc fixtureLo fixtureHi, (0 : Fin 3 → ℝ) ⬝ᵥ uniaxialDisplacement x) +
        boxTractionWork fixtureLo fixtureHi uniaxialStress uniaxialDisplacement := by
  refine virtualWork_box (U := Set.univ) (body := fun _ => 0) (fun i => ?_) isOpen_univ
    (Set.subset_univ _) (fun i j => contDiffOn_const) (fun x _ => Matrix.diagonal_transpose _)
    ?_ (fun x _ => ?_)
  · fin_cases i <;> simp [fixtureLo, fixtureHi]
  · refine (contDiff_pi.2 fun i => ?_).contDiffOn
    simp only [uniaxialDisplacement, affineDisplacement]
    fun_prop
  · ext i
    simp [stressDivergence, MathlibExt.Probability.FokkerPlanck.divergence,
      MathlibExt.Probability.FokkerPlanck.pderiv, uniaxialStress]

-- Simple shear with `τ = 1` and `γ = 2`: the virtual work density is `τ γ = 2`, while the
-- double-counted engineering contraction is `4`.
example (x : Fin 3 → ℝ) :
    ∑ i, ∑ j, simpleShearStress 1 i j *
        smallStrain (displacementGradient (simpleShearField 2) x) i j = 1 * 2 ∧
      2 * (1 * 2 : ℝ) ≠ 1 * 2 :=
  ⟨(simpleShear_engineering_double_count one_ne_zero two_ne_zero x).1,
    (simpleShear_engineering_double_count one_ne_zero two_ne_zero x).2.2⟩

end PhyslibExtTest.Elasticity.WeakAndVirtualWork

end
