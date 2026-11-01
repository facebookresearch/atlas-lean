/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortSpinDictionary
/-! The concrete Parker theta addition law.

The published XOR-mask formula is a quadratic polynomial in the twelve
Golay coefficients. Its polarization is the cocode syndrome of the pointwise
intersection of the encoded words. The proof checks the finite basis data
and then uses algebraic expansion for arbitrary coefficient vectors.
Source: Seysen, arXiv:2002.10921v3, §3.1 and Theorem 6.1. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
-- The published associator mask is presented as a matrix abbreviation.
set_option backward.isDefEq.respectTransparency false
/-- The Parker theta coordinates for arbitrary binary coefficient vectors. -/
def sourceCodeThetaPolynomial (a : Fin 12 → ZMod 2) (k : Fin 12) : ZMod 2 :=
  (∑ j, a j * sourceCodeTheta j k) +
    ∑ i, ∑ j, if i < j then
      a i * a j * golayBooleanCast ((parkerBasisAssociatorMasks i j).testBit k.val) else 0

/-- XOR folds become sums in F₂, for arbitrary masks. -/
theorem sourceMaskFold_sum {ι : Type*} (xs : List ι) (f : ι → ℕ) (m n : ℕ) :
    golayBooleanCast ((xs.foldl (fun b i => b ^^^ f i) m).testBit n) =
      golayBooleanCast (m.testBit n) +
        (xs.map (fun i => golayBooleanCast ((f i).testBit n))).sum := by
  induction xs generalizing m with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_xor, golayBooleanCast_xor,
      List.map_cons, List.sum_cons, add_assoc]

theorem sourceNestedMaskFold_sum {ι κ : Type*} (xs : List ι) (ys : List κ)
    (f : ι → κ → ℕ) (m n : ℕ) :
    golayBooleanCast ((xs.foldl (fun b i => ys.foldl (fun c j => c ^^^ f i j) b) m).testBit n) =
      golayBooleanCast (m.testBit n) +
        (xs.map (fun i => (ys.map (fun j => golayBooleanCast ((f i j).testBit n))).sum)).sum := by
  induction xs generalizing m with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldl_cons, ih, sourceMaskFold_sum, List.map_cons, List.sum_cons,
      add_assoc]

/-- The published mask implementation is exactly the quadratic theta polynomial.
This proof works for all labels by induction on the XOR folds. -/
theorem sourceCodeThetaPolynomial_mask (d : Fin 4096) (k : Fin 12) :
    golayBooleanCast ((parkerThetaMask d.val).testBit k.val) =
      sourceCodeThetaPolynomial (golayLabelCoefficients d) k := by
  unfold parkerThetaMask
  rw [sourceMaskFold_sum, sourceNestedMaskFold_sum]
  simp only [List.finRange, List.map_ofFn, List.sum_ofFn, Nat.zero_testBit,
    show golayBooleanCast false = 0 by rfl, zero_add, Function.comp_def]
  unfold sourceCodeThetaPolynomial
  have hlinear : (∑ j : Fin 12, golayBooleanCast
      ((if d.val.testBit j.val then parkerBasisThetaMasks j else 0).testBit k.val)) =
      ∑ j, golayLabelCoefficients d j * sourceCodeTheta j k := by
    apply Finset.sum_congr rfl
    intro j _
    cases hb : d.val.testBit j.val <;>
      simp [hb, golayBooleanCast, golayLabelCoefficients, sourceCodeTheta]
  have hquad : (∑ i : Fin 12, ∑ j : Fin 12, golayBooleanCast
        ((if i < j ∧ d.val.testBit i.val ∧ d.val.testBit j.val then
          parkerBasisAssociatorMasks i j else 0).testBit k.val)) =
      ∑ i, ∑ j, if i < j then golayLabelCoefficients d i * golayLabelCoefficients d j *
        golayBooleanCast ((parkerBasisAssociatorMasks i j).testBit k.val) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i < j <;> cases hi : d.val.testBit i.val <;>
      cases hj : d.val.testBit j.val <;>
      simp [hij, hi, hj, golayBooleanCast, golayLabelCoefficients]
  rw [hquad]
  rw [hlinear]
  exact add_comm _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Certify only the 1728 basis triples, each a 24-coordinate binary sum.
lemma parkerAssociator_syndrome_basis : ∀ i j k : Fin 12,
    golayBooleanCast ((parkerBasisAssociatorMasks i j).testBit k.val) =
      ∑ t : Fin 24, (golayGeneratorBit i t : ZMod 2) *
        (golayGeneratorBit j t : ZMod 2) * (golayGeneratorBit k t : ZMod 2) := by
  decide +kernel

lemma sourceCodeThetaPolynomial_add_cross (a b : Fin 12 → ZMod 2) (k : Fin 12) :
    sourceCodeThetaPolynomial (a + b) k = sourceCodeThetaPolynomial a k +
      sourceCodeThetaPolynomial b k +
      ∑ i, ∑ j, if i < j then (a i * b j + b i * a j) *
        golayBooleanCast ((parkerBasisAssociatorMasks i j).testBit k.val) else 0 := by
  unfold sourceCodeThetaPolynomial
  simp only [Pi.add_apply]
  rw [show (∑ j, (a j + b j) * sourceCodeTheta j k) =
    (∑ j, a j * sourceCodeTheta j k) + (∑ j, b j * sourceCodeTheta j k) by
      simp only [add_mul, Finset.sum_add_distrib]]
  have h : (∑ i, ∑ j, if i < j then
      (a i + b i) * (a j + b j) *
        golayBooleanCast ((parkerBasisAssociatorMasks i j).testBit k.val) else 0) =
      (∑ i, ∑ j, if i < j then a i * a j *
        golayBooleanCast ((parkerBasisAssociatorMasks i j).testBit k.val) else 0) +
      (∑ i, ∑ j, if i < j then b i * b j *
        golayBooleanCast ((parkerBasisAssociatorMasks i j).testBit k.val) else 0) +
      ∑ i, ∑ j, if i < j then (a i * b j + b i * a j) *
        golayBooleanCast ((parkerBasisAssociatorMasks i j).testBit k.val) else 0 := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [h]
  ring

lemma parkerAssociator_symmetric (i j k : Fin 12) :
    golayBooleanCast ((parkerBasisAssociatorMasks i j).testBit k.val) =
      golayBooleanCast ((parkerBasisAssociatorMasks j i).testBit k.val) := by
  rw [parkerAssociator_syndrome_basis, parkerAssociator_syndrome_basis]
  apply Finset.sum_congr rfl
  intro t _
  ring

lemma parkerAssociator_diagonal (i k : Fin 12) :
    golayBooleanCast ((parkerBasisAssociatorMasks i i).testBit k.val) = 0 := by
  fin_cases i <;> fin_cases k <;> decide

lemma sourceCodeIntersection_syndrome_expansion (a b : Fin 12 → ZMod 2) (k : Fin 12) :
    golaySyndrome (fun t => golayEncoder a t * golayEncoder b t) k =
      ∑ i, ∑ j, a i * b j *
        golayBooleanCast ((parkerBasisAssociatorMasks i j).testBit k.val) := by
  simp only [golaySyndrome, golayEncoder, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [parkerAssociator_syndrome_basis, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

lemma sourceCodeTheta_cross_eq_syndrome (a b : Fin 12 → ZMod 2) (k : Fin 12) :
    (∑ i, ∑ j, if i < j then (a i * b j + b i * a j) *
      golayBooleanCast ((parkerBasisAssociatorMasks i j).testBit k.val) else 0) =
    golaySyndrome (fun t => golayEncoder a t * golayEncoder b t) k := by
  rw [sourceCodeIntersection_syndrome_expansion]
  have hterm (i j : Fin 12) :
      a i * b j * golayBooleanCast ((parkerBasisAssociatorMasks i j).testBit k.val) =
      (if i < j then a i * b j *
        golayBooleanCast ((parkerBasisAssociatorMasks i j).testBit k.val) else 0) +
      (if j < i then a i * b j *
        golayBooleanCast ((parkerBasisAssociatorMasks i j).testBit k.val) else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt_of_gt h]
    · simp [parkerAssociator_diagonal]
    · simp [h, not_lt_of_gt h]
  have hsum : (∑ i, ∑ j, a i * b j *
      golayBooleanCast ((parkerBasisAssociatorMasks i j).testBit k.val)) =
      (∑ i, ∑ j, if i < j then a i * b j *
        golayBooleanCast ((parkerBasisAssociatorMasks i j).testBit k.val) else 0) +
      ∑ i, ∑ j, if j < i then a i * b j *
        golayBooleanCast ((parkerBasisAssociatorMasks i j).testBit k.val) else 0 := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact hterm i j
  rw [hsum]
  rw [Finset.sum_comm (f := fun i j : Fin 12 => if j < i then
    a i * b j * golayBooleanCast ((parkerBasisAssociatorMasks i j).testBit k.val) else 0)]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simp only [hij, ite_true]
    rw [parkerAssociator_symmetric j i k]
    ring
  · simp [hij]

theorem sourceCodeThetaPolynomial_add (a b : Fin 12 → ZMod 2) :
    sourceCodeThetaPolynomial (a + b) = sourceCodeThetaPolynomial a +
      sourceCodeThetaPolynomial b +
      golaySyndrome (fun i => golayEncoder a i * golayEncoder b i) := by
  ext k
  rw [sourceCodeThetaPolynomial_add_cross, sourceCodeTheta_cross_eq_syndrome]
  rfl

@[simp] theorem sourceCodeThetaPolynomial_zero : sourceCodeThetaPolynomial 0 = 0 := by
  ext k
  simp [sourceCodeThetaPolynomial]

@[simp] theorem sourceCodeThetaPolynomial_single (j : Fin 12) :
    sourceCodeThetaPolynomial (Pi.single j 1) = sourceCodeTheta j := by
  ext k
  unfold sourceCodeThetaPolynomial
  have hzero : (∑ i : Fin 12, ∑ l : Fin 12, if i < l then
      (Pi.single j 1 : Fin 12 → ZMod 2) i * (Pi.single j 1 : Fin 12 → ZMod 2) l *
        golayBooleanCast ((parkerBasisAssociatorMasks i l).testBit k.val) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro l _
    by_cases hi : i = j <;> by_cases hl : l = j <;> simp [hi, hl]
  rw [hzero]
  simp [Pi.single_apply]
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
