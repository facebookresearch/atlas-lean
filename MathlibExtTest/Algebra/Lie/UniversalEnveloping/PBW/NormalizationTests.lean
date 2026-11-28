/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Codex
-/

module

import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel

/-!
# Ordered PBW reduction for matrices over ZMod 6

The row-major matrix-unit basis of two-by-two matrices has ordered indices
0,1,2,3. Its reversed word E10 E01 reduces to E01 E10 + E11 − E00.
The contextual tensor congruence and its normalization quotient retain
this relation. Coordinate maps detect nonzero generators and the
commutator E00 − E11.

The coefficient-two generator is nonzero but is killed by three. Thus
the normal-form computations use a coefficient ring with zero divisors
and additive torsion, with no characteristic-zero or domain hypothesis.
-/

noncomputable section

open scoped TensorProduct
open UniversalEnvelopingAlgebra.PBW

namespace MathlibExtTest.PBWNormalization

attribute [local instance 100] LieRing.ofAssociativeRing

private abbrev R := ZMod 6
private abbrev M := Matrix (Fin 2) (Fin 2) R
private abbrev J := Σ _ : Fin 2, Fin 2

private def index : J ≃ Fin 4 :=
  (Equiv.sigmaEquivProd (Fin 2) (Fin 2)).trans finProdFinEquiv

private def basis : Module.Basis (Fin 4) R M :=
  ((Pi.basisFun R J).map
    (LinearEquiv.piCurry R (fun (_ : Fin 2) (_ : Fin 2) => R))).reindex index

private lemma basis_single (i j : Fin 2) :
    basis (finProdFinEquiv (i, j)) = Matrix.single i j (1 : R) := by
  change
    (((Pi.basisFun R J).map
      (LinearEquiv.piCurry R (fun (_ : Fin 2) (_ : Fin 2) => R))).reindex index)
      (finProdFinEquiv (i, j)) =
        (Matrix.single i j (1 : R) : Fin 2 → Fin 2 → R)
  rw [Module.Basis.reindex_apply]
  have hindex : index.symm (finProdFinEquiv (i, j)) = (⟨i, j⟩ : J) := by
    change (Equiv.sigmaEquivProd (Fin 2) (Fin 2)).symm
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  rw [hindex, Module.Basis.map_apply, Pi.basisFun_apply]
  ext r c
  change (Pi.single (⟨i, j⟩ : J) (1 : R)) ⟨r, c⟩ = Matrix.single i j (1 : R) r c
  fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases c <;> decide

private lemma basis_zero : basis 0 = Matrix.single 0 0 (1 : R) :=
  basis_single 0 0

private lemma basis_one : basis 1 = Matrix.single 0 1 (1 : R) :=
  basis_single 0 1

private lemma basis_two : basis 2 = Matrix.single 1 0 (1 : R) :=
  basis_single 1 0

private lemma basis_three : basis 3 = Matrix.single 1 1 (1 : R) :=
  basis_single 1 1

private lemma bracket_two_one : ⁅basis 2, basis 1⁆ = basis 3 - basis 0 := by
  change basis 2 * basis 1 - basis 1 * basis 2 = _
  rw [basis_two, basis_one, basis_three, basis_zero,
    Matrix.single_mul_single_same, Matrix.single_mul_single_same]
  simp only [one_mul]

private lemma bracket_repr :
    basis.repr ⁅basis 2, basis 1⁆ =
      Finsupp.single (3 : Fin 4) (1 : R) - Finsupp.single 0 1 := by
  rw [bracket_two_one, map_sub, basis.repr_self, basis.repr_self]

private def oneWord (i : Fin 4) : OrderedWord (Fin 4) := ⟨[i], by simp⟩
private def emptyWord : OrderedWord (Fin 4) := ⟨[], by simp⟩
private def pairWord : OrderedWord (Fin 4) := ⟨[1, 2], by decide⟩

private lemma normalize_one (i : Fin 4) :
    normalize basis [i] = Finsupp.single (oneWord i) 1 :=
  normalize_ordered basis (oneWord i)

private lemma normalize_pair :
    normalize basis [1, 2] = Finsupp.single pairWord 1 :=
  normalize_ordered basis pairWord

private lemma normalize_reversed :
    normalize basis [2, 1] =
      Finsupp.single pairWord 1 + Finsupp.single (oneWord 3) 1 -
        Finsupp.single (oneWord 0) 1 := by
  have hi : List.adjacentInversion ([2, 1] : List (Fin 4)) =
      some ([], 2, 1, []) := by decide
  rw [normalize_of_adjacentInversion basis hi, bracket_repr]
  change normalize basis [1, 2] +
      (Finsupp.single (3 : Fin 4) (1 : R) - Finsupp.single 0 1).sum
        (fun k r => r • normalize basis [k]) = _
  have hsum :
      (Finsupp.single (3 : Fin 4) (1 : R) - Finsupp.single 0 1).sum
        (fun k r => r • normalize basis [k]) =
          normalize basis [3] - normalize basis [0] := by
    change (Finsupp.linearCombination R (fun k : Fin 4 => normalize basis [k]))
      (Finsupp.single 3 1 - Finsupp.single 0 1) = _
    rw [map_sub, Finsupp.linearCombination_single, Finsupp.linearCombination_single,
      one_smul, one_smul]
  rw [hsum, normalize_pair, normalize_one, normalize_one]
  abel

private abbrev Q := NormalizationQuotient basis

private def generator (i : Fin 4) : Q :=
  normalizationQuotientι basis (basis i)

private lemma tensorWord_one (i : Fin 4) :
    tensorWord basis [i] = TensorAlgebra.ι R (basis i) := by
  simp only [tensorWord_cons, tensorWord_nil, mul_one]

private lemma generator_eq_word (i : Fin 4) :
    generator i = normalizationQuotientMap basis (tensorWord basis [i]) := by
  simp only [generator, normalizationQuotientι_apply, tensorWord_one]

private lemma generator_coordinates (i : Fin 4) :
    normalizationQuotientCoordinates basis (generator i) =
      Finsupp.single (oneWord i) 1 := by
  rw [generator_eq_word, normalizationQuotientCoordinates_mk,
    tensorNormalizer_tensorWord, normalize_one]

private lemma quotient_commutator :
    generator 1 * generator 2 - generator 2 * generator 1 =
      generator 0 - generator 3 := by
  have h := (normalizationQuotientι basis).map_lie (basis 2) (basis 1)
  rw [bracket_two_one, map_sub] at h
  change generator 3 - generator 0 =
    generator 2 * generator 1 - generator 1 * generator 2 at h
  calc
    _ = -(generator 2 * generator 1 - generator 1 * generator 2) := by abel
    _ = -(generator 3 - generator 0) := congrArg Neg.neg h.symm
    _ = _ := by abel

private lemma commutator_coordinates :
    normalizationQuotientCoordinates basis
        (generator 1 * generator 2 - generator 2 * generator 1) =
      Finsupp.single (oneWord 0) 1 - Finsupp.single (oneWord 3) 1 := by
  rw [quotient_commutator, map_sub, generator_coordinates, generator_coordinates]

private lemma generator_one_coefficient :
    normalizationQuotientCoordinates basis (generator 1) (oneWord 1) = 1 := by
  rw [generator_coordinates, Finsupp.single_eq_same]

private lemma commutator_zero_coefficient :
    normalizationQuotientCoordinates basis
      (generator 1 * generator 2 - generator 2 * generator 1) (oneWord 0) = 1 := by
  have hthree :
      (Finsupp.single (oneWord 3) (1 : R)) (oneWord 0) = 0 :=
    Finsupp.single_eq_of_ne (by decide : oneWord (0 : Fin 4) ≠ oneWord 3)
  rw [commutator_coordinates, Finsupp.sub_apply, Finsupp.single_eq_same,
    hthree, sub_zero]

private lemma native_reversed_coordinates :
    pbwCoordinates basis (basisWord basis [2, 1]) =
      Finsupp.single pairWord 1 + Finsupp.single (oneWord 3) 1 -
        Finsupp.single (oneWord 0) 1 := by
  rw [pbwCoordinates_basisWord, normalize_reversed]

example : normalize basis [] = Finsupp.single emptyWord 1 :=
  normalize_ordered basis emptyWord

example : normalize basis [1] = Finsupp.single (oneWord 1) 1 :=
  normalize_one 1

example : normalize basis [1, 2] = Finsupp.single pairWord 1 :=
  normalize_pair

example : normalize basis [2, 1] =
    Finsupp.single pairWord 1 + Finsupp.single (oneWord 3) 1 -
      Finsupp.single (oneWord 0) 1 :=
  normalize_reversed

example : normalizationRingCon basis
    ((TensorAlgebra.ι R (basis 3) - TensorAlgebra.ι R (basis 0)) +
      TensorAlgebra.ι R (basis 1) * TensorAlgebra.ι R (basis 2))
    (TensorAlgebra.ι R (basis 2) * TensorAlgebra.ι R (basis 1)) := by
  have h := normalizationRingCon_lie_compat basis (basis 2) (basis 1)
  rw [bracket_two_one, map_sub] at h
  exact h

example : tensorNormalizer basis
    (TensorAlgebra.ι R (basis 1) *
      ((TensorAlgebra.ι R (basis 3) - TensorAlgebra.ι R (basis 0)) +
        TensorAlgebra.ι R (basis 1) * TensorAlgebra.ι R (basis 2)) *
      TensorAlgebra.ι R (basis 2)) =
    tensorNormalizer basis
      (TensorAlgebra.ι R (basis 1) *
        (TensorAlgebra.ι R (basis 2) * TensorAlgebra.ι R (basis 1)) *
          TensorAlgebra.ι R (basis 2)) := by
  have h := normalizationRingCon_lie_compat basis (basis 2) (basis 1)
  rw [bracket_two_one, map_sub] at h
  exact h (TensorAlgebra.ι R (basis 1)) (TensorAlgebra.ι R (basis 2))

example : normalizationQuotientCoordinates basis
    (generator 1 * generator 2 - generator 2 * generator 1) =
      Finsupp.single (oneWord 0) 1 - Finsupp.single (oneWord 3) 1 :=
  commutator_coordinates

example : generator 1 ≠ 0 := by
  intro h
  have hc := generator_one_coefficient
  rw [h, map_zero] at hc
  exact (by decide : (0 : R) ≠ 1) hc

example : generator 1 * generator 2 - generator 2 * generator 1 ≠ 0 := by
  intro h
  have hc := commutator_zero_coefficient
  rw [h, map_zero] at hc
  exact (by decide : (0 : R) ≠ 1) hc

example : (2 : R) • generator 1 ≠ 0 ∧
    (3 : R) • ((2 : R) • generator 1) = 0 ∧ (2 : R) ≠ 0 ∧ (3 : R) ≠ 0 := by
  have hnonzero : (2 : R) • generator 1 ≠ 0 := by
    intro h
    have hc := congrArg
      (fun q : Q => normalizationQuotientCoordinates basis q (oneWord 1)) h
    rw [map_smul, generator_coordinates, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one, map_zero] at hc
    exact (by decide : (2 : R) ≠ 0) hc
  refine ⟨hnonzero, ?_, by decide, by decide⟩
  rw [smul_smul, show (3 : R) * 2 = 0 by decide, zero_smul]

example : pbwCoordinates basis (basisWord basis [2, 1]) =
    Finsupp.single pairWord 1 + Finsupp.single (oneWord 3) 1 -
      Finsupp.single (oneWord 0) 1 :=
  native_reversed_coordinates

example : basisWord basis [1, 2] - basisWord basis [2, 1] ≠ 0 := by
  intro h
  have hc := congrArg
    (fun u : UniversalEnvelopingAlgebra R M => pbwCoordinates basis u (oneWord 0)) h
  rw [map_sub, pbwCoordinates_basisWord, pbwCoordinates_basisWord,
    normalize_pair, normalize_reversed, map_zero] at hc
  have hpair :
      (Finsupp.single pairWord (1 : R)) (oneWord 0) = 0 :=
    Finsupp.single_eq_of_ne (by decide : oneWord (0 : Fin 4) ≠ pairWord)
  have hthree :
      (Finsupp.single (oneWord 3) (1 : R)) (oneWord 0) = 0 :=
    Finsupp.single_eq_of_ne (by decide : oneWord (0 : Fin 4) ≠ oneWord 3)
  simp only [Finsupp.sub_apply, Finsupp.add_apply, hpair, hthree,
    Finsupp.single_eq_same, Finsupp.zero_apply, zero_add, zero_sub, neg_neg] at hc
  exact (by decide : (1 : R) ≠ 0) hc

end MathlibExtTest.PBWNormalization
