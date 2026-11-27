/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.Hochschild.ProperShuffleCotangentMap
public import MathlibExt.Algebra.Homology.ChainGradedPairingFirstPositiveImages
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.Algebra.Polynomial.Coeff
public meta import Mathlib.Tactic.FinCases

/-!
# Proper shuffles and cotangent classes of a polynomial variable

The algebra and coefficients are `ℚ[X]`. The signed `(1,1)` shuffle is
`1 ⊗ X ⊗ X² - 1 ⊗ X² ⊗ X`. A monomial-coefficient functional detects this
nonzero tensor, whereas the proper shuffle projection kills it. Its full
Hochschild boundary is zero.

The degree-one class of `X` survives the cotangent homology comparison.
Polynomial differentiation gives coordinate one on this class, coordinate
two when the coefficient head is two, and coordinate `2X` on the class of
`X²`. In contrast, the pairing image allowing a degree-zero second factor
already contains the degree-one tensor `1 ⊗ X`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open ModuleCat.Algebra.Hochschild
open ModuleCat.Algebra.Hochschild.Symmetric
open AlgebraicTopology.EilenbergZilber
open scoped TensorProduct BigOperators

namespace MathlibExtTest.Algebra.Homology.Hochschild.ProperShufflePolynomial

private abbrev A := Polynomial ℚ

private abbrev word₂ (a b : A) : A ⊗[ℚ] TensorPower ℚ 2 A :=
  (1 : A) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ (fun i : Fin 2 => if i = 0 then a else b)

private abbrev shuffleInput (a b : A) :
    (ULift A ⊗[ℚ] TensorPower ℚ 1 A) ⊗[ℚ] (A ⊗[ℚ] TensorPower ℚ 1 A) :=
  (ULift.up (1 : A) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ (fun _ : Fin 1 => a)) ⊗ₜ[ℚ]
    ((1 : A) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ (fun _ : Fin 1 => b))

private abbrev ordered : Shuffle 1 1 where
  perm := Equiv.refl _
  isShuffle := by
    constructor <;> intro i j hij
    · have h : i = j := Subsingleton.elim _ _
      simp [h] at hij
    · have h : i = j := Subsingleton.elim _ _
      simp [h] at hij

private abbrev crossing : Shuffle 1 1 where
  perm := Equiv.swap (0 : Fin 2) 1
  isShuffle := by
    constructor <;> intro i j hij
    · have h : i = j := Subsingleton.elim _ _
      simp [h] at hij
    · have h : i = j := Subsingleton.elim _ _
      simp [h] at hij

private lemma shuffle_cases (s : Shuffle 1 1) : s = ordered ∨ s = crossing := by
  generalize h : Equiv.Perm.decomposeFin s.perm = p
  obtain ⟨i, e⟩ := p
  have hperm : s.perm = Equiv.swap (0 : Fin 2) i := by
    calc
      s.perm = Equiv.Perm.decomposeFin.symm (i, e) := by
        rw [← h]
        exact (Equiv.Perm.decomposeFin.symm_apply_apply s.perm).symm
      _ = Equiv.swap (0 : Fin 2) i := by
        have he : e = (1 : Equiv.Perm (Fin 1)) := Subsingleton.elim _ _
        rw [he, Equiv.Perm.decomposeFin_symm_of_one]
  fin_cases i
  · left
    apply Shuffle.ext
    simpa [ordered] using hperm
  · right
    exact Shuffle.ext hperm

private lemma ordered_ne_crossing : ordered ≠ crossing := by
  intro h
  have hp := congrArg (fun s : Shuffle 1 1 => s.perm 0) h
  simp [ordered, crossing] at hp

private lemma shuffles_univ :
    (Finset.univ : Finset (Shuffle 1 1)) = {ordered, crossing} := by
  classical
  ext s
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact shuffle_cases s

private lemma raw_ordered (a b : A) :
    rawShuffleTerm ℚ A A ordered (shuffleInput a b) = word₂ a b := by
  rw [rawShuffleTerm_tprod]
  simp only [ULift.down_up, one_smul]
  apply congrArg (fun f : Fin 2 → A => (1 : A) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ f)
  funext i
  fin_cases i
  · change Fin.append (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)
      (Fin.castAdd 1 (0 : Fin 1)) = a
    exact Fin.append_left _ _ _
  · change Fin.append (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)
      (Fin.natAdd 1 (0 : Fin 1)) = b
    exact Fin.append_right _ _ _

private lemma raw_crossing (a b : A) :
    rawShuffleTerm ℚ A A crossing (shuffleInput a b) = word₂ b a := by
  rw [rawShuffleTerm_tprod]
  simp only [ULift.down_up, one_smul]
  apply congrArg (fun f : Fin 2 → A => (1 : A) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ f)
  funext i
  fin_cases i
  · change Fin.append (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)
      (Fin.natAdd 1 (0 : Fin 1)) = b
    exact Fin.append_right _ _ _
  · change Fin.append (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)
      (Fin.castAdd 1 (0 : Fin 1)) = a
    exact Fin.append_left _ _ _

private lemma signed_shuffle (a b : A) :
    signedRawShuffle ℚ A A 1 1 (shuffleInput a b) = word₂ a b - word₂ b a := by
  classical
  have ho : shuffleSignZ ordered = 1 := by simp [shuffleSignZ, shuffleSign, ordered]
  have hc : shuffleSignZ crossing = -1 := by simp [shuffleSignZ, shuffleSign, crossing]
  simp only [signedRawShuffle, shuffles_univ,
    Finset.sum_insert (by simpa using ordered_ne_crossing), Finset.sum_singleton,
    LinearMap.add_apply, LinearMap.smul_apply, ho, hc, one_smul, neg_one_smul]
  simp only [raw_ordered, raw_crossing, sub_eq_add_neg]

private abbrev relation : A ⊗[ℚ] TensorPower ℚ 2 A :=
  word₂ Polynomial.X (Polynomial.X ^ 2) - word₂ (Polynomial.X ^ 2) Polynomial.X

private def tailCoordinate : TensorPower ℚ 2 A →ₗ[ℚ] ℚ :=
  PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra ℚ (Fin 2) ℚ).compLinearMap
      (fun i : Fin 2 => Polynomial.lcoeff ℚ (if i = 0 then 1 else 2)))

private def tensorCoordinate : A ⊗[ℚ] TensorPower ℚ 2 A →ₗ[ℚ] ℚ :=
  TensorProduct.lift ((Polynomial.lcoeff ℚ 0).smulRight tailCoordinate)

private lemma tensorCoordinate_relation : tensorCoordinate relation = 1 := by
  simp [tensorCoordinate, tailCoordinate, relation, word₂, Polynomial.lcoeff_apply,
    MultilinearMap.compLinearMap_apply, Fin.prod_univ_two]

private lemma relation_mem : relation ∈ rawPositiveRelations ℚ A A 2 := by
  letI : MonoidalCategoryStruct (ModuleCat.{0} ℚ) :=
    ModuleCat.UniverseTensor.tensorStructure.{0, 0} (R := ℚ)
  letI : MonoidalCategory (ModuleCat.{0} ℚ) :=
    ModuleCat.UniverseTensor.monoidalCategory.{0, 0} (R := ℚ)
  letI : MonoidalPreadditive (ModuleCat.{0} ℚ) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{0, 0} (R := ℚ)
  letI : MonoidalLinear ℚ (ModuleCat.{0} ℚ) :=
    ModuleCat.UniverseTensor.monoidalLinear.{0, 0} (R := ℚ)
  have h := HomologicalComplex.ChainGradedPairing.pairAt_mem_positiveImages
    (pairing ℚ A A) 1 1 2 rfl (by decide) (by decide)
    (shuffleInput Polynomial.X (Polynomial.X ^ 2))
  change ((pairing ℚ A A).pair 1 1).hom
    (shuffleInput Polynomial.X (Polynomial.X ^ 2)) ∈ rawPositiveRelations ℚ A A 2 at h
  rw [pairing_pair_signedRawShuffle, signed_shuffle] at h
  exact h

example :
    signedRawShuffle ℚ A A 1 1 (shuffleInput Polynomial.X (Polynomial.X ^ 2)) =
      relation := signed_shuffle _ _

example : relation ≠ 0 := by
  intro h
  have hc := congrArg tensorCoordinate h
  rw [tensorCoordinate_relation, map_zero] at hc
  exact one_ne_zero hc

example : ((properShuffleProjection ℚ A A).f 2).hom relation = 0 := by
  change (rawPositiveRelations ℚ A A 2).mkQ relation = 0
  have hk : relation ∈ LinearMap.ker (rawPositiveRelations ℚ A A 2).mkQ := by
    simpa only [Submodule.ker_mkQ] using relation_mem
  exact hk

example : ((chainComplex ℚ A A).d 2 1).hom relation = 0 := by
  letI : MonoidalCategoryStruct (ModuleCat.{0} ℚ) :=
    ModuleCat.UniverseTensor.tensorStructure.{0, 0} (R := ℚ)
  letI : MonoidalCategory (ModuleCat.{0} ℚ) :=
    ModuleCat.UniverseTensor.monoidalCategory.{0, 0} (R := ℚ)
  letI : MonoidalPreadditive (ModuleCat.{0} ℚ) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{0, 0} (R := ℚ)
  letI : MonoidalLinear ℚ (ModuleCat.{0} ℚ) :=
    ModuleCat.UniverseTensor.monoidalLinear.{0, 0} (R := ℚ)
  have h := HomologicalComplex.ChainGradedPairing.positiveImages_d (pairing ℚ A A)
    (boundary_one_zero ℚ A (ULift A)) (boundary_one_zero ℚ A A) 1 relation_mem
  change ((chainComplex ℚ A A).d 2 1).hom relation ∈
    HomologicalComplex.ChainGradedPairing.positiveImages (pairing ℚ A A) 1 at h
  rw [HomologicalComplex.ChainGradedPairing.positiveImages_one] at h
  exact Submodule.mem_bot.mp h

private abbrev degreeOneClass (m p : A) :=
  (rawPositiveRelations ℚ A A 1).mkQ
    (m ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ (fun _ : Fin 1 => p))

private abbrev cotangentClass (m p : A) :=
  (ChainComplex.homologyZeroClass (properCotangentComplex ℚ A A)).hom (degreeOneClass m p)

private def differentialCoordinate : A ⊗[A] KaehlerDifferential ℚ A →ₗ[A] A :=
  (KaehlerDifferential.polynomialEquiv ℚ).toLinearMap.comp
    (TensorProduct.lid A (KaehlerDifferential ℚ A)).toLinearMap

private lemma differentialCoordinate_tmul (m p : A) :
    differentialCoordinate (m ⊗ₜ[A] KaehlerDifferential.D ℚ A p) =
      m * Polynomial.derivative p := by
  simp [differentialCoordinate, TensorProduct.lid_tmul, smul_eq_mul]

private lemma cotangentCoordinate (m p : A) :
    differentialCoordinate
      (properCotangentHomologyZeroEquiv ℚ A A (cotangentClass m p)) =
        m * Polynomial.derivative p := by
  rw [properCotangentHomologyZeroEquiv_tprod]
  exact differentialCoordinate_tmul m p

example : (properCotangentScalarAugmentation ℚ A A).hom (degreeOneClass 2 Polynomial.X) =
    ULift.up ((2 : A) ⊗ₜ[A] KaehlerDifferential.D ℚ A Polynomial.X) :=
  properCotangentScalarAugmentation_tprod ℚ A A 2 (fun _ : Fin 1 => Polynomial.X)

example : differentialCoordinate
    (properCotangentHomologyZeroEquiv ℚ A A (cotangentClass 1 Polynomial.X)) = 1 := by
  rw [cotangentCoordinate]
  simp

example : differentialCoordinate
    (properCotangentHomologyZeroEquiv ℚ A A (cotangentClass 2 Polynomial.X)) = 2 := by
  rw [cotangentCoordinate]
  simp

example : differentialCoordinate
    (properCotangentHomologyZeroEquiv ℚ A A (cotangentClass 1 (Polynomial.X ^ 2))) =
      (2 : A) * Polynomial.X := by
  rw [cotangentCoordinate]
  simp [Polynomial.derivative_X_sq]

example : cotangentClass 1 Polynomial.X ≠ 0 := by
  intro h
  have hc := congrArg
    (fun z => differentialCoordinate (properCotangentHomologyZeroEquiv ℚ A A z)) h
  rw [cotangentCoordinate] at hc
  simp at hc

private def firstPositiveOne : Submodule ℚ (A ⊗[ℚ] TensorPower ℚ 1 A) := by
  letI : MonoidalCategoryStruct (ModuleCat.{0} ℚ) :=
    ModuleCat.UniverseTensor.tensorStructure.{0, 0} (R := ℚ)
  letI : MonoidalCategory (ModuleCat.{0} ℚ) :=
    ModuleCat.UniverseTensor.monoidalCategory.{0, 0} (R := ℚ)
  letI : MonoidalPreadditive (ModuleCat.{0} ℚ) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{0, 0} (R := ℚ)
  letI : MonoidalLinear ℚ (ModuleCat.{0} ℚ) :=
    ModuleCat.UniverseTensor.monoidalLinear.{0, 0} (R := ℚ)
  exact HomologicalComplex.ChainGradedPairing.firstPositiveImages (pairing ℚ A A) 1

example : ((1 : A) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ
    (fun _ : Fin 1 => (Polynomial.X : A))) ∈ firstPositiveOne := by
  letI : MonoidalCategoryStruct (ModuleCat.{0} ℚ) :=
    ModuleCat.UniverseTensor.tensorStructure.{0, 0} (R := ℚ)
  letI : MonoidalCategory (ModuleCat.{0} ℚ) :=
    ModuleCat.UniverseTensor.monoidalCategory.{0, 0} (R := ℚ)
  letI : MonoidalPreadditive (ModuleCat.{0} ℚ) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{0, 0} (R := ℚ)
  letI : MonoidalLinear ℚ (ModuleCat.{0} ℚ) :=
    ModuleCat.UniverseTensor.monoidalLinear.{0, 0} (R := ℚ)
  letI : Unique (Shuffle 1 0) :=
    { default := Shuffle.rightUnitShuffle 1
      uniq := fun s => Shuffle.eq_rightUnitShuffle s }
  let x : (ULift A ⊗[ℚ] TensorPower ℚ 1 A) ⊗[ℚ] (A ⊗[ℚ] TensorPower ℚ 0 A) :=
    (ULift.up (1 : A) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ
      (fun _ : Fin 1 => (Polynomial.X : A))) ⊗ₜ[ℚ]
        ((1 : A) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ Fin.elim0)
  have h := HomologicalComplex.ChainGradedPairing.pairAt_mem_firstPositiveImages
    (pairing ℚ A A) 1 0 1 rfl (by decide) x
  change ((pairing ℚ A A).pair 1 0).hom x ∈ firstPositiveOne at h
  have hx : ((pairing ℚ A A).pair 1 0).hom x =
      (1 : A) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ (fun _ : Fin 1 => (Polynomial.X : A)) := by
    rw [pairing_pair_tprod, Fintype.sum_unique]
    rw [Shuffle.eq_rightUnitShuffle (default : Shuffle 1 0), Shuffle.rightUnitShuffle_sign]
    simp only [one_smul, ULift.down_up]
    apply congrArg (fun f : Fin 1 → A => (1 : A) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ f)
    funext i
    change Fin.append (fun _ : Fin 1 => (Polynomial.X : A)) Fin.elim0
      (Fin.castAdd 0 i) = Polynomial.X
    exact Fin.append_left _ _ _
  exact hx ▸ h

end MathlibExtTest.Algebra.Homology.Hochschild.ProperShufflePolynomial
