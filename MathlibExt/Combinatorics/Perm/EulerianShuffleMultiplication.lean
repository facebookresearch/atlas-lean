/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Combinatorics.Perm.EulerianComposition
public import MathlibExt.Combinatorics.Perm.ShuffleSortFibers
public import MathlibExt.Algebra.MonoidAlgebra.FiniteFiber

/-!
# Actual Eulerian evaluation and signed shuffle multiplication

The two literal finite signed permutation sums have equal output
fibers. The native actual shuffle/block factorization and split stable
labeling equivalences identify those fibers. Every term in a fiber has the
same original composite sign, proved by the native permutation sign laws.
Thus the evaluated Eulerian elements respect actual signed shuffle
multiplication. There is no supplied multiplicativity or kernel certificate.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace Equiv.Perm

open AlgebraicTopology.EilenbergZilber

/-- The literal signed native shuffle group-ring element. -/
def signedShuffleElement (p q : ℕ) : MonoidAlgebra ℚ (Perm (Fin (p + q))) :=
  ∑ s : Shuffle p q, MonoidAlgebra.single s.perm ((s.perm.sign : ℤ) : ℚ)

def blockLeftAlgebraMap (p q : ℕ) :
    MonoidAlgebra ℚ (Perm (Fin p)) →ₐ[ℚ] MonoidAlgebra ℚ (Perm (Fin (p + q))) :=
  MonoidAlgebra.mapDomainAlgHom ℚ ℚ (blockLeftHom p q)

def blockRightAlgebraMap (p q : ℕ) :
    MonoidAlgebra ℚ (Perm (Fin q)) →ₐ[ℚ] MonoidAlgebra ℚ (Perm (Fin (p + q))) :=
  MonoidAlgebra.mapDomainAlgHom ℚ ℚ (blockRightHom p q)

/-- The actual block action of the original two evaluated Eulerian elements. -/
def splitEulerianLambda (p q : ℕ) (a : ℚ) : MonoidAlgebra ℚ (Perm (Fin (p + q))) :=
  blockLeftAlgebraMap p q (eulerianLambda p a) * blockRightAlgebraMap p q (eulerianLambda q a)

/-- The actual block action has the original literal two-block coefficient sum. -/
theorem splitEulerianLambda_eq_sum (p q : ℕ) (a : ℚ) :
    splitEulerianLambda p q a =
      ∑ α : Perm (Fin p), ∑ β : Perm (Fin q),
        MonoidAlgebra.single (blockPermutation p q α β)
          (((descentBinomialPolynomial p (descentNumber α)).eval a * ((α.sign : ℤ) : ℚ)) *
            ((descentBinomialPolynomial q (descentNumber β)).eval a * ((β.sign : ℤ) : ℚ))) := by
  classical
  unfold splitEulerianLambda eulerianLambda
  simp only [map_sum, blockLeftAlgebraMap, blockRightAlgebraMap,
    MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single]
  simp_rw [Finset.sum_mul, Finset.mul_sum, MonoidAlgebra.single_mul_single,
    blockLeftHom_mul_blockRightHom]

/-- The original two evaluated block elements are exactly the actual two-block stable-label sum. -/
theorem splitEulerianLambda_nat (p q m : ℕ) :
    splitEulerianLambda p q (m : ℚ) =
      ∑ z : (Fin p → Fin m) × (Fin q → Fin m),
        MonoidAlgebra.single (blockPermutation p q (Tuple.sort z.1) (Tuple.sort z.2))
          (((blockPermutation p q (Tuple.sort z.1) (Tuple.sort z.2)).sign : ℤ) : ℚ) := by
  classical
  unfold splitEulerianLambda
  rw [← signedStableSortElement_eq_eulerianLambda,
    ← signedStableSortElement_eq_eulerianLambda]
  unfold signedStableSortElement
  simp only [map_sum, blockLeftAlgebraMap, blockRightAlgebraMap,
    MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single]
  simp_rw [Finset.sum_mul, Finset.mul_sum, MonoidAlgebra.single_mul_single,
    blockLeftHom_mul_blockRightHom]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro g _
  rw [sign_blockPermutation]
  simp only [Units.val_mul, Int.cast_mul]

/-- The exact natural-parameter Eulerian group-ring element respects the actual signed shuffle product. -/
theorem eulerianLambda_mul_signedShuffle (p q m : ℕ) :
    eulerianLambda (p + q) (m : ℚ) * signedShuffleElement p q =
      signedShuffleElement p q * splitEulerianLambda p q (m : ℚ) := by
  classical
  rw [← signedStableSortElement_eq_eulerianLambda, splitEulerianLambda_nat]
  unfold signedStableSortElement signedShuffleElement
  simp_rw [Finset.sum_mul, Finset.mul_sum, MonoidAlgebra.single_mul_single]
  have hleft (f : Fin (p + q) → Fin m) (s : Shuffle p q) :
      (((Tuple.sort f).sign : ℤ) : ℚ) * ((s.perm.sign : ℤ) : ℚ) =
        (((Tuple.sort f * s.perm).sign : ℤ) : ℚ) := by
    rw [sign_mul]
    simp only [Units.val_mul, Int.cast_mul]
  have hright (s : Shuffle p q) (z : (Fin p → Fin m) × (Fin q → Fin m)) :
      ((s.perm.sign : ℤ) : ℚ) *
        (((blockPermutation p q (Tuple.sort z.1) (Tuple.sort z.2)).sign : ℤ) : ℚ) =
      (((s.perm * blockPermutation p q (Tuple.sort z.1) (Tuple.sort z.2)).sign : ℤ) : ℚ) := by
    rw [sign_mul]
    simp only [Units.val_mul, Int.cast_mul]
  simp_rw [hleft, hright]
  let leftTerm : ((Fin (p + q) → Fin m) × Shuffle p q) → MonoidAlgebra ℚ (Perm (Fin (p + q))) :=
    fun z => MonoidAlgebra.single (Tuple.sort z.1 * z.2.perm)
      (((Tuple.sort z.1 * z.2.perm).sign : ℤ) : ℚ)
  let rightTerm : (Shuffle p q × ((Fin p → Fin m) × (Fin q → Fin m))) →
      MonoidAlgebra ℚ (Perm (Fin (p + q))) :=
    fun z => MonoidAlgebra.single (z.1.perm * blockPermutation p q (Tuple.sort z.2.1) (Tuple.sort z.2.2))
      (((z.1.perm * blockPermutation p q (Tuple.sort z.2.1) (Tuple.sort z.2.2)).sign : ℤ) : ℚ)
  change (∑ f : Fin (p + q) → Fin m, ∑ s : Shuffle p q, leftTerm (f, s)) =
    ∑ s : Shuffle p q, ∑ z : (Fin p → Fin m) × (Fin q → Fin m), rightTerm (s, z)
  rw [← Fintype.sum_prod_type leftTerm, ← Fintype.sum_prod_type rightTerm]
  dsimp only [leftTerm, rightTerm]
  let leftOutput : ((Fin (p + q) → Fin m) × Shuffle p q) → Perm (Fin (p + q)) :=
    fun z => Tuple.sort z.1 * z.2.perm
  let rightOutput : (Shuffle p q × ((Fin p → Fin m) × (Fin q → Fin m))) → Perm (Fin (p + q)) :=
    fun z => z.1.perm * blockPermutation p q (Tuple.sort z.2.1) (Tuple.sort z.2.2)
  let signCoefficient : Perm (Fin (p + q)) → ℚ := fun γ => ((γ.sign : ℤ) : ℚ)
  change (∑ z, MonoidAlgebra.single (leftOutput z) (signCoefficient (leftOutput z))) =
    ∑ z, MonoidAlgebra.single (rightOutput z) (signCoefficient (rightOutput z))
  rw [MonoidAlgebra.sum_single_eq_sum_fiber leftOutput signCoefficient,
    MonoidAlgebra.sum_single_eq_sum_fiber rightOutput signCoefficient]
  apply Finset.sum_congr rfl
  intro γ _
  have hcard : Nat.card (ShuffleSortFiber p q m γ) = Nat.card (SplitShuffleSortFiber p q m γ) := by
    simpa only [Fintype.card_eq_nat_card] using card_shuffleSortFiber_eq p q m γ
  simpa only [Fintype.card_eq_nat_card] using
    congrArg (fun n : ℕ => n • MonoidAlgebra.single γ (signCoefficient γ)) hcard

end Equiv.Perm
