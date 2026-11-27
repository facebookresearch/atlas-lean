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
# Eulerian evaluation and signed shuffle products

For `p,q : ℕ`, let `Sh_(p,q)` be the sum of `(p,q)`-shuffle permutations with their signs in
`ℚ[S_(p+q)]`. The block embeddings give the split family `Λ_p(a)^L Λ_q(a)^R`.

At every natural parameter `m`, `Λ_(p+q)(m) Sh_(p,q) = Sh_(p,q) (Λ_p(m)^L Λ_q(m)^R)`. The
split family is also the signed sum over two finite block labelings, with their sorting
permutations combined by `blockPermutation`.

Reference: Loday, *Cyclic Homology*, Sections 4.2 and 4.5.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace Equiv.Perm

open AlgebraicTopology.EilenbergZilber

/-- Let `p,q : ℕ`, `N=p+q`, and `Sh_(p,q) = ∑ s : Shuffle p q, sign(s.perm) [s.perm]` in `ℚ[S_N]`.
`signedShuffleElement p q` is this finite sign-weighted sum; `Shuffle p q` consists of
permutations increasing on each of the two input blocks. -/
def signedShuffleElement (p q : ℕ) : MonoidAlgebra ℚ (Perm (Fin (p + q))) :=
  ∑ s : Shuffle p q, MonoidAlgebra.single s.perm ((s.perm.sign : ℤ) : ℚ)

def blockLeftAlgebraMap (p q : ℕ) :
    MonoidAlgebra ℚ (Perm (Fin p)) →ₐ[ℚ] MonoidAlgebra ℚ (Perm (Fin (p + q))) :=
  MonoidAlgebra.mapDomainAlgHom ℚ ℚ (blockLeftHom p q)

def blockRightAlgebraMap (p q : ℕ) :
    MonoidAlgebra ℚ (Perm (Fin q)) →ₐ[ℚ] MonoidAlgebra ℚ (Perm (Fin (p + q))) :=
  MonoidAlgebra.mapDomainAlgHom ℚ ℚ (blockRightHom p q)

/-- Let `p,q : ℕ`, `N=p+q`, and `Sh_(p,q) = ∑ s : Shuffle p q, sign(s.perm) [s.perm]` in `ℚ[S_N]`.
For `a : ℚ`, `splitEulerianLambda p q a = B_L(Λ_p(a)) * B_R(Λ_q(a))`, where `B_L,B_R` embed
the left and right block group rings in `ℚ[S_N]`. -/
def splitEulerianLambda (p q : ℕ) (a : ℚ) : MonoidAlgebra ℚ (Perm (Fin (p + q))) :=
  blockLeftAlgebraMap p q (eulerianLambda p a) * blockRightAlgebraMap p q (eulerianLambda q a)

/-- Let `p,q : ℕ`, `N=p+q`, and `Sh_(p,q) = ∑ s : Shuffle p q, sign(s.perm) [s.perm]` in `ℚ[S_N]`.
For `a : ℚ`, the split family is the sum over `α ∈ S_p`, `β ∈ S_q` with basis element
`[blockPermutation p q α β]` and coefficient `P_(p,d(α))(a) sign(α) * P_(q,d(β))(a) sign(β)`,
where `P_(r,d)(X)=(1/r!)∏_(j=0)^(r-1)(X+j-d)`. -/
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

/-- Let `p,q : ℕ`, `N=p+q`, and `Sh_(p,q) = ∑ s : Shuffle p q, sign(s.perm) [s.perm]` in `ℚ[S_N]`.
For `m : ℕ`, `splitEulerianLambda p q m` equals the sum over `g : Fin p → Fin m` and `h : Fin
q → Fin m`, with contribution `sign(blockPermutation(sort g,sort h)) [blockPermutation(sort
g,sort h)]`. -/
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

/-- Let `p,q : ℕ`, `N=p+q`, and `Sh_(p,q) = ∑ s : Shuffle p q, sign(s.perm) [s.perm]` in `ℚ[S_N]`.
For every `m : ℕ`, `Λ_N(m) * Sh_(p,q) = Sh_(p,q) * splitEulerianLambda p q m`, where `Λ_r` is
the sign-weighted descent-polynomial family and the natural parameter is coerced to `ℚ`. -/
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
