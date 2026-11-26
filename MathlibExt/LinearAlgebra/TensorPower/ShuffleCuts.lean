/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleUnit
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.Data.Fintype.OfMap

/-!
# Signed shuffle products and degree-cut convolution

For a commutative ring `k` and `k`-module `V`, concatenate tensor
words of lengths `p,q` and then sum their reindexings over `(p,q)`-
shuffles with the permutation sign. A weak cut of `n` is a pair
`p+q=n`; a proper cut requires `p,q>0`. Splitting a length-`n` word
at a cut and multiplying by the signed shuffle gives an endomorphism
of `V^⊗n`.

The two empty-block cuts act by identity. Thus in positive degree the
sum over all weak cuts is `2·id` plus the sum over proper cuts.
In degree zero the two unit cuts coincide and the full sum has one
identity term. No rationality assumption is required.

## References

* J.-L. Loday, *Cyclic Homology*, §4.2, for signed shuffle products.
* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
-/

@[expose] public section
noncomputable section

open scoped TensorProduct BigOperators

universe u v w

namespace TensorPower

/-- For `n ∈ ℕ`, a weak shuffle degree cut is a pair of natural
block lengths `(p,q)` with the specified equality `p+q=n`. -/
abbrev ShuffleDegreeCut (n : ℕ) := {pq : ℕ × ℕ // pq.1 + pq.2 = n}

/-- For `n ∈ ℕ`, a proper shuffle degree cut is a weak cut
`p+q=n` with both block lengths strictly positive. -/
abbrev ProperShuffleDegreeCut (n : ℕ) :=
  {z : ShuffleDegreeCut n // 0 < z.1.1 ∧ 0 < z.1.2}

/-- For a weak cut `(p,q)` of `n`, both lengths lie in
`Fin(n+1)`; the bounded-pair map records those two lengths. -/
def cutBound (n : ℕ) (z : ShuffleDegreeCut n) : Fin (n + 1) × Fin (n + 1) :=
  (⟨z.1.1, by have h := z.2; omega⟩, ⟨z.1.2, by have h := z.2; omega⟩)

/-- For each `n ∈ ℕ`, the map from weak cuts `p+q=n` to their
bounded pairs in `Fin(n+1) × Fin(n+1)` is injective. -/
theorem cutBound_injective (n : ℕ) : Function.Injective (cutBound n) := by
  intro z z' h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun t : Fin (n + 1) × Fin (n + 1) => t.1.val) h
  · exact congrArg (fun t : Fin (n + 1) × Fin (n + 1) => t.2.val) h

instance shuffleDegreeCutFintype (n : ℕ) : Fintype (ShuffleDegreeCut n) :=
  Fintype.ofInjective (cutBound n) (cutBound_injective n)

instance properShuffleDegreeCutFintype (n : ℕ) : Fintype (ProperShuffleDegreeCut n) :=
  Fintype.ofFinite _

/-- For `n ∈ ℕ`, the left unit degree cut is `(0,n)`, with empty
first block and the whole degree in the second block. -/
def leftUnitDegreeCut (n : ℕ) : ShuffleDegreeCut n := ⟨(0, n), Nat.zero_add n⟩

/-- For `n ∈ ℕ`, the right unit degree cut is `(n,0)`, with the
whole degree in the first block and an empty second block. -/
def rightUnitDegreeCut (n : ℕ) : ShuffleDegreeCut n := ⟨(n, 0), Nat.add_zero n⟩

/-- For `n>0`, the weak cuts `p+q=n` are in bijection with the
two unit cuts and the proper cuts: `Cut(n) ≃ Fin 2 ⊕ ProperCut(n)`. -/
def shuffleDegreeCutEquivUnitsProper (n : ℕ) (hn : 0 < n) :
    ShuffleDegreeCut n ≃ Fin 2 ⊕ ProperShuffleDegreeCut n where
  toFun z :=
    if hp : z.1.1 = 0 then Sum.inl 0
    else if hq : z.1.2 = 0 then Sum.inl 1
    else Sum.inr ⟨z, Nat.pos_of_ne_zero hp, Nat.pos_of_ne_zero hq⟩
  invFun z := match z with
    | Sum.inl i => Fin.cases (leftUnitDegreeCut n) (fun _ => rightUnitDegreeCut n) i
    | Sum.inr z => z.val
  left_inv z := by
    by_cases hp : z.1.1 = 0
    · simp only [dite_eq_left hp]
      apply Subtype.ext
      apply Prod.ext
      · exact hp.symm
      · have h := z.2; simp only [hp, Nat.zero_add] at h; exact h.symm
    · by_cases hq : z.1.2 = 0
      · simp only [dite_eq_right hp, dite_eq_left hq]
        apply Subtype.ext
        apply Prod.ext
        · have h := z.2; simp only [hq, Nat.add_zero] at h; exact h.symm
        · exact hq.symm
      · simp only [dite_eq_right hp, dite_eq_right hq]
  right_inv z := by
    cases z with
    | inl i =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [leftUnitDegreeCut]
      · have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
        subst j
        have hcases : Fin.cases (leftUnitDegreeCut n)
            (fun _ : Fin 1 => rightUnitDegreeCut n) (Fin.succ (0 : Fin 1)) = rightUnitDegreeCut n := rfl
        dsimp only
        rw [hcases]
        simp [rightUnitDegreeCut, Nat.ne_of_gt hn]
    | inr z =>
      simp [Nat.ne_of_gt z.2.1, Nat.ne_of_gt z.2.2]

variable {k : Type u} [CommRing k] {V : Type v} [AddCommGroup V] [Module k V]

/-- Let `k` be a commutative ring and `V` a `k`-module.
Write `Sh(p,q)` for permutations that place two ordered blocks
of lengths `p,q`, and `ε(s)` for the integer sign of the shuffle. The signed shuffle endomorphism of `V^⊗(p+q)` is
`sh_(p,q)=∑_(s∈Sh(p,q)) ε(s)·reindex(s)`. Reindexing sends a
word `x` to the word `i ↦ x(s⁻¹(i))`. -/
def signedShuffleEnd (p q : ℕ) : Module.End k (TensorPower k (p + q) V) := by
  classical
  exact ∑ s : AlgebraicTopology.EilenbergZilber.Shuffle p q,
    AlgebraicTopology.EilenbergZilber.shuffleSignZ s •
      (PiTensorProduct.reindex k (fun _ : Fin (p + q) => V) s.perm).toLinearMap

/-- Let `k` be a commutative ring and `V` a `k`-module.
Write `Sh(p,q)` for permutations that place two ordered blocks
of lengths `p,q`, and `ε(s)` for the integer sign of the shuffle. The signed shuffle product
`V^⊗p ⊗[k] V^⊗q → V^⊗(p+q)` first concatenates the two tensor
words, then applies `sh_(p,q)`. -/
def signedShuffleProduct (p q : ℕ) :
    TensorPower k p V ⊗[k] TensorPower k q V →ₗ[k] TensorPower k (p + q) V :=
  (signedShuffleEnd (k := k) (V := V) p q).comp
    (TensorPower.mulEquiv (R := k) (M := V) (n := p) (m := q)).toLinearMap

/-- Let `k` be a commutative ring and `V` a `k`-module.
Write `Sh(p,q)` for permutations that place two ordered blocks
of lengths `p,q`, and `ε(s)` for the integer sign of the shuffle. For words `a : Fin p → V`, `b : Fin q → V`, the product is
`∑_(s∈Sh(p,q)) ε(s) • tprod_k(i ↦ append(a,b)(s⁻¹(i)))` on
`tprod_k(a) ⊗ tprod_k(b)`. -/
theorem signedShuffleProduct_tprod (p q : ℕ) (a : Fin p → V) (b : Fin q → V) :
    signedShuffleProduct (k := k) (V := V) p q (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b) =
      ∑ s : AlgebraicTopology.EilenbergZilber.Shuffle p q,
        AlgebraicTopology.EilenbergZilber.shuffleSignZ s •
          PiTensorProduct.tprod k (fun i => Fin.append a b (s.perm.symm i)) := by
  classical
  have hmul :
      (TensorPower.mulEquiv (R := k) (M := V) (n := p) (m := q)).toLinearMap
          (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b) =
        PiTensorProduct.tprod k (Fin.append a b) :=
    TensorPower.tprod_mul_tprod k a b
  rw [signedShuffleProduct, LinearMap.comp_apply, hmul]
  simp only [signedShuffleEnd, LinearMap.sum_apply, ← Int.cast_smul_eq_zsmul k,
    LinearMap.smul_apply, LinearEquiv.coe_toLinearMap, PiTensorProduct.reindex_tprod]

/-- Let `k` be a commutative ring and `V` a `k`-module.
Write `Sh(p,q)` for permutations that place two ordered blocks
of lengths `p,q`, and `ε(s)` for the integer sign of the shuffle. The signed shuffle endomorphism `sh_(0,n)` is the identity
of `V^⊗n`, since there is only one shuffle with an empty first block. -/
theorem signedShuffleEnd_left_zero (n : ℕ) : signedShuffleEnd (k := k) (V := V) 0 n = LinearMap.id := by
  classical
  letI : Unique (AlgebraicTopology.EilenbergZilber.Shuffle 0 n) :=
    { default := AlgebraicTopology.EilenbergZilber.Shuffle.leftUnitShuffle n
      uniq := AlgebraicTopology.EilenbergZilber.Shuffle.eq_leftUnitShuffle }
  have hdefault : (default : AlgebraicTopology.EilenbergZilber.Shuffle 0 n) =
      AlgebraicTopology.EilenbergZilber.Shuffle.leftUnitShuffle n :=
    AlgebraicTopology.EilenbergZilber.Shuffle.eq_leftUnitShuffle _
  have hsign : AlgebraicTopology.EilenbergZilber.shuffleSignZ
      (default : AlgebraicTopology.EilenbergZilber.Shuffle 0 n) = 1 := by
    rw [hdefault]
    exact AlgebraicTopology.EilenbergZilber.Shuffle.leftUnitShuffle_sign n
  have hperm : (default : AlgebraicTopology.EilenbergZilber.Shuffle 0 n).perm =
      Equiv.refl (Fin (0 + n)) := by
    rw [hdefault]
    rfl
  unfold signedShuffleEnd
  rw [Fintype.sum_unique, hsign, one_smul, hperm, PiTensorProduct.reindex_refl]
  rfl

/-- Let `k` be a commutative ring and `V` a `k`-module.
Write `Sh(p,q)` for permutations that place two ordered blocks
of lengths `p,q`, and `ε(s)` for the integer sign of the shuffle. The signed shuffle endomorphism `sh_(n,0)` is the identity
of `V^⊗n`, since there is only one shuffle with an empty second block. -/
theorem signedShuffleEnd_right_zero (n : ℕ) : signedShuffleEnd (k := k) (V := V) n 0 = LinearMap.id := by
  classical
  letI : Unique (AlgebraicTopology.EilenbergZilber.Shuffle n 0) :=
    { default := AlgebraicTopology.EilenbergZilber.Shuffle.rightUnitShuffle n
      uniq := AlgebraicTopology.EilenbergZilber.Shuffle.eq_rightUnitShuffle }
  have hdefault : (default : AlgebraicTopology.EilenbergZilber.Shuffle n 0) =
      AlgebraicTopology.EilenbergZilber.Shuffle.rightUnitShuffle n :=
    AlgebraicTopology.EilenbergZilber.Shuffle.eq_rightUnitShuffle _
  have hsign : AlgebraicTopology.EilenbergZilber.shuffleSignZ
      (default : AlgebraicTopology.EilenbergZilber.Shuffle n 0) = 1 := by
    rw [hdefault]
    exact AlgebraicTopology.EilenbergZilber.Shuffle.rightUnitShuffle_sign n
  have hperm : (default : AlgebraicTopology.EilenbergZilber.Shuffle n 0).perm =
      Equiv.refl (Fin (n + 0)) := by
    rw [hdefault]
    rfl
  unfold signedShuffleEnd
  rw [Fintype.sum_unique, hsign, one_smul, hperm, PiTensorProduct.reindex_refl]
  rfl

/-- Let `k` be a commutative ring and `V` a `k`-module.
Write `Sh(p,q)` for permutations that place two ordered blocks
of lengths `p,q`, and `ε(s)` for the integer sign of the shuffle. For a weak cut `z=(p,q)` with `p+q=n`, splitting into the
two block tensor powers and applying signed shuffle multiplication,
then identifying the total degree with `n`, gives the cut
endomorphism of `V^⊗n`. -/
def shuffleCutEnd {n : ℕ} (z : ShuffleDegreeCut n) : Module.End k (TensorPower k n V) :=
  (TensorPower.cast k V z.2).toLinearMap.comp
    ((signedShuffleProduct (k := k) (V := V) z.1.1 z.1.2).comp
      ((TensorPower.mulEquiv (R := k) (M := V) (n := z.1.1) (m := z.1.2)).symm.toLinearMap.comp
        (TensorPower.cast k V z.2).symm.toLinearMap))

/-- Let `k` be a commutative ring and `V` a `k`-module.
Write `Sh(p,q)` for permutations that place two ordered blocks
of lengths `p,q`, and `ε(s)` for the integer sign of the shuffle. For `z=(p,q)` with `p+q=n`, the cut endomorphism is
`cast_(p+q=n) ∘ sh_(p,q) ∘ cast_(p+q=n)⁻¹`:
it is the signed shuffle operator transported from degree `p+q`
to degree `n`. -/
theorem shuffleCutEnd_eq_cast {n : ℕ} (z : ShuffleDegreeCut n) :
    shuffleCutEnd (k := k) (V := V) z = (TensorPower.cast k V z.2).toLinearMap.comp
      ((signedShuffleEnd (k := k) (V := V) z.1.1 z.1.2).comp (TensorPower.cast k V z.2).symm.toLinearMap) := by
  apply LinearMap.ext
  intro x
  change TensorPower.cast k V z.2
      (signedShuffleEnd (k := k) (V := V) z.1.1 z.1.2
        ((TensorPower.mulEquiv (R := k) (M := V) (n := z.1.1) (m := z.1.2))
          ((TensorPower.mulEquiv (R := k) (M := V) (n := z.1.1) (m := z.1.2)).symm
            ((TensorPower.cast k V z.2).symm x)))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Let `k` be a commutative ring and `V` a `k`-module.
Write `Sh(p,q)` for permutations that place two ordered blocks
of lengths `p,q`, and `ε(s)` for the integer sign of the shuffle. The cut endomorphism for `(0,n)` is identity on `V^⊗n`. -/
theorem shuffleCutEnd_left_unit (n : ℕ) :
    shuffleCutEnd (k := k) (V := V) (leftUnitDegreeCut n) = LinearMap.id := by
  rw [shuffleCutEnd_eq_cast]
  change (TensorPower.cast k V (Nat.zero_add n)).toLinearMap.comp
    ((signedShuffleEnd (k := k) (V := V) 0 n).comp
      (TensorPower.cast k V (Nat.zero_add n)).symm.toLinearMap) = LinearMap.id
  rw [signedShuffleEnd_left_zero]
  apply LinearMap.ext
  intro x
  exact (TensorPower.cast k V (leftUnitDegreeCut n).2).apply_symm_apply x

/-- Let `k` be a commutative ring and `V` a `k`-module.
Write `Sh(p,q)` for permutations that place two ordered blocks
of lengths `p,q`, and `ε(s)` for the integer sign of the shuffle. The cut endomorphism for `(n,0)` is identity on `V^⊗n`. -/
theorem shuffleCutEnd_right_unit (n : ℕ) :
    shuffleCutEnd (k := k) (V := V) (rightUnitDegreeCut n) = LinearMap.id := by
  rw [shuffleCutEnd_eq_cast]
  change (TensorPower.cast k V (Nat.add_zero n)).toLinearMap.comp
    ((signedShuffleEnd (k := k) (V := V) n 0).comp
      (TensorPower.cast k V (Nat.add_zero n)).symm.toLinearMap) = LinearMap.id
  rw [signedShuffleEnd_right_zero]
  apply LinearMap.ext
  intro x
  exact (TensorPower.cast k V (rightUnitDegreeCut n).2).apply_symm_apply x

/-- Let `k` be a commutative ring and `V` a `k`-module.
Write `Sh(p,q)` for permutations that place two ordered blocks
of lengths `p,q`, and `ε(s)` for the integer sign of the shuffle. The two-cut shuffle convolution in degree `n` is the finite
sum of cut endomorphisms over all weak cuts `p+q=n`, including
the empty-block cuts. -/
def shuffleConvolutionTwo (n : ℕ) : Module.End k (TensorPower k n V) :=
  ∑ z : ShuffleDegreeCut n, shuffleCutEnd (k := k) (V := V) z

/-- Let `k` be a commutative ring and `V` a `k`-module.
Write `Sh(p,q)` for permutations that place two ordered blocks
of lengths `p,q`, and `ε(s)` for the integer sign of the shuffle. The proper two-cut shuffle convolution in degree `n` is
the finite sum of cut endomorphisms over `p,q>0` with `p+q=n`. -/
def properShuffleConvolutionTwo (n : ℕ) : Module.End k (TensorPower k n V) :=
  ∑ z : ProperShuffleDegreeCut n, shuffleCutEnd (k := k) (V := V) z.val

/-- Let `k` be a commutative ring and `V` a `k`-module.
Write `Sh(p,q)` for permutations that place two ordered blocks
of lengths `p,q`, and `ε(s)` for the integer sign of the shuffle. For `n>0`, the full two-cut convolution equals
`2 • id_(V^⊗n) + properShuffleConvolutionTwo(n)`, the two
identity terms coming from `(0,n)` and `(n,0)`. -/
theorem shuffleConvolutionTwo_eq_two_add_proper (n : ℕ) (hn : 0 < n) :
    shuffleConvolutionTwo (k := k) (V := V) n =
      (2 : k) • LinearMap.id + properShuffleConvolutionTwo (k := k) (V := V) n := by
  classical
  let e := shuffleDegreeCutEquivUnitsProper n hn
  unfold shuffleConvolutionTwo properShuffleConvolutionTwo
  rw [← e.symm.sum_comp (fun z => shuffleCutEnd (k := k) (V := V) z), Fintype.sum_sum_type, Fin.sum_univ_two]
  change shuffleCutEnd (k := k) (V := V) (leftUnitDegreeCut n) +
      shuffleCutEnd (k := k) (V := V) (rightUnitDegreeCut n) +
        (∑ z : ProperShuffleDegreeCut n, shuffleCutEnd (k := k) (V := V) z.val) = _
  rw [shuffleCutEnd_left_unit, shuffleCutEnd_right_unit, two_smul]

end TensorPower
