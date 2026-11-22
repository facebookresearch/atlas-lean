/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Function.Basic

/-!
# Dataset swap identity

The reindexing identity behind uniform-stability generalization proofs:
replacing one dataset coordinate by a fresh sample and evaluating there has
the same total as evaluating the original algorithm at a fresh sample. The
losses take values in any additive commutative monoid. The stability bound
itself is not included here.

## References

* O. Bousquet and A. Elisseeff, *Stability and generalization*, Journal of
  Machine Learning Research 2 (2002).
* S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From
  Theory to Algorithms*, Cambridge University Press, 2014, Chapter 13.
-/

@[expose] public section

namespace MathlibExt.Probability.SwapIdentity

/-- The swap identity behind uniform-stability generalization proofs.
Datasets are `S : Fin n → Z`; `A` maps a dataset to a hypothesis and `ℓ h z`
is the loss of `h` on sample `z`, with values in an additive commutative
monoid `R`. For each coordinate `i`, summing the loss of the algorithm trained
on the dataset with coordinate `i` replaced by a fresh sample, evaluated at
the replaced sample, over all datasets and fresh samples, equals summing the
loss of the algorithm trained on the original dataset at a fresh sample. The
bijection swaps the fresh sample with the `i`-th dataset entry. -/
theorem swap_identity {Z H R : Type*} [Fintype Z] [AddCommMonoid R]
    {n : ℕ} (A : (Fin n → Z) → H) (ℓ : H → Z → R) (i : Fin n) :
    (∑ S : Fin n → Z, ∑ z : Z, ℓ (A (Function.update S i z)) (S i))
      = ∑ S : Fin n → Z, ∑ z : Z, ℓ (A S) z := by
  let e : ((Fin n → Z) × Z) ≃ ((Fin n → Z) × Z) :=
    { toFun := fun p => (Function.update p.1 i p.2, p.1 i)
      invFun := fun p => (Function.update p.1 i p.2, p.1 i)
      left_inv := fun p => by
        simp only
        ext
        · simp [Function.update_idem, Function.update_eq_self]
        · simp [Function.update_self]
      right_inv := fun p => by
        simp only
        ext
        · simp [Function.update_idem, Function.update_eq_self]
        · simp [Function.update_self] }
  have hsum : (∑ p : (Fin n → Z) × Z, ℓ (A (Function.update p.1 i p.2)) (p.1 i))
      = ∑ p : (Fin n → Z) × Z, ℓ (A p.1) p.2 := by
    have h := Equiv.sum_comp e (fun p : (Fin n → Z) × Z => ℓ (A p.1) p.2)
    simpa [e] using h
  have hL : (∑ S : Fin n → Z, ∑ z : Z, ℓ (A (Function.update S i z)) (S i))
      = ∑ p : (Fin n → Z) × Z, ℓ (A (Function.update p.1 i p.2)) (p.1 i) :=
    (Fintype.sum_prod_type
      (fun p : (Fin n → Z) × Z => ℓ (A (Function.update p.1 i p.2)) (p.1 i))).symm
  have hR : (∑ S : Fin n → Z, ∑ z : Z, ℓ (A S) z)
      = ∑ p : (Fin n → Z) × Z, ℓ (A p.1) p.2 :=
    (Fintype.sum_prod_type (fun p : (Fin n → Z) × Z => ℓ (A p.1) p.2)).symm
  rw [hL, hR]
  exact hsum

end MathlibExt.Probability.SwapIdentity

end
