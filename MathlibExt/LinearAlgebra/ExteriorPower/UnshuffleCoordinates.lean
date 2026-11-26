/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.ExteriorPower.Unshuffle
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleCoset

/-!
# Unshuffle in ordered-shuffle coordinates

For `w : Fin(p+q) → M`, unshuffle is the sum over `(p,q)`-shuffles `s` of `sign(s.perm)` times
the wedge of `w` at the first-block images tensor the wedge at the second-block images. The
two tensor factors are ordered first block then second block.

Each ordered shuffle contributes once. For an empty block the corresponding wedge is the
degree-zero unit.

Reference: Bourbaki, *Algebra*, Chapter III.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v

namespace exteriorPower

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

open AlgebraicTopology.EilenbergZilber

private theorem unshuffle_summand_shuffle (p q : ℕ) (s : Shuffle p q)
    (w : Fin (p + q) → M) :
    AlternatingMap.domCoprod.summand (ιMulti R p) (ιMulti R q)
        (Quotient.mk'' (Shuffle.cosetRepresentative p q s))
        (w ∘ (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q))) =
      Equiv.Perm.sign s.perm •
        (ιMulti R p (fun i => w (s.perm (Fin.castAdd q i))) ⊗ₜ[R]
          ιMulti R q (fun j => w (s.perm (Fin.natAdd p j)))) := by
  rw [AlternatingMap.domCoprod.summand_mk'', _root_.smul_apply,
    Shuffle.cosetRepresentative_sign]
  simp only [MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
    Function.comp_apply, Shuffle.cosetRepresentative_front, Shuffle.cosetRepresentative_back]
  exact (TensorProduct.smul_tmul' (Equiv.Perm.sign s.perm) _ _).symm

/-- Let `R` be a commutative ring, `M` an `R`-module, and `p,q : ℕ`. Write `L(i)=Fin.castAdd q i`,
`R_b(j)=Fin.natAdd p j`, and `U_(p,q) : Λ^(p+q)_R M → Λ^p_R M ⊗[R] Λ^q_R M` for unshuffle. For
`w : Fin(p+q) → M`, the value is `∑ s : Shuffle p q, sign(s.perm) • (ιMulti_R(fun i ↦
w(s.perm(L i))) ⊗ ιMulti_R(fun j ↦ w(s.perm(R_b j))))`. -/
theorem unshuffle_apply_ιMulti_shuffles (p q : ℕ) (w : Fin (p + q) → M) :
    unshuffle R M p q (ιMulti R (p + q) w) =
      ∑ s : Shuffle p q, Equiv.Perm.sign s.perm •
        (ιMulti R p (fun i => w (s.perm (Fin.castAdd q i))) ⊗ₜ[R]
          ιMulti R q (fun j => w (s.perm (Fin.natAdd p j)))) := by
  rw [unshuffle_apply_ιMulti]
  calc
    (∑ c : Equiv.Perm.ModSumCongr (Fin p) (Fin q),
        AlternatingMap.domCoprod.summand (ιMulti R p) (ιMulti R q) c
          (w ∘ (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)))) =
      ∑ s : Shuffle p q,
        AlternatingMap.domCoprod.summand (ιMulti R p) (ιMulti R q)
          ((Shuffle.cosetEquiv p q).symm s)
          (w ∘ (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q))) := by
        exact ((Shuffle.cosetEquiv p q).symm.sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Shuffle.cosetEquiv_symm_apply]
      exact unshuffle_summand_shuffle R M p q s w

end exteriorPower
