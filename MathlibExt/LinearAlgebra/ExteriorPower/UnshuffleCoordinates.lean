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
# General exterior unshuffle in the existing ordered-shuffle index

The native domCoprod cosets are reindexed by the existing actual ordered
shuffles. Each shuffle contributes once, with its native permutation sign,
including either empty block. The formula requires no basis or denominator.
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

/-- Every general exterior unshuffle is the signed sum over the actual ordered shuffles. -/
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
