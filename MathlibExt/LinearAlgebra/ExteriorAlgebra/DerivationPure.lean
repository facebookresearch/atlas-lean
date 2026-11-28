/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.ExteriorAlgebra.Derivation
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# Exterior derivations on pure words

The exterior derivation induced by an endomorphism acts on a pure word by
applying that endomorphism to each factor in turn and adding the results.
Moving the modified factor to the front gives the equivalent signed formula.
Both equations hold over every commutative ring and arbitrary module.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- An exterior derivation acts on a pure word by replacing each factor
with its image under the endomorphism, then summing those words. -/
theorem derivation_ιMulti (g : Module.End R M) (n : ℕ) (v : Fin n → M) :
    derivation R M g (ιMulti R n v) =
      ∑ i : Fin n, ιMulti R n (Function.update v i (g (v i))) := by
  induction n with
  | zero => simp only [ιMulti_zero_apply, derivation_one, Fin.sum_univ_zero]
  | succ n ih =>
      rw [ιMulti_succ_apply, derivation_ι_mul, ih, Fin.sum_univ_succ,
        Finset.mul_sum]
      apply congrArg₂ (· + ·)
      · have ht : Matrix.vecTail (Function.update v 0 (g (v 0))) =
            Matrix.vecTail v :=
          Fin.tail_update_zero v (g (v 0))
        rw [ιMulti_succ_apply, Function.update_self, ht]
      · apply Finset.sum_congr rfl
        intro i _
        have h0 : (Function.update v i.succ (g (v i.succ))) 0 = v 0 :=
          Function.update_of_ne (Fin.succ_ne_zero i).symm (g (v i.succ)) v
        have ht : Matrix.vecTail (Function.update v i.succ (g (v i.succ))) =
            Function.update (Matrix.vecTail v) i (g (Matrix.vecTail v i)) :=
          Fin.tail_update_succ v i (g (v i.succ))
        rw [ιMulti_succ_apply, h0, ht]

/-- The same pure-word formula with each modified factor placed at the
front, including the sign of its permutation past the preceding factors. -/
theorem derivation_ιMulti_eq_sum_vecCons
    (g : Module.End R M) (n : ℕ) (v : Fin (n + 1) → M) :
    derivation R M g (ιMulti R (n + 1) v) =
      ∑ i : Fin (n + 1), ((-1 : R) ^ i.val) •
        ιMulti R (n + 1) (Matrix.vecCons (g (v i)) (i.removeNth v)) := by
  classical
  rw [derivation_ιMulti]
  apply Finset.sum_congr rfl
  intro i _
  have h := (ιMulti R (n + 1)).map_insertNth i (g (v i)) (i.removeNth v)
  rw [Fin.insertNth_removeNth] at h
  simpa only [← Int.cast_smul_eq_zsmul R, Int.cast_pow,
    Int.cast_neg, Int.cast_one] using h

end ExteriorAlgebra
