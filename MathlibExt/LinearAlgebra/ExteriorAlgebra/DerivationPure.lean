/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.ExteriorAlgebra.Derivation
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# Exterior derivations on pure words

For a commutative ring R, an R-module M and g ∈ End_R(M), the induced degree-zero derivation
acts on the n+1 factors x₀∧…∧xₙ by summing the words in which one xᵢ is replaced by g(xᵢ).
No sign occurs
while that factor remains in its position.

Moving the modified factor to the first position gives the equivalent formula ∑ᵢ(-1)^i
g(xᵢ)∧x₀∧…∧x̂ᵢ∧…∧xₙ, with the other factors in their inherited order. The sign comes from moving
across the i preceding exterior factors. These formulas hold for arbitrary R and M under the
stated commutative-ring hypothesis.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Let R be a commutative ring, M an R-module and g ∈ End_R(M). Let D_g be the degree-zero exterior
derivation induced by g. For n : ℕ and v : Fin n → M, D_g(v₀∧…∧vₙ₋₁)=∑ᵢv₀∧…∧g(vᵢ)∧…∧vₙ₋₁. The
modified factor remains at position i. For n=0, this is D_g(1)=0 and the sum is empty. -/
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

/-- Let R be a commutative ring, M an R-module and g ∈ End_R(M). Let D_g be the degree-zero exterior
derivation induced by g. For v : Fin(n+1) → M, D_g(v₀∧…∧vₙ)=∑ᵢ(-1)^i g(vᵢ)∧removeᵢ(v). The
deleted tail keeps its inherited order, and the coefficient (-1)^i is taken in R. -/
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
