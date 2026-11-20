/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexLocalDisagreementSwitch
import Code.FrontierD.SixVertexMarkedTraceExpansion









open Finset Matrix Polynomial

namespace StatMech.FrontierD

noncomputable section


noncomputable def sixVertexLocalMarkedPatternWeight
    (p : SixVertexLocalIncomingPattern) : Real[X] :=
  if p.Ice then if p.IsCType then C 2 + X else 1 else 0

theorem sixVertexLocalMarkedPatternWeight_eq_pow
    (p : SixVertexLocalIncomingPattern) (hp : p.Ice) :
    sixVertexLocalMarkedPatternWeight p =
      (C 2 + X) ^ (if p.IsCType then 1 else 0) := by
  unfold sixVertexLocalMarkedPatternWeight
  rw [if_pos hp]
  by_cases hpc : p.IsCType <;> simp [hpc]

theorem sixVertexLocalMarkedPatternWeight_mul_eq_pow
    (p q : SixVertexLocalIncomingPattern) (hp : p.Ice) (hq : q.Ice) :
    sixVertexLocalMarkedPatternWeight p *
        sixVertexLocalMarkedPatternWeight q =
      (C 2 + X) ^ sixVertexLocalCTypeCount p q := by
  rw [sixVertexLocalMarkedPatternWeight_eq_pow p hp,
    sixVertexLocalMarkedPatternWeight_eq_pow q hq, ← pow_add]
  rfl



theorem coeff_two_add_X_pow (m k : Nat) :
    ((C 2 + X : Real[X]) ^ m).coeff k =
      (2 : Real) ^ (m - k) * m.choose k := by
  rw [add_comm, Polynomial.coeff_X_add_C_pow]



theorem coeff_two_add_X_pow_mono {a b : Nat} (hab : a <= b) (k : Nat) :
    ((C 2 + X : Real[X]) ^ a).coeff k <=
      ((C 2 + X : Real[X]) ^ b).coeff k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add, Polynomial.coeff_mul]
  let f : Nat × Nat -> Real := fun ij =>
    ((C 2 + X : Real[X]) ^ a).coeff ij.1 *
      ((C 2 + X : Real[X]) ^ d).coeff ij.2
  have hnonneg (ij : Nat × Nat) : 0 <= f ij :=
    mul_nonneg
      (Polynomial.coeffNonnegative_pow
        Polynomial.coeffNonnegative_two_add_X a ij.1)
      (Polynomial.coeffNonnegative_pow
        Polynomial.coeffNonnegative_two_add_X d ij.2)
  have hsingle : f (k, 0) <=
      ∑ ij ∈ Finset.antidiagonal k, f ij := by
    apply Finset.single_le_sum
    · intro ij hij
      exact hnonneg ij
    · exact Finset.mem_antidiagonal.mpr rfl
  have hconst : ((C 2 + X : Real[X]) ^ d).coeff 0 = 2 ^ d := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow]
    simp
  have hcoeffNonneg : 0 <= ((C 2 + X : Real[X]) ^ a).coeff k :=
    Polynomial.coeffNonnegative_pow
      Polynomial.coeffNonnegative_two_add_X a k
  have hpow : (1 : Real) <= 2 ^ d :=
    one_le_pow₀ (by norm_num)
  have hfirst : ((C 2 + X : Real[X]) ^ a).coeff k <= f (k, 0) := by
    dsimp [f]
    rw [hconst]
    nlinarith
  exact hfirst.trans (by simpa [f] using hsingle)



theorem exists_sixVertexLocalSwapTwo_markedCoefficient_le
    (p q : SixVertexLocalIncomingPattern) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice) (hd : p d ≠ q d)
    (hnotCC : Not (p.IsCType /\ q.IsCType)) :
    exists e : Fin 4,
      e ≠ d /\ p e ≠ q e /\
      (sixVertexLocalSwapTwo p q d e).1.Ice /\
      (sixVertexLocalSwapTwo p q d e).2.Ice /\
      forall k,
        (sixVertexLocalMarkedPatternWeight p *
            sixVertexLocalMarkedPatternWeight q).coeff k <=
          (sixVertexLocalMarkedPatternWeight
              (sixVertexLocalSwapTwo p q d e).1 *
            sixVertexLocalMarkedPatternWeight
              (sixVertexLocalSwapTwo p q d e).2).coeff k := by
  obtain ⟨e, hed, heq, hp', hq', hcount⟩ :=
    exists_sixVertexLocalSwapTwo_of_disagreement p q d hp hq hd hnotCC
  refine ⟨e, hed, heq, hp', hq', ?_⟩
  intro k
  rw [sixVertexLocalMarkedPatternWeight_mul_eq_pow p q hp hq,
    sixVertexLocalMarkedPatternWeight_mul_eq_pow _ _ hp' hq']
  exact coeff_two_add_X_pow_mono hcount k

end

end StatMech.FrontierD
