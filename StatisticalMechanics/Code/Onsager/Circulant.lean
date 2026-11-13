/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


















namespace StatMech.Onsager

open scoped Matrix

theorem ons_det_circulant (n : ℕ) [NeZero n] (ω : ℂ) (hω : IsPrimitiveRoot ω n)
    (v : Fin n → ℂ) :
    (Matrix.circulant v).det = ∏ j : Fin n, (∑ k : Fin n, v k * ω ^ ((k : ℕ) * (j : ℕ))) := by
  
  have hpm : ∀ x : ℕ, ω ^ (x % n) = ω ^ x := by
    intro x
    conv_rhs => rw [← Nat.div_add_mod x n]
    rw [pow_add, pow_mul, hω.pow_eq_one, one_pow, one_mul]
  
  have hadd : ∀ a b : Fin n, ω ^ (((a + b : Fin n) : ℕ)) = ω ^ (a : ℕ) * ω ^ (b : ℕ) := by
    intro a b
    rw [Fin.val_add, hpm, pow_add]
  
  set F : Matrix (Fin n) (Fin n) ℂ := Matrix.vandermonde (fun i => ω ^ (i : ℕ)) with hF
  have hFij : ∀ i j : Fin n, F i j = ω ^ ((i : ℕ) * (j : ℕ)) := by
    intro i j
    rw [hF, Matrix.vandermonde_apply, ← pow_mul]
  
  have hinj : Function.Injective (fun i : Fin n => ω ^ (i : ℕ)) := by
    intro i j h
    exact Fin.ext (hω.pow_inj i.isLt j.isLt h)
  have hdetF : F.det ≠ 0 := by
    rw [hF]; exact Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  
  set D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => ∑ k : Fin n, v k * ω ^ ((k : ℕ) * (i : ℕ))) with hD
  
  have hkey : F * Matrix.circulant v = D * F := by
    ext i j
    rw [Matrix.mul_apply, Matrix.diagonal_mul]
    
    have hreindex :
        (∑ l : Fin n, F i l * Matrix.circulant v l j)
          = ∑ k : Fin n, ω ^ ((i : ℕ) * (((k + j : Fin n)) : ℕ)) * v k := by
      refine (Fintype.sum_equiv (Equiv.addRight j)
        (fun k : Fin n => ω ^ ((i : ℕ) * (((k + j : Fin n)) : ℕ)) * v k)
        (fun l : Fin n => F i l * Matrix.circulant v l j) ?_).symm
      intro k
      simp only [Equiv.coe_addRight]
      rw [Matrix.circulant_apply, hFij, add_sub_cancel_right]
    rw [hreindex]
    
    have hstep : ∀ k : Fin n,
        ω ^ ((i : ℕ) * (((k + j : Fin n)) : ℕ)) * v k
          = (v k * ω ^ ((k : ℕ) * (i : ℕ))) * ω ^ ((i : ℕ) * (j : ℕ)) := by
      intro k
      rw [pow_mul', hadd, mul_pow, ← pow_mul, ← pow_mul]
      ring_nf
    simp_rw [hstep]
    rw [← Finset.sum_mul, hFij]
  
  have hdet : F.det * (Matrix.circulant v).det = D.det * F.det := by
    rw [← Matrix.det_mul, ← Matrix.det_mul, hkey]
  have hcirc : (Matrix.circulant v).det = D.det := by
    have h2 : (Matrix.circulant v).det * F.det = D.det * F.det := by
      rw [mul_comm]; exact hdet
    exact mul_right_cancel₀ hdetF h2
  rw [hcirc, hD, Matrix.det_diagonal]

end StatMech.Onsager
