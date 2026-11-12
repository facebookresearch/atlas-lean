/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.KWMatrix
import Code.Onsager.TurningTelescope

















namespace StatMech.Onsager





theorem ons_turnPow_rev (μ ν : Fin 4) :
    ons_turnPow (ν + 2) (μ + 2) = - ons_turnPow μ ν := by
  fin_cases μ <;> fin_cases ν <;> decide






theorem ons_turnW_rev (ω : ℂ) (μ ν : Fin 4) :
    ons_turnW ω (ν + 2) (μ + 2) = (ons_turnW ω μ ν)⁻¹ := by
  fin_cases μ <;> fin_cases ν <;> simp [ons_turnW]






theorem ons_turnPow_sum_rev (n : ℕ) (d : Fin (n + 1) → Fin 4) :
    (∑ k : Fin n, ons_turnPow ((fun j => d (Fin.rev j) + 2) k.castSucc)
        ((fun j => d (Fin.rev j) + 2) k.succ))
      = - ∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ) := by
  
  have e1 : ∀ k : Fin n, Fin.rev k.succ = (Fin.rev k).castSucc := by
    intro k; apply Fin.ext
    simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega
  have e2 : ∀ k : Fin n, Fin.rev k.castSucc = (Fin.rev k).succ := by
    intro k; apply Fin.ext
    simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega
  
  have key : ∀ k : Fin n,
      ons_turnPow ((fun j => d (Fin.rev j) + 2) k.castSucc)
          ((fun j => d (Fin.rev j) + 2) k.succ)
        = - ons_turnPow (d ((Fin.rev k).castSucc)) (d ((Fin.rev k).succ)) := by
    intro k
    simp only []
    rw [ons_turnPow_rev (d (Fin.rev k.succ)) (d (Fin.rev k.castSucc)), e1 k, e2 k]
  
  let e : Fin n ≃ Fin n := ⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩
  calc (∑ k : Fin n, ons_turnPow ((fun j => d (Fin.rev j) + 2) k.castSucc)
          ((fun j => d (Fin.rev j) + 2) k.succ))
      = ∑ k : Fin n, - ons_turnPow (d ((Fin.rev k).castSucc)) (d ((Fin.rev k).succ)) := by
        exact Finset.sum_congr rfl (fun k _ => key k)
    _ = - ∑ k : Fin n, ons_turnPow (d ((Fin.rev k).castSucc)) (d ((Fin.rev k).succ)) := by
        rw [Finset.sum_neg_distrib]
    _ = - ∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ) := by
        congr 1
        exact Equiv.sum_comp e (fun k => ons_turnPow (d k.castSucc) (d k.succ))

end StatMech.Onsager
