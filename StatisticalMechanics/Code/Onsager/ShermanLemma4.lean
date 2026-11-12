/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.ShermanLoop



















































namespace StatMech.Onsager

open Matrix BigOperators Finset

section Orbit

variable {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ} [NeZero n]



theorem ons_cyclicShift_iterate_apply (v : Fin n → E) (j : ℕ) :
    ons_cyclicShift^[j] v = fun k => v (k + Fin.ofNat n j) := by
  induction j with
  | zero =>
    funext k
    simp [Fin.ofNat]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold ons_cyclicShift
    funext k
    show v ((k + 1) + Fin.ofNat n j) = v (k + Fin.ofNat n (j + 1))
    congr 1
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_ofNat, Fin.val_one', Nat.mod_add_mod, Nat.add_mod_mod]
    congr 1
    omega



theorem ons_cyclicShift_iterate_self (v : Fin n → E) :
    ons_cyclicShift^[n] v = v := by
  rw [ons_cyclicShift_iterate_apply]
  funext k
  congr 1
  apply Fin.ext
  simp


theorem ons_cyclicShift_iterate_eq_id :
    ons_cyclicShift^[n] = (id : (Fin n → E) → Fin n → E) := by
  funext v
  exact ons_cyclicShift_iterate_self v


theorem ons_cyclicShift_iterate_mul_self (v : Fin n → E) (j : ℕ) :
    ons_cyclicShift^[n * j] v = v := by
  have h : ons_cyclicShift^[n * j] = (id : (Fin n → E) → Fin n → E) := by
    rw [Function.iterate_mul, ons_cyclicShift_iterate_eq_id, Function.iterate_id]
  rw [h]; rfl


theorem ons_cyclicShift_iterate_mod (v : Fin n → E) (j : ℕ) :
    ons_cyclicShift^[j % n] v = ons_cyclicShift^[j] v := by
  conv_rhs => rw [← Nat.div_add_mod j n]
  rw [Function.iterate_add_apply, ons_cyclicShift_iterate_mul_self]




def ons_orbitSetoid (E : Type*) [Fintype E] [DecidableEq E] (n : ℕ) [NeZero n] :
    Setoid (Fin n → E) where
  r v w := ∃ j : ℕ, ons_cyclicShift^[j] v = w
  iseqv :=
    { refl := fun _ => ⟨0, rfl⟩
      symm := by
        rintro v w ⟨j, rfl⟩
        refine ⟨(n - 1) * j, ?_⟩
        have hmul : (n - 1) * j + j = n * j := by
          have h1 : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos (Nat.pos_of_neZero n)
          calc (n - 1) * j + j = (n - 1) * j + 1 * j := by rw [one_mul]
            _ = (n - 1 + 1) * j := by rw [add_mul]
            _ = n * j := by rw [h1]
        rw [← Function.iterate_add_apply, hmul, ons_cyclicShift_iterate_mul_self]
      trans := by
        rintro u v w ⟨i, rfl⟩ ⟨j, rfl⟩
        exact ⟨j + i, by rw [Function.iterate_add_apply]⟩ }



noncomputable def ons_rep (v : Fin n → E) : Fin n → E :=
  (Quotient.mk (ons_orbitSetoid E n) v).out


theorem ons_rep_rel (v : Fin n → E) :
    (ons_orbitSetoid E n).r (ons_rep v) v :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (ons_orbitSetoid E n) v))


noncomputable def ons_orbitCard (r : Fin n → E) : ℕ :=
  (Finset.univ.filter (fun v => ons_rep v = r)).card


theorem ons_iterate_inv {f : (Fin n → E) → ℂ}
    (hf : ∀ v, f (ons_cyclicShift v) = f v) (v : Fin n → E) (j : ℕ) :
    f (ons_cyclicShift^[j] v) = f v := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', hf, ih]


theorem ons_eq_of_rel {f : (Fin n → E) → ℂ}
    (hf : ∀ v, f (ons_cyclicShift v) = f v) {v w : Fin n → E}
    (h : (ons_orbitSetoid E n).r v w) : f v = f w := by
  obtain ⟨j, hj⟩ := h
  have := ons_iterate_inv hf v j
  rw [hj] at this
  exact this.symm









theorem ons_sum_fiberwise_orbit {f : (Fin n → E) → ℂ}
    (hf : ∀ v, f (ons_cyclicShift v) = f v) :
    ∑ v : Fin n → E, f v
      = ∑ r : Fin n → E, (ons_orbitCard r : ℂ) * f r := by
  have key : ∀ r : Fin n → E,
      (∑ v ∈ Finset.univ.filter (fun v => ons_rep v = r), f v)
        = (ons_orbitCard r : ℂ) * f r := by
    intro r
    have h1 : (∑ v ∈ Finset.univ.filter (fun v => ons_rep v = r), f v)
        = ∑ _v ∈ Finset.univ.filter (fun v => ons_rep v = r), f r := by
      apply Finset.sum_congr rfl
      intro v hv
      have hrep : ons_rep v = r := (Finset.mem_filter.mp hv).2
      have hval : f (ons_rep v) = f v := ons_eq_of_rel hf (ons_rep_rel v)
      rw [← hval, hrep]
    rw [h1, Finset.sum_const, nsmul_eq_mul]
    rfl
  calc
    ∑ v : Fin n → E, f v
        = ∑ r : Fin n → E, ∑ v ∈ Finset.univ.filter (fun v => ons_rep v = r), f v :=
          (Finset.sum_fiberwise Finset.univ ons_rep f).symm
    _ = ∑ r : Fin n → E, (ons_orbitCard r : ℂ) * f r :=
          Finset.sum_congr rfl (fun r _ => key r)





theorem ons_sum_loopWeight_orbit (Λ : Matrix E E ℂ) :
    ∑ v : Fin n → E, ons_loopWeight Λ v
      = ∑ r : Fin n → E, (ons_orbitCard r : ℂ) * ons_loopWeight Λ r :=
  ons_sum_fiberwise_orbit (ons_loopWeight_cyclicShift Λ)

end Orbit

section LogTail

open Complex





theorem ons_hasSum_shifted_pow_div {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => z ^ (k + 1) / (k + 1)) (-Complex.log (1 - z)) := by
  have h := Complex.hasSum_taylorSeries_neg_log hz
  
  have h2 := (hasSum_nat_add_iff' (f := fun n : ℕ => z ^ n / (n : ℂ)) 1).mpr h
  simpa using h2


theorem ons_tsum_shifted_pow_div {z : ℂ} (hz : ‖z‖ < 1) :
    ∑' k : ℕ, z ^ (k + 1) / (k + 1) = -Complex.log (1 - z) :=
  (ons_hasSum_shifted_pow_div hz).tsum_eq

end LogTail

end StatMech.Onsager
