/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.ShermanLoop
import Code.Onsager.ShermanLemma4
import Code.Onsager.ShermanLemma4Return
































































namespace StatMech.Onsager

open Matrix BigOperators Finset Complex

set_option linter.unusedSectionVars false

section AbstractFactorCount

variable {α : Type*} [DecidableEq α]











theorem ons_factorTupleSum_eq_pow (S : Finset α) (wt : α → ℂ) (k : ℕ) :
    (∑ p ∈ Fintype.piFinset (fun _ : Fin k => S), ∏ i : Fin k, wt (p i))
      = (∑ s ∈ S, wt s) ^ k :=
  (ons_pow_eq_sum_tuple S wt k).symm





theorem ons_tupleProd_eq_listProd (wt : α → ℂ) {k : ℕ} (p : Fin k → α) :
    ∏ i : Fin k, wt (p i) = ((List.ofFn p).map wt).prod := by
  rw [List.map_ofFn, List.prod_ofFn]
  rfl











theorem ons_pow_eq_sum_list (S : Finset α) (wt : α → ℂ) (k : ℕ) :
    (∑ s ∈ S, wt s) ^ k
      = ∑ L ∈ (Fintype.piFinset (fun _ : Fin k => S)).image (fun p => List.ofFn p),
          (L.map wt).prod := by
  rw [ons_pow_eq_sum_tuple S wt k]
  rw [Finset.sum_image (fun p _ q _ h => List.ofFn_injective h)]
  exact Finset.sum_congr rfl (fun p _ => ons_tupleProd_eq_listProd wt p)

end AbstractFactorCount

section Lemma4

variable {α : Type*} [DecidableEq α]









theorem ons_factor_hcount (S : Finset α) (wt : α → ℂ) (k : ℕ) :
    (∑ p ∈ Fintype.piFinset (fun _ : Fin (k + 1) => S), ∏ i : Fin (k + 1), wt (p i))
      = (∑ s ∈ S, wt s) ^ (k + 1) :=
  ons_factorTupleSum_eq_pow S wt (k + 1)













theorem ons_lemma4_factorized (S : Finset α) (wt : α → ℂ) (hz : ‖∑ s ∈ S, wt s‖ < 1) :
    (∑' k : ℕ,
        (∑ p ∈ Fintype.piFinset (fun _ : Fin (k + 1) => S), ∏ i : Fin (k + 1), wt (p i))
          / (k + 1))
        = -Complex.log (1 - ∑ s ∈ S, wt s) ∧
      Complex.exp
          (-(∑' k : ℕ,
            (∑ p ∈ Fintype.piFinset (fun _ : Fin (k + 1) => S), ∏ i : Fin (k + 1), wt (p i))
              / (k + 1)))
        = 1 - ∑ s ∈ S, wt s :=
  ons_lemma4_of_factorization hz
    (fun k => ∑ p ∈ Fintype.piFinset (fun _ : Fin (k + 1) => S), ∏ i : Fin (k + 1), wt (p i))
    (ons_factor_hcount S wt)

end Lemma4

end StatMech.Onsager
