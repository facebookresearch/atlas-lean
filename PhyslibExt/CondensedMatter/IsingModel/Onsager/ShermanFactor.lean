/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanFirstReturn

/-!

# Factorized form of the rooted loop series

Powers of finite sums as sums over tuples and lists, and the `-log (1 - z)` identity in factorized
form.

## i. Overview

`(∑_{s ∈ S} wt s) ^ k` is the sum, over `k`-tuples (equivalently length-`k` lists) of elements of
`S`, of the products of their weights (Mathlib's `Finset.sum_pow'`). Feeding this into
`ons_lemma4_of_factorization` gives Sherman's Lemma 4 for a finite family of first-return loops: the
series `∑ₖ (tuple sum of length k + 1) / (k + 1)` equals `-log (1 - ∑ wt)` and its exponential is
`1 - ∑ wt`.

## ii. Key results

- `ons_pow_eq_sum_list` : a power of a finite sum as a sum over lists
- `ons_lemma4_factorized` : Sherman's Lemma 4 for a finite family

## iii. Table of contents

- A. Powers as sums over tuples and lists
- B. Lemma 4

## iv. References

- S. Sherman, *Combinatorial aspects of the Ising model for ferromagnetism. I. A conjecture of
  Feynman on paths and graphs*, J. Math. Phys. 1 (1960) 202-217

-/

@[expose] public section

namespace StatMech.Onsager

open Matrix BigOperators Finset Complex

set_option linter.unusedSectionVars false

section AbstractFactorCount

variable {α : Type*} [DecidableEq α]

/-! ## A. Powers as sums over tuples and lists -/

/-- The product over a tuple equals the product over the list `List.ofFn p`; see also
`List.prod_ofFn` and `List.map_ofFn`. -/
lemma ons_tupleProd_eq_listProd (wt : α → ℂ) {k : ℕ} (p : Fin k → α) :
    ∏ i : Fin k, wt (p i) = ((List.ofFn p).map wt).prod := by
  rw [List.map_ofFn, List.prod_ofFn]
  rfl

lemma ons_pow_eq_sum_list (S : Finset α) (wt : α → ℂ) (k : ℕ) :
    (∑ s ∈ S, wt s) ^ k
      = ∑ L ∈ (Fintype.piFinset (fun _ : Fin k => S)).image (fun p => List.ofFn p),
          (L.map wt).prod := by
  rw [Finset.sum_pow' S wt k]
  rw [Finset.sum_image (fun p _ q _ h => List.ofFn_injective h)]
  exact Finset.sum_congr rfl (fun p _ => ons_tupleProd_eq_listProd wt p)

end AbstractFactorCount

section Lemma4

variable {α : Type*} [DecidableEq α]

/-! ## B. Lemma 4 -/

lemma ons_lemma4_factorized (S : Finset α) (wt : α → ℂ) (hz : ‖∑ s ∈ S, wt s‖ < 1) :
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
    (fun k => (Finset.sum_pow' S wt (k + 1)).symm)

end Lemma4

end StatMech.Onsager
