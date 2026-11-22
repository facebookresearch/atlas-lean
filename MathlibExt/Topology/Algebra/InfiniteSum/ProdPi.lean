/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Data.Fintype.Option

/-!
# Sums of finite products over a function space

For nonnegative summable families `f i : κ → ℝ` indexed by a finite type `ι`, the products
`x ↦ ∏ i, f i (x i)` are summable over the function space `ι → κ`, and their sum is the product
of the sums. This is the infinite-sum version of `Finset.prod_univ_sum`; Mathlib has the
two-factor case `HasSum.mul`.

## Main results

* `hasSum_prod_pi`: if `0 ≤ f i k` and `HasSum (f i) (a i)` for every `i`, then
  `HasSum (fun x : ι → κ => ∏ i, f i (x i)) (∏ i, a i)`.

## Implementation notes

The proof is by induction over the finite index type (`Fintype.induction_empty_option`), with
`HasSum.mul` and `summable_mul_of_summable_norm` for the step `Option ι`.
-/

@[expose] public section

namespace MetaMathlibExt

open Finset

universe u

private theorem hasSum_prod_pi_aux {κ : Type*} :
    ∀ (ι : Type u) [Fintype ι] (f : ι → κ → ℝ) (a : ι → ℝ), (∀ i k, 0 ≤ f i k) →
      (∀ i, HasSum (f i) (a i)) → HasSum (fun x : ι → κ => ∏ i, f i (x i)) (∏ i, a i) := by
  refine Fintype.induction_empty_option ?_ ?_ ?_
  · intro α β _ e ih f a hf0 hf
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (fun i => f (e i)) (fun i => a (e i)) (fun i k => hf0 _ k) (fun i => hf _)
    rw [← (e.arrowCongr (Equiv.refl κ)).symm.hasSum_iff] at h
    rw [← Fintype.prod_equiv e (fun i => a (e i)) a (fun _ => rfl)]
    refine h.congr_fun fun x => ?_
    change ∏ b, f b (x b) = ∏ i, f (e i) (x (e i))
    exact (Fintype.prod_equiv e _ _ fun _ => rfl).symm
  · intro f a _ _
    simp
  · intro α _ ih f a hf0 hf
    have hg := ih (fun i => f (some i)) (fun i => a (some i)) (fun i k => hf0 _ k)
      (fun i => hf _)
    have hn : ∀ i, Summable fun k => ‖f i k‖ := fun i =>
      (hf i).summable.congr fun k => (Real.norm_of_nonneg (hf0 i k)).symm
    have hgn : Summable fun y : α → κ => ‖∏ i, f (some i) (y i)‖ :=
      hg.summable.congr fun y =>
        (Real.norm_of_nonneg (prod_nonneg fun i _ => hf0 _ _)).symm
    have hs : Summable fun z : κ × (α → κ) => f none z.1 * ∏ i, f (some i) (z.2 i) :=
      summable_mul_of_summable_norm (f := f none) (g := fun y : α → κ => ∏ i, f (some i) (y i))
        (hn none) hgn
    have hmul := HasSum.mul (f := f none) (g := fun y : α → κ => ∏ i, f (some i) (y i))
      (hf none) hg hs
    rw [← (Equiv.piOptionEquivProd (β := fun _ : Option α => κ)).hasSum_iff] at hmul
    rw [Fintype.prod_option]
    refine hmul.congr_fun fun x => ?_
    simp [Fintype.prod_option]

/-- A finite product of nonnegative summable families is summable over the function space, with
sum the product of the sums: `∑_{x : ι → κ} ∏ i, f i (x i) = ∏ i, ∑_k f i k`. -/
theorem hasSum_prod_pi {ι : Type u} {κ : Type*} [Fintype ι] {f : ι → κ → ℝ} {a : ι → ℝ}
    (hf0 : ∀ i k, 0 ≤ f i k) (hf : ∀ i, HasSum (f i) (a i)) :
    HasSum (fun x : ι → κ => ∏ i, f i (x i)) (∏ i, a i) :=
  hasSum_prod_pi_aux ι f a hf0 hf

end MetaMathlibExt
