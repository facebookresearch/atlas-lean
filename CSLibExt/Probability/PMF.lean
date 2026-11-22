/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Probability.PMF

/-!
# Probability mass functions: uniform distributions and coin fixing

Facts about probability mass functions in the style of CSLib's `Cslib.Probability.PMF`:

* `uniformOfFintype_fin_succ`: a uniform function `Fin (n + 1) → X` is a uniform head followed by
  an independent uniform tail, joined by `Fin.cons`.
* `uniformOfFintype_unique`: on a type with exactly one element the uniform distribution is the
  point mass at that element.
* `exists_mem_support_bind_apply_le` (**coin fixing**): for every outcome `b`, some `a` in the
  support of `p` does at least as well as the average, `(p.bind f) b ≤ f a b`. Fixing an
  adversary's coins to such an `a` turns a bound for deterministic adversaries into one for
  adversaries with arbitrary coins.
-/

@[expose] public section

namespace Cslib.Probability.PMF

/-- A uniform function on `Fin (n + 1)` is a uniform head followed by an independent uniform
tail. -/
theorem uniformOfFintype_fin_succ (X : Type*) [Fintype X] [Nonempty X] (n : ℕ) :
    uniformOfFintype (Fin (n + 1) → X) =
      (uniformOfFintype X).bind fun x => (uniformOfFintype (Fin n → X)).map (Fin.cons x) := by
  let e : X × (Fin n → X) ≃ (Fin (n + 1) → X) :=
    { toFun := fun p => Fin.cons p.1 p.2
      invFun := fun f => (f 0, Fin.tail f)
      left_inv := fun p => by simp
      right_inv := fun f => by simp }
  rw [← uniformOfFintype_map_equiv e, ← uniformOfFintype_prod, PMF.map_bind]
  congr 1
  funext x
  rw [PMF.map_comp]
  rfl

/-- The uniform distribution on a type with one element is the point mass. -/
theorem uniformOfFintype_unique (α : Type*) [Fintype α] [Unique α] :
    uniformOfFintype α = PMF.pure default := by
  ext a
  simp [Fintype.card_unique, Unique.eq_default a]

/-- **Coin fixing**: some outcome `a` in the support of `p` does at least as well as the average
`(p.bind f) b`. -/
theorem exists_mem_support_bind_apply_le {α β : Type*} (p : PMF α) (f : α → PMF β) (b : β) :
    ∃ a ∈ p.support, (p.bind f) b ≤ f a b := by
  by_contra! hlt
  obtain ⟨a, ha⟩ := p.support_nonempty
  have hne : ∑' x, p x * f x b ≠ ⊤ := by rw [← PMF.bind_apply]; exact PMF.apply_ne_top _ _
  have : (p.bind f) b < (p.bind f) b := by
    calc (p.bind f) b = ∑' x, p x * f x b := PMF.bind_apply _ _ _
      _ < ∑' x, p x * (p.bind f) b := by
        refine ENNReal.tsum_lt_tsum (i := a) hne (fun x => ?_) ?_
        · by_cases hx : x ∈ p.support
          · gcongr
            exact (hlt x hx).le
          · simp [(PMF.apply_eq_zero_iff p x).mpr hx]
        · exact ENNReal.mul_lt_mul_right ((PMF.mem_support_iff p a).mp ha) (PMF.apply_ne_top p a)
            (hlt a ha)
      _ = (p.bind f) b := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  exact lt_irrefl _ this

end Cslib.Probability.PMF
