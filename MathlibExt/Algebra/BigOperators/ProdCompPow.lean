/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
# Products over a finite type regrouped by value

`Fintype.prod_comp_eq_prod_pow`: `∏ b, f (g b) = ∏ c, f c ^ #{b | g b = c}`, a version of
Mathlib's `Finset.prod_comp` whose outer product runs over the whole codomain instead of the image.
It turns the likelihood of i.i.d. categorical observations into a product of powers of counts.
-/

@[expose] public section

namespace Fintype

open Finset

/-- **Products regrouped by the values of a function.** Let $\beta$ and $\gamma$ be finite types,
let $M$ be a commutative monoid, and let $g : \beta \to \gamma$ and $f : \gamma \to M$. Then

$$\prod_{b \in \beta} f(g(b)) = \prod_{c \in \gamma} f(c)^{\#\{b \in \beta \mid g(b) = c\}},$$

where the product on the right runs over all of $\gamma$ and $\#\{b \in \beta \mid g(b) = c\}$ is
the number of elements $b$ of $\beta$ with $g(b) = c$. -/
theorem prod_comp_eq_prod_pow {β γ M : Type*} [Fintype β] [Fintype γ] [DecidableEq γ]
    [CommMonoid M] (g : β → γ) (f : γ → M) :
    ∏ b, f (g b) = ∏ c, f c ^ (univ.filter fun b => g b = c).card := by
  rw [← Finset.prod_fiberwise univ g fun b => f (g b)]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [Finset.prod_congr rfl fun b hb => by rw [(mem_filter.1 hb).2], Finset.prod_const]

end Fintype
