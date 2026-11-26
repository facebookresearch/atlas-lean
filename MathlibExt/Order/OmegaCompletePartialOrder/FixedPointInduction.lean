/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Order.OmegaCompletePartialOrder.ContinuousHom

/-!
# Fixed-point induction for Scott-continuous maps

Scott's fixed-point induction principle on ω-complete partial orders: if a predicate holds at
`⊥`, is closed under suprema of ω-chains, and is preserved by a Scott-continuous map `f`, then
it holds at the least fixed point `ContinuousHom.lfp f`, the supremum of the Kleene chain
`⊥ ≤ f ⊥ ≤ f (f ⊥) ≤ ⋯`.

* `ContinuousHom.Admissible P`: `P` holds at `⊥` and at the supremum of every ω-chain on which
  it holds everywhere. In Winskel's terms, `P` contains `⊥` and is inclusive.
* `ContinuousHom.lfp_induction`: fixed-point induction for admissible predicates.

Mathlib's `OrderHom.lfp_induction` states induction for least fixed points in complete lattices,
with closure under arbitrary suprema. The principle here needs only suprema of ω-chains, so it
applies to ω-complete partial orders that are not complete lattices, such as the flat domain
`Part ℕ` of partial natural numbers.

## References

* G. Winskel, *The Formal Semantics of Programming Languages*, MIT Press, 1993, §10.2
  (Proposition 10.4, fixed-point induction, due to Scott).
-/

@[expose] public section

namespace OmegaCompletePartialOrder.ContinuousHom

variable {D : Type*} [OmegaCompletePartialOrder D] [OrderBot D]

/-- **Admissible predicate.** A predicate $P$ on an ω-complete partial order $D$ with a least
element $\bot$ is admissible when $P(\bot)$ holds and $P$ is closed under suprema of ω-chains:
for every chain $c_0 \le c_1 \le \cdots$ in $D$ with $P(c_i)$ for all $i$, also
$P(\bigsqcup_i c_i)$. In the terminology of Winskel (§10.2), $P$ contains $\bot$ and is
inclusive. -/
def Admissible (P : D → Prop) : Prop :=
  P ⊥ ∧ ∀ c : Chain D, (∀ i, P (c i)) → P (ωSup c)

/-- **Fixed-point induction (Scott).** Let $D$ be an ω-complete partial order with a least
element $\bot$, let $f : D \to D$ be Scott-continuous, that is, monotone and preserving suprema
of ω-chains, and let $P$ be an admissible predicate on $D$: $P(\bot)$ holds and $P$ is closed
under suprema of ω-chains. If $P(x)$ implies $P(f(x))$ for every $x \in D$, then $P$ holds at
the least fixed point $\operatorname{lfp} f = \bigsqcup_n f^n(\bot)$ (Winskel, Proposition
10.4). -/
theorem lfp_induction (f : D →𝒄 D) {P : D → Prop} (hP : Admissible P)
    (hstep : ∀ x, P x → P (f x)) : P (lfp f) :=
  by
    rw [lfp_def]
    refine hP.2 _ fun n => ?_
    change P (f^[n] ⊥)
    induction n with
    | zero => exact hP.1
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hstep _ ih

end OmegaCompletePartialOrder.ContinuousHom
