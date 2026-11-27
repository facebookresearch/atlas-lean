/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.WeightedProjectiveSimplexReflexive

/-!
# One-supported IDP reflexive weighted simplices

A reflexive weighted projective simplex with IDP and a single support value has weight one.
The support remainder identity reduces to `1 + x * (r % r) = r` for the repeated weight `r`.
-/

namespace MetaMathlibExt

/-- **One-supported IDP reflexive weighted simplices have all weights one.** Let $r \ge 1$ and
$x \ge 1$ be natural numbers, and let $q = (r, \dots, r)$ be the weight vector consisting of $x$
copies of $r$. If the weighted projective simplex with weights $q$ is reflexive and has the
integer decomposition property, then $r = 1$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Proposition 1. -/
public theorem one_supported_idp_reflexive_support_eq_one (r x : ℕ)
    (hr : 1 ≤ r) (hx : 1 ≤ x)
    (href : IsReflexive (weightedSimplexList (List.replicate x r)))
    (hidp : HasIDP (weightedSimplexList (List.replicate x r))) : r = 1 := by
  have hvalid : ValidSupport (fun _ : Fin 1 => r) (fun _ => x) :=
    ⟨by decide, Function.injective_of_subsingleton _, fun _ => hr, fun _ => hx⟩
  have hexpand : expandSupport (fun _ : Fin 1 => r) (fun _ => x) = List.replicate x r := by
    simp [expandSupport, List.ofFn_succ]
  have h := idp_reflexive_implies_support_necessary _ _ hvalid
    (hexpand ▸ href) (hexpand ▸ hidp) 0
  simpa using h.symm

end MetaMathlibExt
