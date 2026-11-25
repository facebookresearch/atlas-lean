/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

/-!
# Inverse limits of spaces over a preorder

This module formalizes the concrete inverse limit from ATLAS NumberTheoryI
Definition 8.9: for a family `X` of spaces indexed by a preorder and
transition maps `f h : X j → X i` for `h : i ≤ j`, the inverse limit is the
set of compatible dependent functions, that is, tuples `x` satisfying
`f h (x j) = x i` for every `h : i ≤ j`.

It also formalizes the topological half of Proposition 8.10: the limit set is
closed when every factor is Hausdorff and every transition map is continuous,
and hence compact when every factor is compact.

## Main definitions

* `InverseLimit.carrier`: the set of compatible tuples.

## Main results

* `InverseLimit.proj_compat`: elements of the limit project compatibly.
* `InverseLimit.isClosed_carrier`: the limit set is closed in the product.
* `InverseLimit.isCompact_carrier`: the limit set is compact in the product.

## References

* ATLAS NumberTheoryI, Definition 8.9 (inverse limit as compatible tuples)
  and Proposition 8.10 (closedness and compactness of the limit).
-/

namespace InverseLimit

variable {ι : Type*} [Preorder ι]
variable {X : ι → Type*}

/-- **Inverse limit as compatible tuples.** Let $I$ be a preordered set, let $(X_i)_{i \in I}$
be a family of sets, and for every $i \le j$ let $f_{ij} \colon X_j \to X_i$ be a map. The inverse
limit is the set of tuples $x = (x_i)_{i \in I}$ in the product $\prod_{i \in I} X_i$ such that
$f_{ij}(x_j) = x_i$ whenever $i \le j$.

Source: ATLAS NumberTheoryI, Definition 8.9. -/
def carrier (f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i) : Set (∀ i, X i) :=
  { x | ∀ ⦃i j : ι⦄ (h : i ≤ j), f h (x j) = x i }

/-- **Membership in the inverse limit.** Let $I$ be a preordered set, let $(X_i)_{i \in I}$ be a
family of sets, and for every $i \le j$ let $f_{ij} \colon X_j \to X_i$ be a map. A tuple
$x \in \prod_{i \in I} X_i$ lies in the inverse limit if and only if $f_{ij}(x_j) = x_i$ for all
$i \le j$. -/
@[simp]
theorem mem_carrier_iff {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
    {x : ∀ i, X i} :
    x ∈ carrier f ↔ ∀ ⦃i j : ι⦄ (h : i ≤ j), f h (x j) = x i :=
  Iff.rfl

/-- **Elements of the inverse limit are compatible.** Let $I$ be a preordered set, let
$(X_i)_{i \in I}$ be a family of sets, and for every $i \le j$ let $f_{ij} \colon X_j \to X_i$ be
a map. If $x = (x_i)_{i \in I}$ lies in the inverse limit, then $f_{ij}(x_j) = x_i$ for all
$i \le j$. -/
theorem proj_compat {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
    {x : ∀ i, X i} (hx : x ∈ carrier f) ⦃i j : ι⦄ (h : i ≤ j) :
    f h (x j) = x i :=
  hx h

variable [∀ i, TopologicalSpace (X i)]

/-- **The inverse limit is closed.** Let $I$ be a preordered set, let $(X_i)_{i \in I}$ be a
family of Hausdorff topological spaces, and for every $i \le j$ let $f_{ij} \colon X_j \to X_i$
be a continuous map. Then the inverse limit
$\{x \in \prod_{i \in I} X_i : f_{ij}(x_j) = x_i \text{ for all } i \le j\}$ is closed in the
product $\prod_{i \in I} X_i$.

Each equation $f_{ij}(x_j) = x_i$ cuts out a closed set because $X_i$ is Hausdorff, and the
limit is the intersection of all of them. -/
theorem isClosed_carrier [∀ i, T2Space (X i)]
    {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
    (hf : ∀ ⦃i j : ι⦄ (h : i ≤ j), Continuous (f h)) :
    IsClosed (carrier f) := by
  have heq : carrier f =
      ⋂ (i : ι) (j : ι) (h : i ≤ j), { x | f h (x j) = x i } := by
    ext x
    simp [carrier]
  rw [heq]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun h =>
    isClosed_eq ((hf h).comp (continuous_apply j)) (continuous_apply i)

/-- **The inverse limit of compact Hausdorff spaces is compact.** Let $I$ be a preordered set, let
$(X_i)_{i \in I}$ be a family of compact Hausdorff topological spaces, and for every $i \le j$
let $f_{ij} \colon X_j \to X_i$ be a continuous map. Then the inverse limit
$\{x \in \prod_{i \in I} X_i : f_{ij}(x_j) = x_i \text{ for all } i \le j\}$ is compact in the
product $\prod_{i \in I} X_i$.

It is a closed subset of a compact product. -/
theorem isCompact_carrier [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)]
    {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
    (hf : ∀ ⦃i j : ι⦄ (h : i ≤ j), Continuous (f h)) :
    IsCompact (carrier f) :=
  (isClosed_carrier hf).isCompact

end InverseLimit
