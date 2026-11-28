/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The weak sequence selection property of pointwise function spaces

The topology on `C_p(X)` is the pointwise topology inherited from the product `ℝ^X`.

## References

* Marion Scheepers, *A sequential property of Cₚ(X) and a covering property of Hurewicz*,
  Proceedings of the American Mathematical Society 125 (1997), 2789–2795, p. 2790.
* Boaz Tsaban, *Selection principles in mathematics: A milestone of open problems*,
  Note di Matematica 22 (2003/2004), no. 2, 179–208, Section 15.
-/

@[expose] public section

open Set Filter Topology

namespace MathlibExt.Topology.SelectionPrinciplesShared

/-- `C_p(X)`: continuous real-valued functions on `X` with the pointwise (product) topology. -/
abbrev Cp (X : Type*) [TopologicalSpace X] : Type _ := {f : X → ℝ // Continuous f}

/-- The constant zero function `𝟎` as a point of `C_p(X)`. -/
def cpZero (X : Type*) [TopologicalSpace X] : Cp X := ⟨fun _ => 0, continuous_const⟩

/-- The weak sequence selection property of `C_p(X)` (Scheepers; Tsaban, Section 15): for every
sequence `(f^n_k)_{k ∈ ℕ}`, `n ∈ ℕ`, of sequences in `C_p(X)` each converging to `𝟎`, there are
indices `k_n` with `𝟎` in the closure of `{f^n_{k_n} : n ∈ ℕ}`. -/
def HasWeakSSP (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ f : ℕ → ℕ → Cp X, (∀ n, Tendsto (f n) atTop (𝓝 (cpZero X))) →
    ∃ k : ℕ → ℕ, cpZero X ∈ closure (range fun n => f n (k n))

end MathlibExt.Topology.SelectionPrinciplesShared
