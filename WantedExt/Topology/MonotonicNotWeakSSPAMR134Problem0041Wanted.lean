/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Monotonic versus weak sequence selection in C_p(X) (Tsaban, Milestone Problem 15.4)

B. Tsaban, Selection principles in mathematics: A milestone of open problems, Problem 15.4
(Scheepers, Problem 2): does the monotonic sequence selection property of `C_p(X)` imply the weak
sequence selection property?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.Topology.SelectionPrinciplesShared

@[expose] public section

namespace MathlibExt.Topology.MonotonicNotWeakSSPAMR134Problem0041Wanted

/-!
Source: B. Tsaban, Selection principles in mathematics: A milestone of open problems, Note di
Matematica 22 (2003/2004), arXiv:math/0312182, Problem 15.4 (M. Scheepers, Proc. Amer. Math. Soc.
125 (1997), Problem 2). UnsolvedMath record UM-00800669 (`AMR-134-0041`), dataset
ulamai/UnsolvedMath v1.8.0.

Following the source's convention (Section 2.3), `X` ranges over sets of reals. The monotonic
sequence selection property is the sequence selection property restricted to sequences `(f^n_k)_k`
that converge to `𝟎` pointwise and monotonically; as in Sakai's paper (zbMATH review Zbl 1109.54014)
monotone means `f^n_{k+1}(x) ≤ f^n_k(x)` for all `k` and `x`.
-/

open Filter MathlibExt.Topology.SelectionPrinciplesShared

/-- The monotonic sequence selection property of `C_p(X)` (Scheepers): for every sequence
`(f^n_k)_{k ∈ ℕ}`, `n ∈ ℕ`, of sequences in `C_p(X)` each converging pointwise and monotonically
(non-increasingly) to `𝟎`, there are indices `k_n` with `f^n_{k_n} → 𝟎`. -/
def HasMonotonicSSP (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ f : ℕ → ℕ → Cp X, (∀ n, Tendsto (f n) atTop (nhds (cpZero X))) →
    (∀ n k x, (f n (k + 1)).1 x ≤ (f n k).1 x) →
      ∃ k : ℕ → ℕ, Tendsto (fun n => f n (k n)) atTop (nhds (cpZero X))

/-- Tsaban, Milestone Problem 15.4 (Scheepers): for every set of reals `X`, the monotonic sequence
selection property of `C_p(X)` implies the weak sequence selection property of `C_p(X)`. -/
def monotonicSSPImpliesWeakSSP : Prop :=
  ∀ X : Set ℝ, HasMonotonicSSP X → HasWeakSSP X

/--
Resolved false: Sakai proved that `C_p(X)` has the weak sequence selection property only when `X` is
zero-dimensional, so `C_p([0, 1])` lacks it, while monotone pointwise convergence to `𝟎` on the
compact space `[0, 1]` is uniform (Dini), which gives the monotonic sequence selection property; the
problem list's Notes added in proof record the negative answer. Source: B. Tsaban, Selection
principles in mathematics: A milestone of open problems, Note di Matematica 22 (2003/2004),
arXiv:math/0312182, Problem 15.4 (M. Scheepers, Proc. Amer. Math. Soc. 125 (1997), Problem 2);
resolution: M. Sakai, The sequence selection properties of C_p(X), Topology Appl. 154 (2007),
552-560, doi:10.1016/j.topol.2006.07.008, zbMATH review Zbl 1109.54014 (T. Natkaniec): if C_p(X) has
the weak sequence selection property then X is zero-dimensional, so C_p([0,1]) does not have it,
which solves problems of Scheepers; the problem list's Notes added in proof: 'Sakai also settled
Problems 15.3 and 15.4 in the negative', https://doi.org/10.1016/j.topol.2006.07.008.
-/
public theorem_wanted monotonicSSPImpliesWeakSSP_refuted : ¬ monotonicSSPImpliesWeakSSP

end MathlibExt.Topology.MonotonicNotWeakSSPAMR134Problem0041Wanted
