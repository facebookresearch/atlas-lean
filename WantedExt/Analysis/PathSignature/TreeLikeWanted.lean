/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.PathSignature.Basic
public import MathlibExt.Analysis.PathSignature.TreeLike
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Uniqueness of the signature up to tree-like equivalence (wanted)

Hambly and Lyons proved that a path of bounded variation has trivial signature exactly when it is
tree-like (B. Hambly and T. Lyons, *Uniqueness for the signature of a path of bounded variation
and the reduced path group*, Ann. of Math. 171 (2010), arXiv:math/0507536, Theorem 1), extending
Chen's theorem for irreducible piecewise regular paths. Boedihardjo, Geng, Lyons and Yang extended
it to weakly geometric rough paths (Adv. Math. 293 (2016), arXiv:1406.7871, Theorem 1.1).

We record Theorem 1 for absolutely continuous paths in `ℝ^d`, described by an integrable
velocity, which is the setting of `MathlibExt.Analysis.PathSignature.signature`; Hambly and
Lyons prove it for all paths of bounded variation.
-/

open MeasureTheory

@[expose] public section

namespace MathlibExt.Analysis.PathSignature.TreeLikeWanted

open MathlibExt.Analysis.PathSignature

/-- **Hambly–Lyons uniqueness theorem: trivial signature iff tree-like.** Let `T ≥ 0` and let
`X : [0, T] → ℝ^d` (Euclidean norm) be the absolutely continuous path `X_t = ∫_0^t v` with velocity
`v` integrable on `[0, T]`. Then `X` is tree-like (`IsTreeLike`) if and only if its signature over
`[0, T]` is trivial, `S(X)_{0,T} = 1 = (1, 0, 0, …)` (B. Hambly and T. Lyons, *Uniqueness for the
signature of a path of bounded variation and the reduced path group*, Ann. of Math. 171 (2010),
arXiv:math/0507536, Theorem 1, there for all paths of bounded variation). Their Corollary 1.5
deduces that two paths of bounded variation have the same signature iff the concatenation of one
with the other run backwards is a Lipschitz tree-like path. -/
theorem_wanted isTreeLike_iff_signature_eq_tensorOne {d : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (v : Fin d → ℝ → ℝ) (hv : ∀ i, IntervalIntegrable (v i) volume 0 T) :
    IsTreeLike (fun t => WithLp.toLp 2 (fun i => ∫ u in (0 : ℝ)..t, v i u) :
        ℝ → EuclideanSpace ℝ (Fin d)) T ↔
      signature v 0 T = tensorOne

end MathlibExt.Analysis.PathSignature.TreeLikeWanted
