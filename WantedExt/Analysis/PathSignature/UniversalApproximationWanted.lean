/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.PathSignature.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Universal approximation by linear functionals of the signature (wanted)

The shuffle product identity makes the linear functionals `X ↦ ∑ λ_k S(X)^{I_k}_{a,b}` of the
signature an algebra containing the constants; with a time coordinate it separates paths, so by the
Stone–Weierstrass theorem it is uniformly dense among continuous functions on compact sets of paths
(Chevyrev and Kormilitzin, *A primer on the signature method in machine learning*,
arXiv:1603.03788v2, Propositions 1.34 and 1.35; T. Lyons, Proc. ICM 2014, arXiv:1405.4537,
Lemma 9.4). This is the basis of the signature method in machine learning.
-/

open MeasureTheory

@[expose] public section

namespace MathlibExt.Analysis.PathSignature.UniversalApproximationWanted

open MathlibExt.Analysis.PathSignature

/-- **Universal approximation by linear functionals of the signature.** Fix `a < b`. Describe an
absolutely continuous path `X : [a, b] → ℝ^{d+1}` with a fixed starting point by its velocity
`f ∈ L¹([a, b]; ℝ^{d+1})`, so that `‖f − f'‖_{L¹}` is the bounded-variation distance of the two
paths, and suppose the coordinate `0` is time (`f₀ = 1` almost everywhere, so `X⁰_t = t` up to
the fixed start). Let `K` be a compact set of such velocities and `g` a real function continuous
on `K`. Then for every `ε > 0` there are finitely many reals `λ_k` and words `I_k` with
`|g(X) − ∑_k λ_k S(X)^{I_k}_{a,b}| < ε` for every `X ∈ K` (Chevyrev and Kormilitzin, *A primer
on the signature method in machine learning*, arXiv:1603.03788v2, Proposition 1.35, stated there
for paths with the bounded-variation norm `|X_a| + ∫_a^b |Ẋ_t| dt`). -/
theorem_wanted exists_signature_linear_approx {d : ℕ} {a b : ℝ} (hab : a < b)
    (K : Set (Lp (Fin (d + 1) → ℝ) 1 (volume.restrict (Set.Icc a b)))) (hK : IsCompact K)
    (htime : ∀ f ∈ K, ∀ᵐ u ∂(volume.restrict (Set.Icc a b)), f u 0 = 1)
    (g : Lp (Fin (d + 1) → ℝ) 1 (volume.restrict (Set.Icc a b)) → ℝ) (hg : ContinuousOn g K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : List (ℝ × List (Fin (d + 1))), ∀ f ∈ K,
      |g f - (L.map fun p => p.1 * signature (fun i u => f u i) a b p.2).sum| < ε

end MathlibExt.Analysis.PathSignature.UniversalApproximationWanted
