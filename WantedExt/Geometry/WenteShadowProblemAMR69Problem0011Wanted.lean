/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Connected shadows do not force convexity (Wente's shadow problem in 3-space)

M. Ghomi, Open Problems in Geometry of Curves and Surfaces (2019), Problem 2.2 (Wente, 1978): let `f
: M → ℝ^{n+1}` be a closed oriented hypersurface with Gauss map `G_f`, and for `u ∈ Sⁿ` let `S_u =
{p ∈ M | ⟨G_f(p), u⟩ > 0}` be the shadow. Does connectedness of the shadows imply that `f(M)` is
convex?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.Geometry.Manifold.Sheaf.Basic

@[expose] public section

namespace MathlibExt.Geometry.WenteShadowProblemAMR69Problem0011Wanted

/-!
Source: M. Ghomi, Open Problems in Geometry of Curves and Surfaces (2019), Problem 2.2 (Wente's
shadow problem). UnsolvedMath record UM-07000011 (`AMR-069-0011`), dataset ulamai/UnsolvedMath
v1.8.0.

Formalized in `3`-space (`n = 2`), the case Wente posed and the only one settled: `M` is a closed
(compact, connected, Hausdorff) smooth surface modelled on `ℝ²`, `f` a `C^∞` immersion, and the
orientation is a continuous unit normal field `n` (the Gauss map). "`f(M)` is convex" is read, as in
Ghomi's paper, as `f` being a convex embedding: injective onto the boundary of a convex body
(compact convex with nonempty interior). Ghomi's list: "nothing known in higher dimensions".
-/

open scoped ContDiff Manifold

/-- `f` is a convex embedding: it is injective and maps `M` onto the boundary of a convex body
(a compact convex set with nonempty interior). -/
def IsConvexEmbedding {M : Type*} (f : M → EuclideanSpace ℝ (Fin 3)) : Prop :=
  Function.Injective f ∧ ∃ K : Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ K ∧ IsCompact K ∧
    (interior K).Nonempty ∧ Set.range f = frontier K

/-- Wente's shadow problem (Ghomi, Open Problems in Geometry of Curves and Surfaces, Problem 2.2),
in `3`-space: let `M` be a closed (compact, connected, Hausdorff) smooth surface, `f : M → ℝ³` a
smooth immersion and `n : M → S²` a continuous unit normal field (Gauss map; its existence is the
orientation of `M`). If every shadow `S_u = {p | ⟨n p, u⟩ > 0}`, `u ∈ S²`, is connected, then `f`
is a convex embedding. -/
def connectedShadowsImplyConvex : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ∞ M] [CompactSpace M] [ConnectedSpace M]
    (f n : M → EuclideanSpace ℝ (Fin 3)), ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ f →
    (∀ p, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) f p)) →
    Continuous n → (∀ p, ‖n p‖ = 1) →
    (∀ p v, inner ℝ (n p) (mfderiv (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) f p v) = 0) →
    (∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → IsConnected {p | 0 < inner ℝ (n p) u}) →
    IsConvexEmbedding f

/--
Resolved false: Ghomi constructed a smooth embedded torus in `ℝ³` all of whose shadows are
connected; a torus is not the boundary of a convex body, so connected shadows do not imply convexity
(they do for spheres and when shadows are simply connected). Source: M. Ghomi, Open Problems in
Geometry of Curves and Surfaces (2019), Problem 2.2 (Wente's shadow problem); resolution: M. Ghomi,
Shadows and convexity of surfaces, Ann. of Math. (2) 155 (2002), 281-293, arXiv:math/0409366;
recorded in Ghomi's list after Problem 2.2, Theorem 2 of the introduction: there is a smooth
embedding f : S¹ × S¹ → ℝ³ such that S_u is connected for all u ∈ S²; Theorems 1 and 3: f is a
convex embedding iff every S_u is simply connected, or if M is a sphere with connected shadows;
Ghomi's list: "the answer to Problem 2.2 is yes provided that each shadow is simply connected, or
that M is topologically a sphere; otherwise, the answer is no", https://arxiv.org/abs/math/0409366.
-/
public theorem_wanted connectedShadowsImplyConvex_refuted : ¬ connectedShadowsImplyConvex

end MathlibExt.Geometry.WenteShadowProblemAMR69Problem0011Wanted
