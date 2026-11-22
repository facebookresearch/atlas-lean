/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Extension complexity of convex polygons is sublinear (Open Problem Garden 37341)

Open Problem Garden, Extension complexity of (convex) polygons: the extension complexity of a
polytope `P` is the minimum number `q` for which there is a polytope `Q` with `q` facets and an
affine map `π` with `π(Q) = P`. Does there exist, for infinitely many integers `n`, a convex polygon
on `n` vertices whose extension complexity is `Ω(n)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Independent
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.Bornology.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Geometry.PolygonExtensionComplexityOpenGardenProblem37341Wanted

/-!
Source: Open Problem Garden, Extension complexity of (convex) polygons (node 37341; posted by DOT),
http://www.openproblemgarden.org/op/extension_complexity_of_convex_polygons. UnsolvedMath record
UM-00003100 (`OPG-37341`), dataset ulamai/UnsolvedMath v1.8.0.

Extension complexity is taken in the form Shitov states (Introduction, citing Yannakakis): the least
number of inequalities in a representation `{y | a i ⬝ᵥ y ≤ b i}` of a polytope (bounded) that is
sent onto `P` by a linear projection; this equals the least number of facets of such a polytope, and
allowing affine maps changes nothing (translate `Q`). A convex polygon on `n` vertices is the convex
hull of `n` points in convex position (`ConvexIndependent`). `Ω(n)` for infinitely many `n` means:
some `ε > 0` and infinitely many `n` with an `n`-gon of extension complexity at least `ε n`.
-/

/-- `P ⊆ ℝ²` has an extended formulation of size `r`: it is the image under a linear map
`π : ℝ^m → ℝ²` of a polytope `Q = {y ∈ ℝ^m | a i ⬝ᵥ y ≤ b i for all i}` given by `r` linear
inequalities (`Q` bounded). -/
def HasExtendedFormulation (P : Set (Fin 2 → ℝ)) (r : ℕ) : Prop :=
  ∃ (m : ℕ) (a : Fin r → Fin m → ℝ) (b : Fin r → ℝ) (π : (Fin m → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)),
    Bornology.IsBounded {y : Fin m → ℝ | ∀ i, a i ⬝ᵥ y ≤ b i} ∧
      π '' {y : Fin m → ℝ | ∀ i, a i ⬝ᵥ y ≤ b i} = P

/-- The extension complexity `xc(P)`: the least number of inequalities describing a polytope that
projects linearly onto `P`, equivalently the least number of facets of such a polytope. -/
noncomputable def extensionComplexity (P : Set (Fin 2 → ℝ)) : ℕ :=
  sInf {r | HasExtendedFormulation P r}

/-- The source's question: for some `ε > 0` there are infinitely many `n` for which some convex
polygon with `n` vertices (`n` points in convex position) has extension complexity at least `ε n`,
i.e. `Ω(n)`. -/
def linearExtensionComplexityPolygons : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ n, N ≤ n ∧ ∃ v : Fin n → (Fin 2 → ℝ), ConvexIndependent ℝ v ∧
    ε * n ≤ extensionComplexity (convexHull ℝ (Set.range v))

/--
Resolved false: Shitov proved that every convex polygon with `n > 3` vertices is a linear projection
of a polytope with at most `147 n^{2/3}` facets, so for every `ε > 0` all large `n`-gons have
extension complexity below `ε n`; Shitov identifies the Open Problem Garden question with his
Question 4. Source: Open Problem Garden, Extension complexity of (convex) polygons (node 37341;
posted by DOT), http://www.openproblemgarden.org/op/extension_complexity_of_convex_polygons;
resolution: Y. Shitov, Sublinear extensions of polygons, Proc. Lond. Math. Soc. (3) 132(4) (2026),
e70137, doi:10.1112/plms.70137; arXiv:1412.0728, Theorem 5: pc(n) ≤ 147 n^{2/3} for all n > 3, where
pc(n) is the smallest number such that every convex polygon with n vertices is a linear projection
of a polytope with at most pc(n) facets (Question 1); Section 2 identifies the Open Problem Garden
question with Question 4 ('Do we have pc(n) > εn for some fixed ε > 0?') and states that Theorem 5
goes against the expected affirmative answer, https://doi.org/10.1112/plms.70137.
-/
public theorem_wanted linearExtensionComplexityPolygons_refuted :
    ¬ linearExtensionComplexityPolygons

end MathlibExt.Geometry.PolygonExtensionComplexityOpenGardenProblem37341Wanted
