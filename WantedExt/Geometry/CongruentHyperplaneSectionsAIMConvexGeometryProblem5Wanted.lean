/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Congruent hyperplane sections do not determine a body up to ±1 (AIM sections of bodies, Problem 4)

AIM workshop Sections of convex bodies, problem list, Problem 4: suppose `K` and `L` are star bodies
and that `K ∩ S` is congruent to `L ∩ S` for every `S ∈ G(n, k)`, where `2 ≤ k ≤ n - 1` is fixed.
Does it follow that `K = ±L`? (The answer is affirmative for `k = 2` when 'congruent to' is replaced
by 'a rotation of'.)
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Geometry.Convex.Covering

@[expose] public section

namespace MathlibExt.Geometry.CongruentHyperplaneSectionsAIMConvexGeometryProblem5Wanted

/-!
Source: AIM workshop Sections of convex bodies, problem list,
https://aimath.org/pastworkshops/sectionsconvexproblems.pdf, Problem 4. UnsolvedMath record
UM-20001273 (`AIM-CONVEX_GEOMETRY-0005`), dataset ulamai/UnsolvedMath v1.8.0.

The formalized case is `k = n - 1` (central hyperplane sections), for every `n ≥ 3`; smaller `k` are
not claimed. Bodies are convex bodies (MathlibExt's `ConvexCovering.IsConvexBody`: compact, convex,
nonempty interior) with the origin in their interior, a subclass of star bodies, and congruence is
the strongest form: an orthogonal map `φ` of the hyperplane with `φ (K ∩ H) = L ∩ H`, no
translation. A counterexample in this subclass with this relation is a counterexample to the list's
question for `k = n - 1`. The target says the answer is yes for some `n ≥ 3`; Zhang's theorem
refutes it for every `n ≥ 3`.
-/

open scoped Pointwise

/-- Euclidean space `ℝⁿ`. -/
abbrev En (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- Every central hyperplane section of `K` is the image of the corresponding section of `L` under
an orthogonal transformation of the hyperplane: for every linear hyperplane `H` there is a linear
isometry `φ` of `H` with `φ (K ∩ H) = L ∩ H`. -/
def CongruentCentralHyperplaneSections {n : ℕ} (K L : Set (En n)) : Prop :=
  ∀ H : Submodule ℝ (En n), Module.finrank ℝ H + 1 = n →
    ∃ φ : H ≃ₗᵢ[ℝ] H, φ '' {x : H | (x : En n) ∈ K} = {x : H | (x : En n) ∈ L}

/-- For some `n ≥ 3`, congruence of all central hyperplane sections determines a convex body
(`ConvexCovering.IsConvexBody` of MathlibExt: compact, convex, nonempty interior) with the origin in
its interior, in particular a star body, up to reflection in the origin (the `k = n - 1` case of the
AIM question, Sections of convex bodies, Problem 4). -/
def hyperplaneSectionsDetermineUpToReflection : Prop :=
  ∃ n : ℕ, 3 ≤ n ∧ ∀ K L : Set (En n),
    ConvexCovering.IsConvexBody K → (0 : En n) ∈ interior K →
    ConvexCovering.IsConvexBody L → (0 : En n) ∈ interior L →
    CongruentCentralHyperplaneSections K L → K = L ∨ K = -L

/--
Resolved false for hyperplane sections in every dimension `n ≥ 3`: Zhang (Theorem 1.3) constructed
convex bodies `K ≠ ±L` in `ℝⁿ`, given by radial functions (so with the origin in their interiors),
such that for every unit vector `ξ` an orthogonal map of `ξ^⊥` carries `K ∩ ξ^⊥` onto `L ∩ ξ^⊥`.
Source: AIM workshop Sections of convex bodies, problem list,
https://aimath.org/pastworkshops/sectionsconvexproblems.pdf, Problem 4; resolution: N. Zhang, On
bodies with congruent sections or projections, J. Differential Equations 265 (2018), 2064-2075,
arXiv:1711.10445, Theorem 1.3: for every n ≥ 3 there are convex bodies K, L ⊂ ℝⁿ with K ≠ L and K ≠
-L such that for every ξ ∈ Sⁿ⁻¹ some orthogonal transformation φ_ξ ∈ O(n - 1) of ξ^⊥ satisfies φ_ξ(K
∩ ξ^⊥) = L ∩ ξ^⊥ (the bodies are given by radial functions, so the origin is interior); this answers
Problem 1.1 of the paper, the same question (Gardner, Geometric tomography, Problem 7.3),
negatively, https://doi.org/10.1016/j.jde.2018.04.025.
-/
public theorem_wanted hyperplaneSectionsDetermineUpToReflection_refuted :
    ¬ hyperplaneSectionsDetermineUpToReflection

end MathlibExt.Geometry.CongruentHyperplaneSectionsAIMConvexGeometryProblem5Wanted
