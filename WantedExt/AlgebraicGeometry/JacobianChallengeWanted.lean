/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Jacobian of a smooth proper curve (Merten challenge)

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, modules `LeanEval.AlgebraicGeometry.JacobianChallenge` — jacobian_challenge_alggeo (manifest `manifests/problems/jacobian_challenge_alggeo.toml`, rev 1, submitter Christian Merten, status active) — and `LeanEval.AlgebraicGeometry.UniformMordellLang` — annals_uniform_mordell_lang (manifest `manifests/problems/annals_uniform_mordell_lang.toml`, rev 1, submitters Thomas Browning and Christian Merten, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.AlgebraicGeometry.JacobianChallengeWanted` namespace. The Uniform Mordell–Lang declarations are consolidated into this file, reusing its Jacobian-interface declarations instead of duplicating upstream's namespaced copy, and the added `c_pos` record states the source-required positivity of the uniform constant. Mathematical
statements are otherwise unchanged. Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge/near/587802685
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.JacobianChallengeWanted
/-!
# Jacobians in algebraic geometry

Christian Merten's algebraic-geometry analogue of Kevin Buzzard's Jacobian
challenge, posted to leanprover Zulip:
<https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge/near/587802685>.

In the following, by a smooth curve we mean a geometrically irreducible, smooth scheme of relative
dimension one over a field.

## Main missing definitions

* `AlgebraicGeometry.JacobianChallenge.genus` -- genus of a proper, smooth curve
* `AlgebraicGeometry.JacobianChallenge.Jacobian` -- the Jacobian of a proper, smooth curve
* `AlgebraicGeometry.JacobianChallenge.Jacobian.ofCurve` -- the Abel-Jacobi map from a proper smooth
  curve to its Jacobian

## Main missing theorems

* `Jacobian.smoothOfRelativeDimension_genus` -- The Jacobian of a proper, smooth curve `C` is smooth
  of relative dimension `g`, where `g` is the genus of `C`.
* `Jacobian.exists_unique_ofCurve_comp` -- the universal property of the Jacobian of a proper,
  smooth curve.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

namespace JacobianChallenge

open _root_.AlgebraicGeometry

-- We make `C` implicit at the variable level so that instance and `def` holes
-- whose statement references the outer `C` (e.g. `instance instGrpObj :
-- GrpObj (Jacobian C) := sorry`) elaborate to a Π-type with `{C}` implicit;
-- otherwise the eval-pipeline's `Solution.lean` would have to thread a `C`
-- argument through every delegation. Decls that genuinely need `C` explicit
-- (e.g. `genus`, `Jacobian`, `comp_ofCurve`) supply their own `(C : ...)`
-- binder.
variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  -- smooth curve
  [SmoothOfRelativeDimension 1 C.hom]
  -- proper
  [IsProper C.hom]
  -- geometrically irreducible
  [GeometricallyIrreducible C.hom]

-- data
/- The genus of a smooth proper curve. -/
/-- **Genus of a smooth proper curve.** For a field $k$ and a curve $C$ over $k$, that is, a
$k$-scheme that is proper, smooth of relative dimension $1$ and geometrically irreducible, the
genus of $C$ is a natural number.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge/near/587802685 Via leanprover/lean-eval@38361be, problem `jacobian_challenge_alggeo`. -/
public def_wanted genus (C : Over (Spec (.of k))) [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIrreducible C.hom] : ℕ

-- data
/- The Jacobian of a smooth, proper curve over a field `k`. -/
/-- **Jacobian of a smooth proper curve.** For a field $k$ and a curve $C$ over $k$, that is, a
$k$-scheme that is proper, smooth of relative dimension $1$ and geometrically irreducible, the
Jacobian $J(C)$ of $C$ is a $k$-scheme.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge/near/587802685 Via leanprover/lean-eval@38361be, problem `jacobian_challenge_alggeo`. -/
public def_wanted Jacobian (C : Over (Spec (.of k))) [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIrreducible C.hom] : Over (Spec (.of k))

namespace Jacobian

/-! ## The Jacobian of `C` is an abelian variety. -/

-- data
/- The group scheme structure on the Jacobian of the curve `C`. -/
/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge/near/587802685 Via leanprover/lean-eval@38361be, problem `jacobian_challenge_alggeo`. -/
public instance_wanted instGrpObj : GrpObj (❰Jacobian❱ C)

/- The Jacobian of `C` is smooth of relative dimension `g` over `k`, where `g` is the
genus of `C`. -/
/-- **The Jacobian has dimension equal to the genus.** Let $C$ be a proper, smooth, geometrically
irreducible curve over a field $k$. The Jacobian $J(C)$ is smooth of relative dimension $g$ over
$k$, where $g$ is the genus of $C$.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge/near/587802685 Via leanprover/lean-eval@38361be, problem `jacobian_challenge_alggeo`. -/
public theorem_wanted smoothOfRelativeDimension_genus :
    SmoothOfRelativeDimension (❰genus❱ C) (❰Jacobian❱ C).hom

/- The Jacobian of `C` is proper over `k`. -/
/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge/near/587802685 Via leanprover/lean-eval@38361be, problem `jacobian_challenge_alggeo`. -/
public instance_wanted instIsProper : IsProper (❰Jacobian❱ C).hom

/- The Jacobian of `C` is geometrically irreducible over `k`. -/
/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge/near/587802685 Via leanprover/lean-eval@38361be, problem `jacobian_challenge_alggeo`. -/
public instance_wanted instGeometricallyIrreducible : GeometricallyIrreducible (❰Jacobian❱ C).hom

-- data
/- The Abel-Jacobi map from a smooth, proper curve to its Jacobian associated
to a `k`-rational point of `C`. -/
/-- **Abel–Jacobi map.** Let $C$ be a proper, smooth, geometrically irreducible curve over a field
$k$. Each $k$-rational point $P$ of $C$ gives a morphism of $k$-schemes $C \to J(C)$ from $C$ to
its Jacobian, the Abel–Jacobi map based at $P$.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge/near/587802685 Via leanprover/lean-eval@38361be, problem `jacobian_challenge_alggeo`. -/
public def_wanted ofCurve (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) : C ⟶ ❰Jacobian❱ C

/- The Abel-Jacobi map sends the `k`-rational point `P` to `0`, where `0` (denoted by `η` below) is
the neutral element of the group scheme `Jacobian C`. -/
/-- **The Abel–Jacobi map sends the base point to zero.** Let $C$ be a proper, smooth,
geometrically irreducible curve over a field $k$, let $J(C)$ be its Jacobian, and let $P$ be a
$k$-rational point of $C$. The Abel–Jacobi map $C \to J(C)$ based at $P$ sends $P$ to the
identity point of $J(C)$ for its group scheme structure.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge/near/587802685 Via leanprover/lean-eval@38361be, problem `jacobian_challenge_alggeo`. -/
public theorem_wanted comp_ofCurve (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    P ≫ ❰ofCurve❱ P = η[❰Jacobian❱ C]

/-- **Universal property of the Jacobian.** Let $C$ be a proper, smooth, geometrically irreducible
curve over a field $k$, let $J(C)$ be its Jacobian, let $P$ be a $k$-rational point of $C$, and
let $\iota_P : C \to J(C)$ be the Abel–Jacobi map based at $P$. Let $A$ be a group scheme over $k$
that is smooth, proper and geometrically irreducible. For every morphism of $k$-schemes
$f : C \to A$ sending $P$ to the identity point of $A$, there is a unique morphism of $k$-schemes
$g : J(C) \to A$ with $f = g \circ \iota_P$.

In other words, the Jacobian of $C$ is the Albanese variety of $C$.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge/near/587802685 Via leanprover/lean-eval@38361be, problem `jacobian_challenge_alggeo`.
-/
public theorem_wanted exists_unique_ofCurve_comp (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C)
    {A : Over (Spec (.of k))} [Smooth A.hom] [IsProper A.hom] [GrpObj A]
    [GeometricallyIrreducible A.hom] (f : C ⟶ A) (hf : P ≫ f = η[A]) :
    ∃! (g : ❰Jacobian❱ C ⟶ A), f = ❰ofCurve❱ P ≫ g

end Jacobian

/-! ## Uniform Mordell–Lang (co-located with the Jacobian interface it uses) -/

set_option linter.defProp false in
/- The Jacobian of `C` is geometrically integral over `k`. -/
/-- Source: V. Dimitrov, Z. Gao, and P. Habegger, `Uniformity in Mordell–Lang for curves`, Annals of Math, 194 (1) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-1-UniformMordellLang.lean Via leanprover/lean-eval@38361be, problem `annals_uniform_mordell_lang`. -/
public instance_wanted instGeometricallyIntegral : GeometricallyIntegral (❰Jacobian❱ C).hom

/-- The Jacobian of `C` is an abelian variety, with the commutative monoid
structure derived from its group-object structure and geometric integrality
(the preceding wanted dependencies), as upstream. -/
public instance_wanted instIsCommMonObj {k : Type u} [Field k] {C : Over (Spec (.of k))}
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] : IsCommMonObj (❰Jacobian❱ C)

set_option warn.classDefReducibility false in
/-- The `k`-points of the Jacobian of `C` form an abelian group. -/
noncomputable instance_wanted instCommGroup {k : Type u} [Field k]
    {C : Over (Spec (.of k))} [SmoothOfRelativeDimension 1 C.hom]
    [IsProper C.hom] [GeometricallyIrreducible C.hom] :
    CommGroup (𝟙_ (Over (Spec (.of k))) ⟶ ❰Jacobian❱ C)

/-- **Group law on the rational points of the Jacobian.** Let $C$ be a proper, smooth,
geometrically irreducible curve over a field $k$. The commutative group structure on the set of
$k$-rational points of the Jacobian $J(C)$ is the one induced by its commutative group scheme
structure: the product of two $k$-points $x$ and $y$ is $\mu \circ (x, y)$, where $\mu$ is the
multiplication morphism of $J(C)$.

This pins down the group law rather than allowing an arbitrary commutative group structure.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge/near/587802685 Via leanprover/lean-eval@38361be, problem `jacobian_challenge_alggeo`. -/
public theorem_wanted instCommGroup_eq {k : Type u} [Field k]
    {C : Over (Spec (.of k))} [SmoothOfRelativeDimension 1 C.hom]
    [IsProper C.hom] [GeometricallyIrreducible C.hom] :
    (❰instCommGroup❱ : CommGroup (𝟙_ (Over (Spec (.of k))) ⟶ ❰Jacobian❱ C)) =
      @CategoryTheory.Hom.commGroup
        (Over (Spec (.of k)))
        (CategoryTheory.instCategoryOver)
        (AlgebraicGeometry.instCartesianMonoidalCategoryOverScheme)
        (❰Jacobian❱ C)
        (𝟙_ (Over (Spec (.of k))))
        (❰Jacobian.instGrpObj❱)
        (AlgebraicGeometry.instBraidedCategoryOverScheme)
        (❰instIsCommMonObj❱)

set_option linter.defProp false in
/- If `k` is a number field, then the `k`-points of the Jacobian of `C` are finitely generated.

This is the Mordell-Weil theorem; it is what gives Theorem 1.1's `ρ` a meaning. Anonymous
upstream, named here so that it can be addressed as a hole. -/
/-- Source: V. Dimitrov, Z. Gao, and P. Habegger, `Uniformity in Mordell–Lang for curves`, Annals of Math, 194 (1) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-1-UniformMordellLang.lean Via leanprover/lean-eval@38361be, problem `annals_uniform_mordell_lang`. -/
public instance_wanted instFG [NumberField k] :
    @IsMulFG (𝟙_ (Over (Spec (.of k))) ⟶ ❰Jacobian❱ C)
      (❰instCommGroup❱).toMul

end JacobianChallenge

end AlgebraicGeometry

/-! ### Theorem 1.1 -/

open CommGroup Module CategoryTheory MonoidalCategory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.JacobianChallengeWanted.AlgebraicGeometry.JacobianChallenge

/- The function `c` of Theorem 1.1 of the paper. -/
/-- **Uniform Mordell–Lang constant.** For natural numbers $g$ and $d$, $c(g, d)$ is a natural
number: the constant in the uniform bound on rational points of curves in Theorem 1.1 of
Dimitrov, Gao and Habegger.

Source: V. Dimitrov, Z. Gao, and P. Habegger, `Uniformity in Mordell–Lang for curves`, Annals of Math, 194 (1) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-1-UniformMordellLang.lean Via leanprover/lean-eval@38361be, problem `annals_uniform_mordell_lang`. -/
public def_wanted c (g : ℕ) (d : ℕ) : ℕ

/-
Statement of Theorem 1.1:

Let `g ≥ 2` and `d ≥ 1` be integers. Then there exists a constant `c = c(g, d) ≥ 1` with the
following property. If `C` is a smooth curve of genus `g` defined over a number field `F` with
`[F : Q] ≤ d`, then `#C(F) ≤ c^(1+ρ)`, where `ρ` is the rank of `Jac(C)(F)`.

We do not give a complete definition of the Jacobian of `C`. Instead, a characterization can be
The uniform Mordell–Lang declarations below are co-located in this file with the Jacobian wishlist declarations they use, since wanted references are file-local.

Note however that the characterization of the Jacobian of `C` is only correct when the `C` has an
`F`-point, but Theorem 1.1 is trivial when `C` has no `F`-points, so this is not a problem.
-/
/-- **The uniform Mordell–Lang constant is at least one.** For all natural numbers $g$ and
$d$, the uniform constant satisfies $c(g, d) \ge 1$. -/
public theorem_wanted c_pos (g d : ℕ) : 1 ≤ ❰c❱ g d

/-- **Uniform Mordell–Lang for curves.** Let $g \ge 2$ and $d \ge 1$ be natural numbers, let $F$
be a number field with $[F : \mathbb{Q}] \le d$, and let $C$ be a proper, smooth, geometrically
irreducible curve over $F$. If $C$ has genus $g$, then the number of $F$-rational points of $C$,
possibly infinite, is at most $c(g, d)^{1 + \rho}$, where $c$ is the uniform constant and $\rho$
is the free rank of the group of $F$-rational points of the Jacobian of $C$.

Source: V. Dimitrov, Z. Gao, and P. Habegger, `Uniformity in Mordell–Lang for curves`, Annals of Math, 194 (1) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-1-UniformMordellLang.lean Via leanprover/lean-eval@38361be, problem `annals_uniform_mordell_lang`. -/
public theorem_wanted theorem_1_1 (g d : ℕ) (hg : g ≥ 2) (hd : d ≥ 1) {F : Type*} [Field F] [NumberField F]
    (hF : finrank ℚ F ≤ d) (C : Over (Spec (.of F))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    ❰genus❱ C = g → ENat.card (𝟙_ (Over (Spec (.of F))) ⟶ C) ≤
      ❰c❱ g d ^ (1 + freeRank (𝟙_ (Over (Spec (.of F))) ⟶ ❰Jacobian❱ C))

end MathlibExt.AlgebraicGeometry.JacobianChallengeWanted
