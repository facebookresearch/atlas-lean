/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rational approximations to linear subspaces

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.LinearSubspaces` — annals_linear_subspaces (manifest `manifests/problems/annals_linear_subspaces.toml`, rev 1, submitter Justus Springer, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.LinearSubspacesWanted` namespace. Mathematical
statements are unchanged. Source: N. de Saxcé, `Rational approximations to linear subspaces`, Annals of Math, 203 (3) 2026. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2026-203-3-LinearSubspaces.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.InnerProductSpace.ExteriorPower
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.LinearAlgebra.Projectivization.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.LinearSubspacesWanted
/-!
# Main Statement from Rational approximations to linear subspaces

We formalise the statement of the main result from N. de Saxcé,
`Rational approximations to linear subspaces`, Annals of Math, 203 (3) 2026.
-/

set_option autoImplicit false

noncomputable section

namespace LinearSubspaces

open ENNReal Real Module exteriorPower InnerProductGeometry

open scoped LinearAlgebra.Projectivization

variable {d : ℕ}

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- **Distance between lines.** For lines $x$ and $y$ through the origin in $\mathbb{R}^d$, the
distance $\operatorname{dist}(x, y)$ is $\sin \theta$, where $\theta \in [0, \pi]$ is the angle
between nonzero vectors spanning $x$ and $y$. This is the usual distance on the projective
space. -/
def distLines (x y : ℙ ℝ ℝᵈ) : ℝ := sin (angle x.rep y.rep)

/-- **Distance from a line to a subspace.** For a line $x$ through the origin in $\mathbb{R}^d$
and a subspace $y$ of $\mathbb{R}^d$, the distance $\operatorname{dist}(x, y)$ is the infimum,
over all lines $y'$ contained in $y$, of the distance $\operatorname{dist}(x, y')$ between the
lines $x$ and $y'$. When $y = 0$ there is no such line and the value is $0$. -/
def distLineSubspace (x : ℙ ℝ ℝᵈ) (y : Submodule ℝ ℝᵈ) : ℝ :=
  ⨅ y' : {y' : ℙ ℝ ℝᵈ // y'.submodule ≤ y}, distLines x y'.1

/-- **Distance between subspaces.** For subspaces $x$ and $y$ of $\mathbb{R}^d$, the distance
$\operatorname{dist}(x, y)$ is defined as follows. If $\dim y \le \dim x$, it is the supremum,
over all lines $y'$ contained in $y$, of the distance $\operatorname{dist}(y', x)$ from the line
$y'$ to the subspace $x$. If $\dim y > \dim x$, it is the supremum, over all lines $x'$ contained
in $x$, of the distance $\operatorname{dist}(x', y)$ from the line $x'$ to the subspace $y$. A
supremum over no lines is $0$. -/
def distSubspaces (x y : Submodule ℝ ℝᵈ) : ℝ :=
  if finrank ℝ y ≤ finrank ℝ x then
    ⨆ y' : {y' : ℙ ℝ ℝᵈ // y'.submodule ≤ y}, distLineSubspace y'.1 x
  else
    ⨆ x' : {x' : ℙ ℝ ℝᵈ // x'.submodule ≤ x}, distLineSubspace x'.1 y

/-- **The integer lattice.** $\mathbb{Z}^d$ is the $\mathbb{Z}$-submodule of $\mathbb{R}^d$
spanned by the standard basis vectors, that is, the lattice of points with integer coordinates. -/
abbrev intPoints : Submodule ℤ ℝᵈ :=
  .span ℤ (Set.range (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)

local notation "ℤᵈ" => intPoints

/-- **Integer points of a subspace.** For a subspace $V$ of $\mathbb{R}^d$, this is the set
$V \cap \mathbb{Z}^d$ of integer points of $V$, as a $\mathbb{Z}$-submodule of $V$. -/
def intPointsSubspace (V : Submodule ℝ ℝᵈ) : Submodule ℤ V :=
  ZLattice.comap ℝ ℤᵈ V.subtype

instance (V : Submodule ℝ ℝᵈ) : DiscreteTopology (intPointsSubspace V) :=
  ZLattice.comap_discreteTopology ℝ _ (by fun_prop) V.injective_subtype

/-- **Rational subspace.** A subspace $V$ of $\mathbb{R}^d$ is rational if $V \cap \mathbb{Z}^d$
is a full-rank lattice in $V$, that is, a discrete subgroup of $V$ that spans $V$ over
$\mathbb{R}$.

The paper does not state which definition of rational subspace it uses; this one is common
and is the most convenient for defining heights of rational subspaces. -/
abbrev IsRational (V : Submodule ℝ ℝᵈ) : Prop :=
  IsZLattice ℝ (intPointsSubspace V)

/-- **Chosen basis of a rational subspace.** For a rational subspace $V$ of $\mathbb{R}^d$, this
is a fixed choice of a $\mathbb{Z}$-basis of the lattice $V \cap \mathbb{Z}^d$, indexed by
$\{0, \dots, \dim V - 1\}$ and viewed as an $\mathbb{R}$-basis of $V$. -/
def chosenBasis (V : Submodule ℝ ℝᵈ) (hV : IsRational V) : Basis (Fin (finrank ℝ V)) ℝ V :=
  .ofZLatticeBasis ℝ _ <| .reindex (Free.chooseBasis ℤ (intPointsSubspace V)) <|
    Fintype.equivFinOfCardEq <| by rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ]

/-- **Height of a rational subspace.** For a rational subspace $V$ of $\mathbb{R}^d$ of dimension
$k$, let $v_1, \dots, v_k$ be the chosen basis of the lattice $V \cap \mathbb{Z}^d$. The height of
$V$ is $H(V) = \lVert v_1 \wedge \dots \wedge v_k \rVert$, where the exterior power
$\bigwedge^k \mathbb{R}^d$ carries the inner product whose value on decomposable elements
$u_1 \wedge \dots \wedge u_k$ and $w_1 \wedge \dots \wedge w_k$ is the Gram determinant
$\det(\langle u_i, w_j \rangle)_{i,j}$. -/
def height (V : Submodule ℝ ℝᵈ) (hV : IsRational V) : ℝ :=
  ‖ιMulti ℝ _ (V.subtype ∘ chosenBasis V hV)‖

/-- **Diophantine exponent.** Let $x$ be a subspace of $\mathbb{R}^d$ and let $k$ be a natural
number. For subspaces $v$ of $\mathbb{R}^d$ write $\operatorname{dist}(v, x)$ for the distance
between the subspaces $v$ and $x$, and for a rational subspace $v$ write $H(v)$ for its height.
The diophantine exponent $\beta_k(x)$ of $x$ for approximation by $k$-dimensional rational
subspaces is the infimum, taken in $[0, \infty]$, of the set of real numbers $\beta > 0$ for
which there is a real number $c > 0$ such that $\operatorname{dist}(v, x) \ge c \, H(v)^{-\beta}$
for every $k$-dimensional rational subspace $v$ of $\mathbb{R}^d$. In particular
$\beta_k(x) = \infty$ when there is no such $\beta$. -/
def diophantineExponent (k : ℕ) (x : Submodule ℝ ℝᵈ) : ℝ≥0∞ :=
  sInf (.ofReal '' {β : ℝ | β > 0 ∧ ∃ c > 0, ∀ v : Submodule ℝ ℝᵈ, finrank ℝ v = k →
    (hv : IsRational v) → distSubspaces v x ≥ c * height v hv ^ (-β)})

/--
**Dirichlet's principle in Grassmann varieties.** Let $d$, $l$ and $k$ be natural numbers with
$d \ge 2$, $0 < l < d$ and $1 \le k \le l$, and for a subspace $x$ of $\mathbb{R}^d$ write
$\beta_k(x)$ for the diophantine exponent of $x$ for approximation by $k$-dimensional rational
subspaces. Then every $l$-dimensional subspace $x$ of $\mathbb{R}^d$ satisfies
$\beta_k(x) \ge \frac{d}{k(d - l)}$. Moreover, some $l$-dimensional subspace $x$ of
$\mathbb{R}^d$ satisfies $\beta_k(x) = \frac{d}{k(d - l)}$.

Source: N. de Saxcé, `Rational approximations to linear subspaces`, Annals of Math, 203 (3) 2026. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2026-203-3-LinearSubspaces.lean Via leanprover/lean-eval@38361be, problem `annals_linear_subspaces`.
-/
public theorem_wanted theorem_1
    (hd : 2 ≤ d) (l : ℕ) (hl0 : 0 < l) (hld : l < d) (k : ℕ) (hk1 : 1 ≤ k) (hkl : k ≤ l) :
    (∀ x : Submodule ℝ ℝᵈ, finrank ℝ x = l → diophantineExponent k x ≥ d / (k * (d - l))) ∧
    (∃ x : Submodule ℝ ℝᵈ, finrank ℝ x = l ∧ diophantineExponent k x = d / (k * (d - l)))

end LinearSubspaces

end

end MathlibExt.NumberTheory.LinearSubspacesWanted
