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

/-- When `x = x¹` and `y = y¹` are lines, the distance is the usual distance on the
projective space, given by `d(x¹,y¹) = sin ∡(x¹,y¹)`. -/
def distLines (x y : ℙ ℝ ℝᵈ) : ℝ := sin (angle x.rep y.rep)

/-- Then, if `x = x¹` is a line and `y = yᵏ` a k-dimensional subspace, we set
`d(x¹,yᵏ) = min { d(x¹, y¹) : y¹ ≤ yᵏ }`. -/
def distLineSubspace (x : ℙ ℝ ℝᵈ) (y : Submodule ℝ ℝᵈ) : ℝ :=
  ⨅ y' : {y' : ℙ ℝ ℝᵈ // y'.submodule ≤ y}, distLines x y'.1

/-- Finally, in general, if `x = xˡ` is `l`-dimensional and `y = yᵏ` is `k`-dimensional, then
`d(xˡ, yᵏ) = max { d(y¹, xˡ) : y¹ ≤ yᵏ }`, if `k ≤ l`, and
`d(xˡ, yᵏ) = max { d(x¹, yᵏ) : x¹ ≤ xˡ }`, if `k ≥ l`. -/
def distSubspaces (x y : Submodule ℝ ℝᵈ) : ℝ :=
  if finrank ℝ y ≤ finrank ℝ x then
    ⨆ y' : {y' : ℙ ℝ ℝᵈ // y'.submodule ≤ y}, distLineSubspace y'.1 x
  else
    ⨆ x' : {x' : ℙ ℝ ℝᵈ // x'.submodule ≤ x}, distLineSubspace x'.1 y

/-- The lattice `ℤᵈ`, as a `ℤ`-submodule of `ℝᵈ`. -/
abbrev intPoints : Submodule ℤ ℝᵈ :=
  .span ℤ (Set.range (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)

local notation "ℤᵈ" => intPoints

/-- Given a subspace `V ≤ ℝᵈ`, this is the set `V ∩ ℤᵈ` as a `ℤ`-submodule of `V`. -/
def intPointsSubspace (V : Submodule ℝ ℝᵈ) : Submodule ℤ V :=
  ZLattice.comap ℝ ℤᵈ V.subtype

instance (V : Submodule ℝ ℝᵈ) : DiscreteTopology (intPointsSubspace V) :=
  ZLattice.comap_discreteTopology ℝ _ (by fun_prop) V.injective_subtype

/-- A subspace `V ≤ ℝᵈ` is called rational, if `V ∩ ℤᵈ` is a full-rank lattice in `V`.
Note that the paper never explicitly mentions the definition of "rational subspace" they are
using. The one we use here is common, and it is the most convenient for defining heights
of rational subspaces below. -/
abbrev IsRational (V : Submodule ℝ ℝᵈ) : Prop :=
  IsZLattice ℝ (intPointsSubspace V)

/-- For a rational subspace `V ≤ ℝᵈ`, a choice of a `ℤ`-basis of the lattice `V ∩ ℤᵈ`, viewed
as an `ℝ`-basis of `V`. -/
def chosenBasis (V : Submodule ℝ ℝᵈ) (hV : IsRational V) : Basis (Fin (finrank ℝ V)) ℝ V :=
  .ofZLatticeBasis ℝ _ <| .reindex (Free.chooseBasis ℤ (intPointsSubspace V)) <|
    Fintype.equivFinOfCardEq <| by rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ]

/-- For a rational subspace `V ≤ ℝᵈ`, choose a basis `v₁, ... vₖ` for the subgroup `V ∩ ℤᵈ`.
The height is defined as `H(v) = ‖v₁ ∧ ··· ∧ vₖ‖`, where the norm on `⋀ᵏ ℝᵈ` is the usual
Euclidean norm. -/
def height (V : Submodule ℝ ℝᵈ) (hV : IsRational V) : ℝ :=
  ‖ιMulti ℝ _ (V.subtype ∘ chosenBasis V hV)‖

/-- For a subspace `x ≤ ℝᵈ` and `k : ℕ`, define the diophantine exponent of `x`
for approximation by `k`-dimensional rational subspaces by
`βₖ(x) = inf { β > 0 | ∃ c > 0 : ∀ v ∈ Xₖ(ℚ), d(v, x) ≥ c * H(v)^(−β) }.` -/
def diophantineExponent (k : ℕ) (x : Submodule ℝ ℝᵈ) : ℝ≥0∞ :=
  sInf (.ofReal '' {β : ℝ | β > 0 ∧ ∃ c > 0, ∀ v : Submodule ℝ ℝᵈ, finrank ℝ v = k →
    (hv : IsRational v) → distSubspaces v x ≥ c * height v hv ^ (-β)})

/--
Statement of Theorem 1 (Dirichlet's principle in Grassmann varieties):

For all `l`-dimensional subspaces `x ≤ ℝᵈ` and all `k ∈ {1,...,l}`, we have
`βₖ(x) ≥ d / (k * (d - l))`, and this lower bound is optimal.
Source: N. de Saxcé, `Rational approximations to linear subspaces`, Annals of Math, 203 (3) 2026. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2026-203-3-LinearSubspaces.lean Via leanprover/lean-eval@38361be, problem `annals_linear_subspaces`.
-/
public theorem_wanted theorem_1
    (hd : 2 ≤ d) (l : ℕ) (hl0 : 0 < l) (hld : l < d) (k : ℕ) (hk1 : 1 ≤ k) (hkl : k ≤ l) :
    (∀ x : Submodule ℝ ℝᵈ, finrank ℝ x = l → diophantineExponent k x ≥ d / (k * (d - l))) ∧
    (∃ x : Submodule ℝ ℝᵈ, finrank ℝ x = l ∧ diophantineExponent k x = d / (k * (d - l)))

end LinearSubspaces

end

end MathlibExt.NumberTheory.LinearSubspacesWanted
