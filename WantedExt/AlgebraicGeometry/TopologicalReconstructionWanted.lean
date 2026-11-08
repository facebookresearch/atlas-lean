/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Topological reconstruction theorems for varieties

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.AlgebraicGeometry.TopologicalReconstruction` — kollar_lieblich_olsson_sawin (manifest `manifests/problems/kollar_lieblich_olsson_sawin.toml`, rev 1, submitter Junyan Xu, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.AlgebraicGeometry.TopologicalReconstructionWanted` namespace. Mathematical
statements are unchanged. Source: János Kollár, Max Lieblich, Martin Olsson, and Will Sawin. The Zariski topology, linear systems, and algebraic varieties.
-/
module


public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Topology.Category.Profinite.Nobeling.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
open AlgebraicGeometry

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.TopologicalReconstructionWanted
/-!
# Topological reconstruction theorems for varieties

Let X and Y be normal, projective, irreducible schemes over fields of characteristic 0.
Assume that
* dim X ≥ 4, or
* dim X ≥ 3 and the fields are finitely generated field extensions of ℚ, or
* dim X ≥ 2 and the fields are uncountable.
Then every homeomorphism between X and Y extends to an isomorphism of schemes.
This theorem is the culmination of several reconstruction results proved in [KLOS20, Kol20].

The approach in [KLOS] naturally breaks into two parts:
* Reconstruction of a scheme from the underlying topological space together with the
  additional information of the linear equivalence relation on divisors.
* Reconstruction of linear equivalence from the topological space.

## Reference

* [KLOS] János Kollár, Max Lieblich, Martin Olsson, and Will Sawin.
  The Zariski topology, linear systems, and algebraic varieties.
  https://williamsawin.com/ReconstructionBook.pdf or
  https://max.lieblich.us/wp-content/uploads/2021/09/reconstructionweb.pdf

* [KLOS20] János Kollár, Max Lieblich, Martin Olsson, and Will Sawin.
  Topological reconstruction theorems for varieties. https://arxiv.org/abs/2003.04847

* [Kol20] János Kollár. What determines a variety? https://arxiv.org/abs/2002.12424
-/

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.TopologicalReconstruction

universe u

/-- The structure morphism from a projective space `ℙⁿ_R` to `Spec R`. -/
noncomputable def projToSpec {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] : Proj 𝒜 ⟶ Spec (.of R) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap ..))

/-- A morphism from a scheme to Spec R is projective if it factors through some
closed immersion into ℙⁿ_R. -/
def IsProjectiveHom {X : Scheme} {R : Type*} [CommRing R] (f : X ⟶ Spec (.of R)) : Prop :=
  let := @MvPolynomial.gradedAlgebra
  ∃ (n : ℕ) (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin n) R)),
    IsClosedImmersion i ∧ f = i ≫ projToSpec _

/-- A scheme X is normal if for all `x : X` the local ring O_{X,x} is a normal domain. -/
def IsNormalScheme (X : Scheme) : Prop :=
  ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)

/- Theorem 1.4.3 in the reference. -/
/-- Source: János Kollár, Max Lieblich, Martin Olsson, and Will Sawin. The Zariski topology, linear systems, and algebraic varieties. Via leanprover/lean-eval@38361be, problem `kollar_lieblich_olsson_sawin`. -/
public theorem_wanted kollar_lieblich_olsson_sawin (X Y : Scheme.{u}) (K L : Type u)
    [Field K] [Field L] [CharZero K] [CharZero L] [IrreducibleSpace X] [IrreducibleSpace Y]
    (norm_X : IsNormalScheme X) (f : X ⟶ Spec (.of K)) (proj_f : IsProjectiveHom f)
    (norm_Y : IsNormalScheme Y) (g : Y ⟶ Spec (.of L)) (proj_g : IsProjectiveHom g)
    (h : 4 ≤ topologicalKrullDim X ∨
      (3 ≤ topologicalKrullDim X ∧ Algebra.EssFiniteType ℚ K ∧ Algebra.EssFiniteType ℚ L) ∨
      (2 ≤ topologicalKrullDim X ∧ Uncountable K ∧ Uncountable L))
    (homeo : X ≃ₜ Y) : ∃ iso : X ≅ Y, (iso.hom : X → Y) = homeo

end AlgebraicGeometry.TopologicalReconstruction

end MathlibExt.AlgebraicGeometry.TopologicalReconstructionWanted
