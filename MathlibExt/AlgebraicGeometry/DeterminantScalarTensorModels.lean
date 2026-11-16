/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BoundedScalarDeterminants
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Normalized native scalar tensor, unit and dual comparisons

The functor is the actual native extension of scalars. Its comparisons
are fixed on every source adjunction-unit vector and every target scalar.
The dual comparison is tested on every original functional/vector pair.
These are ordinary completed-source integration maps, not arbitrary
functors or line trivializations.

References: Stacks Project, Tags 0FJW/0FJX; native Mathlib tensor-product
base change and finite-projective duality.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.DeterminantScalarTensorModels

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open BoundedScalarDeterminants
open scoped TensorProduct

variable {R S : CommRingCat.{0}} (g : R ⟶ S)

/-- The actual source-unit vector in the native scalar extension. -/
def vector (M : ModuleCat.{0} R) (x : M) : (ModuleCat.extendScalars g.hom).obj M :=
  (ModuleCat.extendRestrictScalarsAdj g.hom).unit.app M x

/-- Scalar comparisons retain the whole native tensor and dual action. -/
structure ScalarTensorSources where
  unit : (ModuleCat.extendScalars g.hom).obj (𝟙_ (ModuleCat.{0} R)) ≅
    𝟙_ (ModuleCat.{0} S)
  unit_normalized : ∀ (s : S) (r : R),
    unit.hom (s • vector g (𝟙_ (ModuleCat.{0} R)) r) = s * g.hom r
  tensor : ∀ M N : ModuleCat.{0} R,
    (ModuleCat.extendScalars g.hom).obj (M ⊗ N) ≅
      (ModuleCat.extendScalars g.hom).obj M ⊗ (ModuleCat.extendScalars g.hom).obj N
  tensor_normalized : ∀ (M N : ModuleCat.{0} R) (s : S) (m : M) (n : N),
    (tensor M N).hom (s • vector g (M ⊗ N) (m ⊗ₜ[R] n)) =
      (s • vector g M m) ⊗ₜ[S] vector g N n
  dual : ∀ M : ModuleCat.{0} R, Module.Finite R M → Module.Projective R M →
    ((ModuleCat.extendScalars g.hom).obj (ModuleCat.of R (Module.Dual R M)) ≅
      ModuleCat.of S (Module.Dual S ((ModuleCat.extendScalars g.hom).obj M)))
  dual_normalized : ∀ (M : ModuleCat.{0} R) (hF : Module.Finite R M)
    (hP : Module.Projective R M) (s t : S) (f : Module.Dual R M) (v : M),
    (dual M hF hP).hom
      (s • vector g (ModuleCat.of R (Module.Dual R M)) f) (t • vector g M v) =
        s * t * g.hom (f v)

end MathlibExt.AlgebraicGeometry.DeterminantScalarTensorModels
