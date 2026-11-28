/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SemistableReduction

/-!
# Semistable reduction probes

The split torus of rank zero carries its Hopf-algebra group law by instance search, and the
identity of the trivial group scheme over a field, which is locally of finite type, is its identity
component.
-/

@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.SemistableReduction

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.SemistableReduction
open scoped CategoryTheory.MonObj

variable (k : Type) [Field k]

-- The split torus of rank zero, `Spec k[ℤ⁰]`, is a commutative group scheme over `k`.
example : GrpObj (splitTorus k 0) := inferInstance

example : IsCommMonObj (splitTorus k 0) := inferInstance

/-- The trivial group scheme `Spec k` is locally of finite type over `k`. -/
instance locallyOfFiniteType_unit : LocallyOfFiniteType (𝟙_ (Over (Spec (.of k)))).hom := by
  change LocallyOfFiniteType (𝟙 (Spec (.of k)))
  infer_instance

/-- The identity of the trivial group scheme `Spec k` over a field is its identity component. -/
theorem isIdentityComponent_id_unit : IsIdentityComponent (𝟙 (𝟙_ (Over (Spec (.of k))))) := by
  refine ⟨?_, ?_, ?_⟩
  · change IsOpenImmersion (𝟙 (Spec (.of k)))
    infer_instance
  · infer_instance
  · intro x
    change Set.range (𝟙 (Spec (.of k))) = connectedComponent _
    rw [PreconnectedSpace.connectedComponent_eq_univ]
    exact Set.range_eq_univ.mpr fun y ↦ ⟨y, rfl⟩

end MathlibExtTest.AlgebraicGeometry.SemistableReduction
