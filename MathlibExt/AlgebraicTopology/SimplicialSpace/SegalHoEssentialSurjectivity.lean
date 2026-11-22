/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Original Ho essential surjectivity from degree-zero component surjectivity.
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalHomotopyCategory

/-!
# Essential surjectivity from object components

A map between Segal spaces induces an essentially surjective homotopy-category functor whenever
its degree-zero map is surjective on simplicial components. Vertex representatives and the
object-component comparison construct the required isomorphisms in the target homotopy category.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SimplicialSpace.SegalHomotopy

/-- Original component surjectivity supplies a Ho essential-image witness.
No Ho equivalence, inverse functor or completeness outcome is assumed. -/
theorem map_essSurj_of_componentSurjective
    {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    (hc : Function.Surjective (SSet.mapπ₀ (f.hom.app (op ⦋0⦌)))) :
    (map f hW hV).EssSurj := by
  constructor
  intro v
  obtain ⟨c, hfc⟩ := hc (SSet.π₀.mk v.vertex)
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective c
  have hnat := objectComponentClass_naturality f hW hV (SSet.π₀.mk x)
  have hcomp := congrArg (objectComponentClass V hV) hfc
  rw [objectComponentClass_mk, objectQuotientMap_class] at hnat
  rw [objectComponentClass_mk] at hcomp
  have hclass := hnat.trans hcomp
  have hi := (objectClass_eq_iff V hV (mappingVertexMap f x) v.vertex).mp hclass
  refine ⟨⟨x⟩, ?_⟩
  change Nonempty ((⟨mappingVertexMap f x⟩ : Object V hV) ≅ ⟨v.vertex⟩)
  exact hi

end SimplicialSpace.SegalHomotopy
