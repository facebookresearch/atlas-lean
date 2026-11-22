/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeHomotopyEdge

/-!
# The original relative homotopy classes are actual mapping components

Every elementary original marked cylinder homotopy is precisely a full
maximal relative mapping edge. Native quotient recursion in both
directions therefore identifies the generated original homotopy classes
with the actual connected components. The original representative map,
zero vertex, base triangle and full marked homotopy are retained.
This is not a claim that components alone detect arbitrary weak spaces.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped Simplicial

namespace SSet.Marked

/-- Every original relative homotopy class maps to its actual maximal mapping component. -/
def relativeHomotopyClassToPi0 (Z : Marked.{u}) (X Y : Over Z) :
    (relativeIntervalCylinder Z).HomotopyClass X Y →
      SSet.π₀ (relativeMappingComplex .maximal X.hom Y.hom) := by
  change Quot (@HomRel.CompClosure (Over Z) _ (relativeIntervalCylinder Z).elementaryHomotopyRel X Y) → _
  refine Quot.lift (fun f => SSet.π₀.mk (relativeMappingVertexEquiv Z X Y f)) ?_
  intro f g h
  have H : Nonempty (((relativeIntervalCylinder Z).app X).LeftHomotopy f g) :=
    (HomRel.compClosure_iff_self (r := (relativeIntervalCylinder Z).elementaryHomotopyRel) f g).mp h
  obtain ⟨H⟩ := H
  exact SSet.π₀.sound (relativeHomotopyMappingEdge H)

/-- Every actual maximal relative mapping component gives its original native marked homotopy class. -/
def relativePi0ToHomotopyClass (Z : Marked.{u}) (X Y : Over Z) :
    SSet.π₀ (relativeMappingComplex .maximal X.hom Y.hom) →
      (relativeIntervalCylinder Z).HomotopyClass X Y :=
  SSet.π₀.lift (fun x => (relativeIntervalCylinder Z).homotopyQuotientFunctor.map
    ((relativeMappingVertexEquiv Z X Y).symm x)) (by
    intro x y e
    let V := relativeMappingVertexEquiv Z X Y
    let e' : SSet.Edge (V (V.symm x)) (V (V.symm y)) :=
      e.ofEq (V.apply_symm_apply x).symm (V.apply_symm_apply y).symm
    exact (relativeIntervalCylinder Z).homotopyQuotientFunctor_map_eq (relativeMappingEdgeHomotopy e'))

/-- The original whole representative map is sent to its own exact relative mapping vertex component. -/
theorem relativeHomotopyClassToPi0_map (Z : Marked.{u}) (X Y : Over Z) (f : X ⟶ Y) :
    relativeHomotopyClassToPi0 Z X Y ((relativeIntervalCylinder Z).homotopyQuotientFunctor.map f) =
      SSet.π₀.mk (relativeMappingVertexEquiv Z X Y f) := rfl

/-- The same actual component vertex is read back as its original native marked slice map class. -/
theorem relativePi0ToHomotopyClass_mk (Z : Marked.{u}) (X Y : Over Z)
    (x : (relativeMappingComplex .maximal X.hom Y.hom) _⦋0⦌) :
    relativePi0ToHomotopyClass Z X Y (SSet.π₀.mk x) =
      (relativeIntervalCylinder Z).homotopyQuotientFunctor.map ((relativeMappingVertexEquiv Z X Y).symm x) :=
  SSet.π₀.lift_mk _ _ x

/-- The native original marked relative homotopy classes are exactly the actual maximal mapping components,
  at every value universe. -/
def relativeHomotopyClassEquivPi0 (Z : Marked.{u}) (X Y : Over Z) :
    (relativeIntervalCylinder Z).HomotopyClass X Y ≃
      SSet.π₀ (relativeMappingComplex .maximal X.hom Y.hom) where
  toFun := relativeHomotopyClassToPi0 Z X Y
  invFun := relativePi0ToHomotopyClass Z X Y
  left_inv c := by
    obtain ⟨f, rfl⟩ := (relativeIntervalCylinder Z).homotopyQuotientFunctor.map_surjective c
    rw [relativeHomotopyClassToPi0_map, relativePi0ToHomotopyClass_mk, Equiv.symm_apply_apply]
  right_inv c := by
    obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective c
    rw [relativePi0ToHomotopyClass_mk, relativeHomotopyClassToPi0_map, Equiv.apply_symm_apply]

/-- The whole representative formula of the native component equivalence remains exactly the original marked
  map's zero vertex. -/
theorem relativeHomotopyClassEquivPi0_map (Z : Marked.{u}) (X Y : Over Z) (f : X ⟶ Y) :
    relativeHomotopyClassEquivPi0 Z X Y ((relativeIntervalCylinder Z).homotopyQuotientFunctor.map f) =
      SSet.π₀.mk (relativeMappingVertexEquiv Z X Y f) := rfl

end SSet.Marked
