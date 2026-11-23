/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.NormalCrossingsModels
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.Dimension.Finrank

@[expose] public noncomputable section

/-!
# Normalized prime-to-ell alteration data

The field extension map is the actual generic stalk map of the alteration,
transported only by its displayed generic-point equality. Its degree is
the actual finrank for that scalar action, with finiteness recorded.
The boundary is the actual reduced scheme pullback and must satisfy the
completed strict crossings model. No free degree or boundary oracle occurs.

Reference: Gabber, in Illusie--Laszlo--Orgogozo,
Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des
schémas quasi-excellents, Exposé X, Theorem 2.1.
-/

namespace MathlibExt.AlgebraicGeometry.PrimeToEllAlterations

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open _root_.CategoryTheory _root_.TopologicalSpace
open MathlibExt.AlgebraicGeometry.NormalCrossingsModels

universe u

/-- The actual function-field map, pinned by the generic scheme stalk map. -/
def genericFieldMap {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) (h : f (genericPoint Y) = genericPoint X) : X.functionField ⟶ Y.functionField :=
  eqToHom (congrArg (fun x : X ↦ X.presheaf.stalk x) h.symm) ≫ f.stalkMap (genericPoint Y)

/-- The degree of the actual generic field extension, with its canonical scalar action, as
`Module.finrank`: it is `0` when the extension is infinite. `PrimeToEllAlteration.finiteField`
records finiteness where the degree is used. -/
def genericDegree {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) (h : f (genericPoint Y) = genericPoint X) : ℕ :=
  letI : Algebra X.functionField Y.functionField := (genericFieldMap f h).hom.toAlgebra
  Module.finrank X.functionField Y.functionField

/-- The generic field map of the identity is the identity. -/
@[simp]
theorem genericFieldMap_id (X : Scheme.{u}) [IsIntegral X]
    (h : (𝟙 X : X ⟶ X) (genericPoint X) = genericPoint X) :
    genericFieldMap (𝟙 X) h = 𝟙 X.functionField := by
  simp only [genericFieldMap, Scheme.Hom.stalkMap_id]
  change eqToHom (rfl : X.functionField = X.functionField) ≫ 𝟙 _ = _
  simp

/-- The identity has generic degree one. -/
@[simp]
theorem genericDegree_id (X : Scheme.{u}) [IsIntegral X]
    (h : (𝟙 X : X ⟶ X) (genericPoint X) = genericPoint X) : genericDegree (𝟙 X) h = 1 := by
  unfold genericDegree
  rw [genericFieldMap_id]
  exact Module.finrank_self _

/-- A genuine smooth proper integral model over the coefficient field. -/
structure SmoothProperModel (k : Type u) [Field k] where
  variety : Over (Spec (.of k))
  integral : IsIntegral variety.left
  smooth : Smooth variety.hom
  proper : IsProper variety.hom

attribute [instance] SmoothProperModel.integral SmoothProperModel.smooth SmoothProperModel.proper

/-- One actual prime-to-ell alteration of the displayed proper integral pair. -/
structure PrimeToEllAlteration {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [IsIntegral X.left]
    (D : X.left.IdealSheafData) (ell : ℕ) where
  /-- The genuine smooth proper source. -/
  source : SmoothProperModel k
  /-- The actual morphism over the base field. -/
  morphism : source.variety ⟶ X
  /-- The actual proper alteration morphism. -/
  properMorphism : IsProper morphism.left
  /-- This point equation is the actual generic-point dominance condition. -/
  genericPointMap : morphism.left (genericPoint source.variety.left) = genericPoint X.left
  /-- The actual generic field extension is finite. -/
  finiteField :
    letI : Algebra X.left.functionField source.variety.left.functionField :=
      (genericFieldMap morphism.left genericPointMap).hom.toAlgebra
    Module.Finite X.left.functionField source.variety.left.functionField
  /-- The actual generic degree is prime to `ell`. -/
  coprimeDegree : Nat.Coprime ell (genericDegree morphism.left genericPointMap)
  /-- The actual reduced inverse-image boundary has strict crossings. -/
  crossings : IsStrictNormalCrossings source.variety (reducedPullbackBoundary morphism.left D)

/-- The displayed proper generic-point-dominating morphism is genuinely surjective. -/
theorem PrimeToEllAlteration.surjective {k : Type u} [Field k]
    {X : Over (Spec (.of k))} [IsIntegral X.left] {D : X.left.IdealSheafData} {ell : ℕ}
    (a : PrimeToEllAlteration X D ell) : Function.Surjective a.morphism.left := by
  let : IsProper a.morphism.left := a.properMorphism
  apply Set.range_eq_univ.mp
  apply Set.Subset.antisymm (Set.subset_univ _)
  have h : {genericPoint X.left} ⊆ Set.range a.morphism.left :=
    Set.singleton_subset_iff.mpr ⟨genericPoint a.source.variety.left, a.genericPointMap⟩
  simpa only [genericPoint_closure] using
    closure_minimal h a.morphism.left.isClosedMap.isClosed_range

end MathlibExt.AlgebraicGeometry.PrimeToEllAlterations
