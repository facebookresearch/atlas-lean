/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.SuspendedFreeSphere
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.OriginalISuspensionCofibrantComparison

/-!
# Original suspended free spheres and strict scalar representatives

The actual I-cone comparison on cofibrant diagrams normalizes the whole
free-sphere source word. The original Q counit and the strict representative
remain in the equation; the map need not be the image under Q of another map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.FreeSphereHom

attribute [local instance] Native.modelCategory Native.allObjectsFibrant
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

private abbrev D := EnrichedFunctorCat PointedCGWH.{u, v} I
private abbrev H := toHomotopyCategory (D (I := I))
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := I)
private abbrev ε := Replacement.cofibrantReplacementCounit (B := B) (A := I)
private abbrev S := OriginalISuspension.suspension (B := B) (I := I)
private abbrev T := EnrichedFunctorCat.tensorLeft (A := I) PointedCGWH.sphereOne

/-- The forward suspended free-sphere map keeps the original three comparison legs. -/
theorem originalSuspendedFreeSphereIso_hom (a : I) (n : ℕ) :
    (originalSuspendedFreeSphereIso (B := B) a n).hom =
      (ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B)).hom.app
          (Free.object a (PointedCGWH.SphereHom.sphere n)) ≫
        H.map (T.map (ε.app (Free.object a (PointedCGWH.SphereHom.sphere n)))) ≫
          H.map (scalarFreeSphereIso a n).hom := rfl

/-- Every strict representative into the actual Q target has the exact scalar source word. -/
theorem originalSuspendedFreeSphereIso_strict_map (a : I) (n : ℕ) (Y : D (I := I))
    (g : Free.object a (PointedCGWH.SphereHom.sphere n) ⟶ Q.obj Y) :
    (originalSuspendedFreeSphereIso (B := B) a n).inv ≫
        H.map (S.map (ε.app (Free.object a (PointedCGWH.SphereHom.sphere n)) ≫ g)) ≫
          (ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B)).hom.app Y =
      H.map (scalarFreeSphereIso a n).inv ≫ H.map (T.map g) := by
  let X := Free.object a (PointedCGWH.SphereHom.sphere n)
  let _ : IsCofibrant (Q.obj X) := Replacement.isCofibrant_cofibrantReplacement X
  let _ : IsCofibrant (Q.obj Y) := Replacement.isCofibrant_cofibrantReplacement Y
  have hn := OriginalISuspensionCofibrantComparison.comparison_hom_naturality
    (B := B) (ε.app X ≫ g)
  change H.map (S.map (ε.app X ≫ g)) ≫
      (OriginalISuspensionCofibrantComparison.comparisonQ (B := B) Y).hom =
    (OriginalISuspensionCofibrantComparison.comparisonQ (B := B) X).hom ≫
      H.map (T.map (ε.app X ≫ g)) at hn
  rw [OriginalISuspensionCofibrantComparison.comparisonQ_hom_eq_original,
    OriginalISuspensionCofibrantComparison.comparisonQ_hom_eq_original] at hn
  apply (cancel_epi (originalSuspendedFreeSphereIso (B := B) a n).hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [originalSuspendedFreeSphereIso_hom]
  have hc := (H.mapIso (scalarFreeSphereIso a n)).hom_inv_id_assoc (H.map (T.map g))
  change H.map (scalarFreeSphereIso a n).hom ≫
      H.map (scalarFreeSphereIso a n).inv ≫ H.map (T.map g) = H.map (T.map g) at hc
  simp only [Category.assoc]
  rw [hc]
  simpa only [T.map_comp, H.map_comp] using hn

end HomotopicalAlgebra.EnrichedProjective.Native.FreeSphereHom
