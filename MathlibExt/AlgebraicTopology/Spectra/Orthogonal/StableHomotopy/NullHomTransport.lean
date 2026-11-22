/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.ShiftedHom

/-!
# Null classes of the original orthogonal scalar Hom functions

Every ordinary level homotopy arrow preserves the original null class by
the actual Q counit and fundamental lemma. The full scalar adjunct sends
the original zero factorization through its actual cotensored zero. Both
original suspension Hom functions therefore retain the same null class.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NullHomTransport

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open PointedCGWH.Spectra.Orthogonal.ShiftedHomTests

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C := OrthogonalCarrier.{u, v}
private abbrev scalarLoop := cotensor (I := O.{u, v}) PointedCGWH.sphereOne.{u, v}
private abbrev scalarSuspension :=
  EnrichedFunctorCat.tensorLeft (A := O.{u, v}) PointedCGWH.sphereOne.{u, v}
private abbrev scalarAdjunction :=
  ScalarLeibniz.adjunction (A := O.{u, v}) PointedCGWH.sphereOne.{u, v}
private instance nativeZero : HasZeroObject C.{u, v} := Diagrams.nativeHasZeroObject

/-- Both original native zero legs form exactly the ordinary null map. -/
theorem nativeNullMap (X E : C.{u, v}) :
    Diagrams.toZero X ≫ Diagrams.zeroTo E = OrdinaryHoCofiberKernel.nullMap X E :=
  OrdinaryHoChosenPuppe.actualNullMap_eq_chosen
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero X E

/-- The full original scalar adjunct sends the same native null map to
the ordinary null map through its actual cotensored zero. -/
theorem scalarAdjunct_null (X E : C.{u, v}) :
    scalarAdjunction.homEquiv X E (OrdinaryHoCofiberKernel.nullMap
        (scalarSuspension.obj X) E) =
      OrdinaryHoCofiberKernel.nullMap X (scalarLoop.obj E) := by
  let Z : C.{u, v} := Diagrams.zeroDiagram
  let hZ : IsZero (scalarLoop.obj Z) := NativeK.cotensorZero_isZero PointedCGWH.sphereOne
  have hA : scalarAdjunction.homEquiv X Z (Diagrams.toZero (scalarSuspension.obj X)) =
      hZ.isTerminal.from X := hZ.isTerminal.hom_ext _ _
  have hR : scalarLoop.map (Diagrams.zeroTo E) = hZ.isInitial.to (scalarLoop.obj E) :=
    hZ.isInitial.hom_ext _ _
  rw [← nativeNullMap (scalarSuspension.obj X) E, scalarAdjunction.homEquiv_naturality_right,
    hA, hR]
  exact OrdinaryHoChosenPuppe.actualNullMap_eq_chosen (scalarLoop.obj Z) hZ X
    (scalarLoop.obj E)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev H := toHomotopyCategory C.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := O.{u, v})
private abbrev ε := Replacement.cofibrantReplacementCounit (B := B) (A := O.{u, v})
private abbrev S := OriginalISuspension.suspension (B := B) (I := O.{u, v})

private theorem nativeFibrant (X : C.{u, v}) : IsFibrant X :=
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant X

private theorem qCofibrant (X : C.{u, v}) : IsCofibrant (Q.obj X) :=
  Replacement.isCofibrant_cofibrantReplacement (B := B) X

private theorem scalarQuillen : scalarAdjunction.{u, v}.IsQuillenAdjunction := by
  let _ : IsCofibrant PointedCGWH.sphereOne.{u, v} :=
    PointedCGWH.modelCategory.sphereOne_isCofibrant
  exact ScalarCompatibility.scalar_isQuillen (B := B) PointedCGWH.sphereOne

attribute [local instance] nativeFibrant qCofibrant scalarQuillen

/-- Every full ordinary level Ho source morphism preserves the unchanged
original null class, using its actual original Q representative. -/
theorem precomp_nullHom {X Y E : C.{u, v}} (f : H.obj X ⟶ H.obj Y) :
    f ≫ OrdinaryHoCofiberKernel.nullHom Y E = OrdinaryHoCofiberKernel.nullHom X E := by
  obtain ⟨a, ha⟩ := map_surjective_of_isLocalization H (Q.obj X) Y
    ((epsilonHoIso X).hom ≫ f)
  have hε : (epsilonHoIso X).hom = H.map (ε.app X) :=
    Replacement.cofibrantReplacementProjectionIso_hom_app X
  apply (cancel_epi (epsilonHoIso X).hom).mp
  have hLeft : (epsilonHoIso X).hom ≫ (f ≫ OrdinaryHoCofiberKernel.nullHom Y E) =
      OrdinaryHoCofiberKernel.nullHom (Q.obj X) E :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ OrdinaryHoCofiberKernel.nullHom Y E) ha.symm).trans
        (OrdinaryHoCofiberKernel.precomp_nullHom (C := C.{u, v}) a))
  have hRight : (epsilonHoIso X).hom ≫ OrdinaryHoCofiberKernel.nullHom X E =
      OrdinaryHoCofiberKernel.nullHom (Q.obj X) E :=
    (congrArg (fun t => t ≫ OrdinaryHoCofiberKernel.nullHom X E) hε).trans
      (OrdinaryHoCofiberKernel.precomp_nullHom (C := C.{u, v}) (ε.app X))
  exact hLeft.trans hRight.symm

/-- Every whole ordinary Ho target map retains that same original null class. -/
theorem nullHom_postcomp {X Y E : C.{u, v}} (g : H.obj Y ⟶ H.obj E) :
    OrdinaryHoCofiberKernel.nullHom X Y ≫ g = OrdinaryHoCofiberKernel.nullHom X E :=
  OrdinaryHoCofiberKernel.nullHom_postcomp g

/-- The actual scalar Ho adjunct retains the original null class at
every full scalar target shift. -/
theorem scalarHomEquiv_null (r : ℕ) (X E : C.{u, v}) :
    scalarHomEquiv r X E (OrdinaryHoCofiberKernel.nullHom
        (scalarSuspension.obj (Q.obj X)) ((loopTarget r).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (Q.obj X) ((loopTarget (r + 1)).obj E) := by
  change QuillenOrdinaryHoHom.homEquiv scalarAdjunction (Q.obj X) ((loopTarget r).obj E)
      (H.map (OrdinaryHoCofiberKernel.nullMap
        (scalarSuspension.obj (Q.obj X)) ((loopTarget r).obj E))) = _
  rw [QuillenOrdinaryHoHom.homEquiv_map]
  exact H.congr_map (scalarAdjunct_null (Q.obj X) ((loopTarget r).obj E))

/-- Both original endpoint isomorphisms and the full scalar adjunct
retain the same original suspension null class. -/
theorem suspensionHomEquiv_null (r : ℕ) (X E : C.{u, v}) :
    suspensionHomEquiv r X E (OrdinaryHoCofiberKernel.nullHom
        (S.obj (Q.obj X)) ((loopTarget r).obj E)) =
      OrdinaryHoCofiberKernel.nullHom X ((loopTarget (r + 1)).obj E) := by
  rw [suspensionHomEquiv_apply, precomp_nullHom, scalarHomEquiv_null, precomp_nullHom]

/-- The entire inverse suspension Hom function retains the original null
class as well, in every source and target shift. -/
theorem suspensionHomEquiv_symm_null (r : ℕ) (X E : C.{u, v}) :
    (suspensionHomEquiv r X E).symm
        (OrdinaryHoCofiberKernel.nullHom X ((loopTarget (r + 1)).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (S.obj (Q.obj X)) ((loopTarget r).obj E) := by
  apply (suspensionHomEquiv r X E).injective
  rw [Equiv.apply_symm_apply, suspensionHomEquiv_null]

end PointedCGWH.Spectra.Orthogonal.NullHomTransport
