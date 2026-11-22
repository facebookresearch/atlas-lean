/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.IndexKan.OriginalHom

/-!
# Original native Lan of the original replacement counit

The unchanged source I replacement and original Lan give a full natural
counit from Lan Q to Lan. Brown's original level Quillen law makes this
counit level weak when the original source is cofibrant. Both original
replacement endpoints remain explicit in all source-map squares.

Its actual mapped arrow gives the Hom equivalence comparing raw Lan
tests and Lan Q tests. The original counit, its inverse in ordinary Ho,
and every actual source and target function are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.IndexKan

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev OC := OrthogonalCarrier.{u, v}

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

private abbrev AC := EnrichedFunctorCat PointedCGWH.{u, v} A

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev HO := toHomotopyCategory OC.{u, v}

/-- Every actual level weak map between cofibrant sources has its same weak Lan map. -/
theorem originalLan_levelWeak_of_cofibrant
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    {X Y : AC.{u, v} (A := A)} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) (hf : weakEquivalences (AC.{u, v} (A := A)) f) :
    weakEquivalences OC.{u, v} ((originalLan j).map f) := by
  let _ : (originalAdjunction j).IsQuillenAdjunction := originalAdjunction_isQuillen j
  let _ : WeakEquivalence f := (HomotopicalAlgebra.weakEquivalence_iff _).mpr hf
  exact (CategoryTheory.Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
    (adj := originalAdjunction j) f).mem

/-- The whole original Lan of the same original I-record Q counit. -/
def originalLanQCounit (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    prolongedQ (B := B) j ⟶ originalLan j where
  app X := (originalLan j).map ((originalQCounit (B := B) (A := A)).app X)
  naturality X Y f := by
    change (originalLan j).map ((originalQ (B := B) (A := A)).map f) ≫
        (originalLan j).map ((originalQCounit (B := B) (A := A)).app Y) =
      (originalLan j).map ((originalQCounit (B := B) (A := A)).app X) ≫
        (originalLan j).map f
    rw [← (originalLan j).map_comp, ← (originalLan j).map_comp]
    exact congrArg (fun a => (originalLan j).map a)
      ((originalQCounit (B := B) (A := A)).naturality f)

/-- The entire counit is the actual right whiskering of the original Q counit. -/
theorem originalLanQCounit_eq_whisker
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    originalLanQCounit j =
      whiskerRight (originalQCounit (B := B) (A := A)) (originalLan j) ≫
        (Functor.leftUnitor (originalLan j)).hom := by
  apply NatTrans.ext
  apply funext
  intro X
  change (originalLan j).map ((originalQCounit (B := B) (A := A)).app X) =
    (originalLan j).map ((originalQCounit (B := B) (A := A)).app X) ≫
      𝟙 ((originalLan j).obj X)
  exact (Category.comp_id ((originalLan j).map
    ((originalQCounit (B := B) (A := A)).app X))).symm

/-- Each complete original counit component is the same actual Lan map of original epsilon. -/
theorem originalLanQCounit_app
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (X : AC.{u, v} (A := A)) :
    (originalLanQCounit j).app X =
      (originalLan j).map ((originalQCounit (B := B) (A := A)).app X) := rfl

/-- Every whole original source arrow retains the same original Q-counit naturality square. -/
theorem originalLanQCounit_naturality
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    {X Y : AC.{u, v} (A := A)} (f : X ⟶ Y) :
    (prolongedQ (B := B) j).map f ≫ (originalLanQCounit j).app Y =
      (originalLanQCounit j).app X ≫ (originalLan j).map f :=
  (originalLanQCounit j).naturality f

/-- The original Lan Q counit is level weak on each genuinely cofibrant original source. -/
theorem originalLanQCounit_levelWeak
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : AC.{u, v} (A := A)) [IsCofibrant X] :
    weakEquivalences OC.{u, v} ((originalLanQCounit j).app X) := by
  let _ : IsCofibrant ((originalQ (B := B) (A := A)).obj X) := originalQ_isCofibrant X
  let εX : (originalQ (B := B) (A := A)).obj X ⟶ X :=
    (originalQCounit (B := B) (A := A)).app X
  exact originalLan_levelWeak_of_cofibrant j εX (originalQCounit_levelWeak X)

/-- The original Lan Q counit satisfies every full original orthogonal Omega-target test. -/
theorem originalLanQCounit_omegaTests
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : AC.{u, v} (A := A)) [IsCofibrant X] :
    NativeK.omegaTests orthogonalFamily ((originalLanQCounit j).app X) :=
  NativeK.levelWeak_le_omegaTests orthogonalFamily _ (originalLanQCounit_levelWeak j X)

/-- Its actual original mapped arrow gives the level Ho isomorphism between Lan Q and Lan. -/
def originalLanQHoIso (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : AC.{u, v} (A := A)) [IsCofibrant X] :
    HO.obj ((prolongedQ (B := B) j).obj X) ≅ HO.obj ((originalLan j).obj X) := by
  let _ : WeakEquivalence ((originalLanQCounit j).app X) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr (originalLanQCounit_levelWeak j X)
  exact QuillenOrdinaryHoReplacement.replacementHoIso ((originalLanQCounit j).app X)

/-- The whole forward isomorphism map is the original Lan of the same original Q counit. -/
theorem originalLanQHoIso_hom
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : AC.{u, v} (A := A)) [IsCofibrant X] :
    (originalLanQHoIso j X).hom = HO.map ((originalLanQCounit j).app X) := rfl

/-- Both original Hom functions compare raw Lan with the same full original Lan Q. -/
def originalLanQHomEquiv (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : AC.{u, v} (A := A)) [IsCofibrant X] (E : OC.{u, v}) :
    (HO.obj ((originalLan j).obj X) ⟶ HO.obj E) ≃
      (HO.obj ((prolongedQ (B := B) j).obj X) ⟶ HO.obj E) := by
  let _ : WeakEquivalence ((originalLanQCounit j).app X) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr (originalLanQCounit_levelWeak j X)
  exact QuillenOrdinaryHoReplacement.replacementPrecompEquiv
    ((originalLanQCounit j).app X) E

/-- The full forward Hom function is precomposition by that unchanged mapped original counit. -/
theorem originalLanQHomEquiv_apply
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : AC.{u, v} (A := A)) [IsCofibrant X] (E : OC.{u, v})
    (g : HO.obj ((originalLan j).obj X) ⟶ HO.obj E) :
    originalLanQHomEquiv j X E g = HO.map ((originalLanQCounit j).app X) ≫ g := rfl

/-- The full inverse Hom function uses the inverse of the same original mapped counit. -/
theorem originalLanQHomEquiv_symm_apply
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : AC.{u, v} (A := A)) [IsCofibrant X] (E : OC.{u, v})
    (g : HO.obj ((prolongedQ (B := B) j).obj X) ⟶ HO.obj E) :
    (originalLanQHomEquiv j X E).symm g = (originalLanQHoIso j X).inv ≫ g := rfl

/-- Every full original source square retains both mapped original replacement counits. -/
theorem originalLanQHomEquiv_source
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    {X Y : AC.{u, v} (A := A)} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) (E : OC.{u, v}) (g : HO.obj ((originalLan j).obj Y) ⟶ HO.obj E) :
    originalLanQHomEquiv j X E (HO.map ((originalLan j).map f) ≫ g) =
      HO.map ((prolongedQ (B := B) j).map f) ≫ originalLanQHomEquiv j Y E g := by
  rw [originalLanQHomEquiv_apply, originalLanQHomEquiv_apply]
  rw [← Category.assoc, ← Category.assoc, ← HO.map_comp, ← HO.map_comp]
  exact congrArg (fun a => HO.map a ≫ g) (originalLanQCounit_naturality j f).symm

/-- The full inverse source function retains both original Lan source maps. -/
theorem originalLanQHomEquiv_symm_source
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    {X Y : AC.{u, v} (A := A)} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) (E : OC.{u, v})
    (g : HO.obj ((prolongedQ (B := B) j).obj Y) ⟶ HO.obj E) :
    (originalLanQHomEquiv j X E).symm (HO.map ((prolongedQ (B := B) j).map f) ≫ g) =
      HO.map ((originalLan j).map f) ≫ (originalLanQHomEquiv j Y E).symm g := by
  apply (originalLanQHomEquiv j X E).injective
  rw [Equiv.apply_symm_apply, originalLanQHomEquiv_source, Equiv.apply_symm_apply]

/-- Every target Ho morphism retains the whole forward counit Hom function. -/
theorem originalLanQHomEquiv_targetHo
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : AC.{u, v} (A := A)) [IsCofibrant X] {E E' : OC.{u, v}}
    (g : HO.obj ((originalLan j).obj X) ⟶ HO.obj E) (h : HO.obj E ⟶ HO.obj E') :
    originalLanQHomEquiv j X E' (g ≫ h) = originalLanQHomEquiv j X E g ≫ h := by
  rw [originalLanQHomEquiv_apply, originalLanQHomEquiv_apply, Category.assoc]

/-- Every target Ho morphism retains the inverse of the same original counit function. -/
theorem originalLanQHomEquiv_symm_targetHo
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : AC.{u, v} (A := A)) [IsCofibrant X] {E E' : OC.{u, v}}
    (g : HO.obj ((prolongedQ (B := B) j).obj X) ⟶ HO.obj E) (h : HO.obj E ⟶ HO.obj E') :
    (originalLanQHomEquiv j X E').symm (g ≫ h) =
      (originalLanQHomEquiv j X E).symm g ≫ h := by
  rw [originalLanQHomEquiv_symm_apply, originalLanQHomEquiv_symm_apply, Category.assoc]

end PointedCGWH.Spectra.Orthogonal.IndexKan
