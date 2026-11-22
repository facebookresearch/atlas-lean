/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.IndexKan.OriginalLevel
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenOrdinaryHoReplacement

/-!
# Actual native orthogonal Kan Hom functions

The original coend/restriction adjunction supplies both complete ordinary
level Hom functions. The source replacement is the original native I
record at the caller's same realized cardinal and bottom. Its original
counit appears in the forward and inverse formulas.

Every source arrow, target arrow and target morphism in the actual level
homotopy category keeps its original function. No adjoint Hom bijection,
stable model, new replacement, or native comparison outcome is an input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
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

private abbrev HA := toHomotopyCategory (AC.{u, v} (A := A))
private abbrev HO := toHomotopyCategory OC.{u, v}

/-- Both full original level Hom functions use the actual native coend adjunction. -/
def cofibrantHomEquiv (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : AC.{u, v} (A := A)) [IsCofibrant X] (E : OC.{u, v}) :
    (HO.obj ((originalLan j).obj X) ⟶ HO.obj E) ≃
      (HA.obj X ⟶ HA.obj ((EnrichedFunctorCat.restriction j).obj E)) := by
  let _ : (originalAdjunction j).IsQuillenAdjunction := originalAdjunction_isQuillen j
  let _ : IsFibrant E := allObjectsFibrant E
  exact QuillenOrdinaryHoHom.homEquiv (originalAdjunction j) X E

/-- The original forward Hom function retains every actual representative adjunct. -/
theorem cofibrantHomEquiv_map (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : AC.{u, v} (A := A)) [IsCofibrant X] (E : OC.{u, v})
    (f : (originalLan j).obj X ⟶ E) :
    cofibrantHomEquiv j X E (HO.map f) =
      HA.map ((originalAdjunction j).homEquiv X E f) := by
  let _ : (originalAdjunction j).IsQuillenAdjunction := originalAdjunction_isQuillen j
  let _ : IsFibrant E := allObjectsFibrant E
  exact QuillenOrdinaryHoHom.homEquiv_map (originalAdjunction j) X E f

/-- The original inverse Hom function retains the same original inverse adjunct. -/
theorem cofibrantHomEquiv_symm_map (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : AC.{u, v} (A := A)) [IsCofibrant X] (E : OC.{u, v})
    (f : X ⟶ (EnrichedFunctorCat.restriction j).obj E) :
    (cofibrantHomEquiv j X E).symm (HA.map f) =
      HO.map (((originalAdjunction j).homEquiv X E).symm f) := by
  let _ : (originalAdjunction j).IsQuillenAdjunction := originalAdjunction_isQuillen j
  let _ : IsFibrant E := allObjectsFibrant E
  exact QuillenOrdinaryHoHom.homEquiv_symm_map (originalAdjunction j) X E f

/-- The original replacement counit determines its actual level Ho isomorphism. -/
def originalQHoIso (X : AC.{u, v} (A := A)) :
    HA.obj ((originalQ (A := A)).obj X) ≅ HA.obj X := by
  let _ : WeakEquivalence ((originalQCounit (A := A)).app X) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr (originalQCounit_levelWeak X)
  exact QuillenOrdinaryHoReplacement.replacementHoIso ((originalQCounit (A := A)).app X)

/-- Its entire forward map is the unchanged original I-record counit. -/
theorem originalQHoIso_hom (X : AC.{u, v} (A := A)) :
    (originalQHoIso X).hom = HA.map ((originalQCounit (A := A)).app X) := rfl

/-- The actual original replacement constructs the complete Hom functions for every source. -/
def originalHomEquiv (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : AC.{u, v} (A := A)) (E : OC.{u, v}) :
    (HO.obj ((prolongedQ j).obj X) ⟶ HO.obj E) ≃
      (HA.obj X ⟶ HA.obj ((EnrichedFunctorCat.restriction j).obj E)) := by
  let _ : (originalAdjunction j).IsQuillenAdjunction := originalAdjunction_isQuillen j
  let _ : IsCofibrant ((originalQ (A := A)).obj X) := originalQ_isCofibrant X
  let _ : IsFibrant E := allObjectsFibrant E
  let _ : WeakEquivalence ((originalQCounit (A := A)).app X) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr (originalQCounit_levelWeak X)
  exact QuillenOrdinaryHoReplacement.homEquiv (originalAdjunction j)
    ((originalQCounit (A := A)).app X) E

/-- The whole forward function is inverse original counit followed by original adjunct. -/
theorem originalHomEquiv_apply (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : AC.{u, v} (A := A)) (E : OC.{u, v})
    (f : HO.obj ((prolongedQ j).obj X) ⟶ HO.obj E) :
    originalHomEquiv j X E f = (originalQHoIso X).inv ≫
      (letI : IsCofibrant ((originalQ (A := A)).obj X) := originalQ_isCofibrant X
       cofibrantHomEquiv j ((originalQ (A := A)).obj X) E f) := by
  let _ : (originalAdjunction j).IsQuillenAdjunction := originalAdjunction_isQuillen j
  let _ : IsCofibrant ((originalQ (A := A)).obj X) := originalQ_isCofibrant X
  let _ : IsFibrant E := allObjectsFibrant E
  let _ : WeakEquivalence ((originalQCounit (A := A)).app X) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr (originalQCounit_levelWeak X)
  exact QuillenOrdinaryHoReplacement.homEquiv_apply (originalAdjunction j)
    ((originalQCounit (A := A)).app X) E f

/-- The whole inverse function uses the same mapped original counit before inverse adjunct. -/
theorem originalHomEquiv_symm_apply
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : AC.{u, v} (A := A)) (E : OC.{u, v})
    (f : HA.obj X ⟶ HA.obj ((EnrichedFunctorCat.restriction j).obj E)) :
    (originalHomEquiv j X E).symm f =
      (letI : IsCofibrant ((originalQ (A := A)).obj X) := originalQ_isCofibrant X
       (cofibrantHomEquiv j ((originalQ (A := A)).obj X) E).symm
         (HA.map ((originalQCounit (A := A)).app X) ≫ f)) := by
  let _ : (originalAdjunction j).IsQuillenAdjunction := originalAdjunction_isQuillen j
  let _ : IsCofibrant ((originalQ (A := A)).obj X) := originalQ_isCofibrant X
  let _ : IsFibrant E := allObjectsFibrant E
  let _ : WeakEquivalence ((originalQCounit (A := A)).app X) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr (originalQCounit_levelWeak X)
  exact QuillenOrdinaryHoReplacement.homEquiv_symm_apply (originalAdjunction j)
    ((originalQCounit (A := A)).app X) E f

/-- Every represented target arrow uses the same full original forward adjunct and counit. -/
theorem originalHomEquiv_map (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : AC.{u, v} (A := A)) (E : OC.{u, v}) (f : (prolongedQ j).obj X ⟶ E) :
    originalHomEquiv j X E (HO.map f) = (originalQHoIso X).inv ≫
      HA.map ((originalAdjunction j).homEquiv ((originalQ (A := A)).obj X) E f) := by
  rw [originalHomEquiv_apply]
  let _ : IsCofibrant ((originalQ (A := A)).obj X) := originalQ_isCofibrant X
  rw [cofibrantHomEquiv_map]

/-- Every original source arrow retains the entire Q-counit naturality square. -/
theorem originalHomEquiv_source (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    {X Y : AC.{u, v} (A := A)} (f : X ⟶ Y) (E : OC.{u, v})
    (g : HO.obj ((prolongedQ j).obj Y) ⟶ HO.obj E) :
    originalHomEquiv j X E (HO.map ((prolongedQ j).map f) ≫ g) =
      HA.map f ≫ originalHomEquiv j Y E g := by
  let _ : (originalAdjunction j).IsQuillenAdjunction := originalAdjunction_isQuillen j
  let _ : IsCofibrant ((originalQ (A := A)).obj X) := originalQ_isCofibrant X
  let _ : IsCofibrant ((originalQ (A := A)).obj Y) := originalQ_isCofibrant Y
  let _ : IsFibrant E := allObjectsFibrant E
  let _ : WeakEquivalence ((originalQCounit (A := A)).app X) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr (originalQCounit_levelWeak X)
  let _ : WeakEquivalence ((originalQCounit (A := A)).app Y) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr (originalQCounit_levelWeak Y)
  exact QuillenOrdinaryHoReplacement.homEquiv_coefficient (originalAdjunction j)
    ((originalQCounit (A := A)).app Y) ((originalQCounit (A := A)).app X) E f
    ((originalQ (A := A)).map f) ((originalQCounit (A := A)).naturality f) g

/-- The inverse function keeps the same entire original source/Q/Lan square. -/
theorem originalHomEquiv_symm_source
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    {X Y : AC.{u, v} (A := A)} (f : X ⟶ Y) (E : OC.{u, v})
    (g : HA.obj Y ⟶ HA.obj ((EnrichedFunctorCat.restriction j).obj E)) :
    (originalHomEquiv j X E).symm (HA.map f ≫ g) =
      HO.map ((prolongedQ j).map f) ≫ (originalHomEquiv j Y E).symm g := by
  apply (originalHomEquiv j X E).injective
  rw [Equiv.apply_symm_apply, originalHomEquiv_source, Equiv.apply_symm_apply]

/-- Every original target arrow retains the actual full restriction map. -/
theorem originalHomEquiv_target (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : AC.{u, v} (A := A)) {E E' : OC.{u, v}}
    (f : HO.obj ((prolongedQ j).obj X) ⟶ HO.obj E) (g : E ⟶ E') :
    originalHomEquiv j X E' (f ≫ HO.map g) =
      originalHomEquiv j X E f ≫ HA.map ((EnrichedFunctorCat.restriction j).map g) := by
  let _ : (originalAdjunction j).IsQuillenAdjunction := originalAdjunction_isQuillen j
  let _ : IsCofibrant ((originalQ (A := A)).obj X) := originalQ_isCofibrant X
  let _ : IsFibrant E := allObjectsFibrant E
  let _ : IsFibrant E' := allObjectsFibrant E'
  let _ : WeakEquivalence ((originalQCounit (A := A)).app X) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr (originalQCounit_levelWeak X)
  exact QuillenOrdinaryHoReplacement.homEquiv_target (originalAdjunction j)
    ((originalQCounit (A := A)).app X) f g

/-- Every inverse target function uses the same original restriction and target maps. -/
theorem originalHomEquiv_symm_target
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : AC.{u, v} (A := A)) {E E' : OC.{u, v}}
    (f : HA.obj X ⟶ HA.obj ((EnrichedFunctorCat.restriction j).obj E)) (g : E ⟶ E') :
    (originalHomEquiv j X E').symm
        (f ≫ HA.map ((EnrichedFunctorCat.restriction j).map g)) =
      (originalHomEquiv j X E).symm f ≫ HO.map g := by
  apply (originalHomEquiv j X E').injective
  rw [Equiv.apply_symm_apply, originalHomEquiv_target, Equiv.apply_symm_apply]

/-- The original full Hom functions form a natural transformation on actual target arrows. -/
def originalHomNatTrans (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : AC.{u, v} (A := A)) :
    HO ⋙ coyoneda.obj (Opposite.op (HO.obj ((prolongedQ j).obj X))) ⟶
      HO ⋙ (restrictionHoFunctor j ⋙ coyoneda.obj (Opposite.op (HA.obj X))) where
  app E := TypeCat.ofHom (originalHomEquiv j X E)
  naturality E E' f := by
    ext g
    change originalHomEquiv j X E' (g ≫ HO.map f) =
      originalHomEquiv j X E g ≫ (restrictionHoFunctor j).map (HO.map f)
    rw [restrictionHoFunctor_map]
    exact originalHomEquiv_target j X g f

set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual level Ho target morphism preserves the complete original forward function. -/
theorem originalHomEquiv_targetHo
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : AC.{u, v} (A := A)) {E E' : OC.{u, v}}
    (f : HO.obj ((prolongedQ j).obj X) ⟶ HO.obj E) (g : HO.obj E ⟶ HO.obj E') :
    originalHomEquiv j X E' (f ≫ g) =
      originalHomEquiv j X E f ≫ (restrictionHoFunctor j).map g := by
  have h := (Localization.Construction.natTransExtension
    (originalHomNatTrans j X)).naturality_apply g f
  simp only [Localization.Construction.natTransExtension_app,
    Localization.Construction.NatTransExtension.app_eq] at h
  change originalHomEquiv j X E' (f ≫ g) =
    originalHomEquiv j X E f ≫ (restrictionHoFunctor j).map g at h
  exact h

set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual level Ho target morphism also preserves the original inverse function. -/
theorem originalHomEquiv_symm_targetHo
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : AC.{u, v} (A := A)) {E E' : OC.{u, v}}
    (f : HA.obj X ⟶ HA.obj ((EnrichedFunctorCat.restriction j).obj E))
    (g : HO.obj E ⟶ HO.obj E') :
    (originalHomEquiv j X E').symm (f ≫ (restrictionHoFunctor j).map g) =
      (originalHomEquiv j X E).symm f ≫ g := by
  apply (originalHomEquiv j X E').injective
  rw [Equiv.apply_symm_apply, originalHomEquiv_targetHo, Equiv.apply_symm_apply]

end PointedCGWH.Spectra.Orthogonal.IndexKan
