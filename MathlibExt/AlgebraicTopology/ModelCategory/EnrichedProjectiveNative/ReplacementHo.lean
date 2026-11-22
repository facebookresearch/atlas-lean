/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.BifibrantReplacement
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Original native replacements on the actual level homotopy category

The original replacement functors preserve weak equivalences. The actual
localization construction therefore gives endofunctors on Ho(level), and
the literal original weak comparison arrows give natural isomorphisms to
the identity on every homotopy-category object and morphism.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.Replacement

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
attribute [local instance] Native.modelCategory

/-- Original Q also reflects the native weak class through its original natural trivial fibration.
-/
theorem cofibrantReplacement_map_weakEquivalence_iff
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) (cofibrantReplacement.map f) ↔
      weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) f := by
  constructor
  · intro hf
    apply (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)).of_precomp
      (cofibrantReplacementCounit.app X) f (cofibrantReplacementCounit_mem_weakEquivalences X)
    rw [← cofibrantReplacementCounit_naturality]
    exact (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)).comp_mem _ _ hf
      (cofibrantReplacementCounit_mem_weakEquivalences Y)
  · exact cofibrantReplacement_map_mem_weakEquivalences f

/-- Original R reflects the native weak class through its original natural trivial cofibration. -/
theorem fibrantReplacement_map_weakEquivalence_iff
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) (fibrantReplacement.map f) ↔
      weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) f := by
  constructor
  · intro hf
    apply (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)).of_postcomp f
      (fibrantReplacementUnit.app Y) (fibrantReplacementUnit_mem_weakEquivalences Y)
    rw [fibrantReplacementUnit_naturality]
    exact (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)).comp_mem _ _
      (fibrantReplacementUnit_mem_weakEquivalences X) hf
  · exact fibrantReplacement_map_mem_weakEquivalences f

/-- Both original replacement orders reflect the exact same level weak class. -/
theorem cofibrantFibrantReplacement_map_weakEquivalence_iff
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) (cofibrantFibrantReplacement.map f) ↔
      weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) f :=
  (fibrantReplacement_map_weakEquivalence_iff (cofibrantReplacement.map f)).trans
    (cofibrantReplacement_map_weakEquivalence_iff f)

/-- The reverse original replacement order reflects that same level weak class. -/
theorem fibrantCofibrantReplacement_map_weakEquivalence_iff
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) (fibrantCofibrantReplacement.map f) ↔
      weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) f :=
  (cofibrantReplacement_map_weakEquivalence_iff (fibrantReplacement.map f)).trans
    (fibrantReplacement_map_weakEquivalence_iff f)

/-- The literal original replacement followed by the actual level projection inverts level weak
maps. -/
theorem cofibrantReplacementHo_inverts :
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)).IsInvertedBy (cofibrantReplacement
      (A := A) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)) :=
  fun _ _ φ hφ => Localization.inverts (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v}
    A)) (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (cofibrantReplacement.map φ) (cofibrantReplacement_map_mem_weakEquivalences φ hφ)

/-- The actual original replacement action on the constructed level homotopy category. -/
def cofibrantReplacementHo : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ⥤
  HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
  Localization.Construction.lift (cofibrantReplacement (A := A) ⋙ toHomotopyCategory
    (EnrichedFunctorCat PointedCGWH.{u, v} A)) cofibrantReplacementHo_inverts

/-- The whole functor equality retains the original replacement action on all projected arrows. -/
theorem cofibrantReplacementHo_projection :
    toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ⋙ cofibrantReplacementHo (A := A) =
      cofibrantReplacement (A := A) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)
      :=
  Localization.Construction.fac _ _

/-- The exact constructed lifting comparison on the whole functor. -/
def cofibrantReplacementHoProjectionIso :
    toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ⋙ cofibrantReplacementHo (A := A) ≅
      cofibrantReplacement (A := A) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)
      :=
  eqToIso cofibrantReplacementHo_projection

/-- The actual strict construction supplies this lifting witness, without an incoming localization
dictionary. -/
@[instance_reducible]
def cofibrantReplacementHoLifting :
    Localization.Lifting (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
      (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A))
      (cofibrantReplacement (A := A) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
        (cofibrantReplacementHo (A := A)) :=
  ⟨cofibrantReplacementHoProjectionIso⟩

attribute [local instance] cofibrantReplacementHoLifting

/-- The original weak comparison gives the identity isomorphism on the whole actual Ho(level)
category. -/
def cofibrantReplacementHoIso : cofibrantReplacementHo (A := A) ≅ 𝟭 (HomotopyCategory
  (EnrichedFunctorCat PointedCGWH.{u, v} A)) :=
  Localization.liftNatIso (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (cofibrantReplacement (A := A) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (cofibrantReplacementHo (A := A)) (𝟭 (HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v}
      A))) cofibrantReplacementProjectionIso

/-- The induced action retains each literal original replacement map after projection. -/
theorem cofibrantReplacementHo_map_projected {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (φ : X
  ⟶ Y) :
    cofibrantReplacementHo.map ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
      φ) = (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
      (cofibrantReplacement.map φ) := by
  exact Functor.congr_hom cofibrantReplacementHo_projection φ

/-- The full isomorphism is natural for every level homotopy-category morphism. -/
theorem cofibrantReplacementHoIso_naturality
    {X Y : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)} (φ : X ⟶ Y) :
    cofibrantReplacementHo.map φ ≫ cofibrantReplacementHoIso.hom.app Y =
      cofibrantReplacementHoIso.hom.app X ≫ φ :=
  cofibrantReplacementHoIso.hom.naturality φ

/-- The actual replacement action is an equivalence of the level homotopy category. -/
theorem cofibrantReplacementHo_isEquivalence : (cofibrantReplacementHo (A := A)).IsEquivalence :=
  Functor.isEquivalence_of_iso cofibrantReplacementHoIso.symm

/-- The literal original replacement followed by the actual level projection inverts level weak
maps. -/
theorem fibrantReplacementHo_inverts :
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)).IsInvertedBy (fibrantReplacement (A
      := A) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)) :=
  fun _ _ φ hφ => Localization.inverts (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v}
    A)) (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (fibrantReplacement.map φ) (fibrantReplacement_map_mem_weakEquivalences φ hφ)

/-- The actual original replacement action on the constructed level homotopy category. -/
def fibrantReplacementHo : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ⥤
  HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
  Localization.Construction.lift (fibrantReplacement (A := A) ⋙ toHomotopyCategory
    (EnrichedFunctorCat PointedCGWH.{u, v} A)) fibrantReplacementHo_inverts

/-- The whole functor equality retains the original replacement action on all projected arrows. -/
theorem fibrantReplacementHo_projection :
    toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ⋙ fibrantReplacementHo (A := A) =
      fibrantReplacement (A := A) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
  Localization.Construction.fac _ _

/-- The exact constructed lifting comparison on the whole functor. -/
def fibrantReplacementHoProjectionIso :
    toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ⋙ fibrantReplacementHo (A := A) ≅
      fibrantReplacement (A := A) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
  eqToIso fibrantReplacementHo_projection

/-- The actual strict construction supplies this lifting witness, without an incoming localization
dictionary. -/
@[instance_reducible]
def fibrantReplacementHoLifting :
    Localization.Lifting (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
      (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A))
      (fibrantReplacement (A := A) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
        (fibrantReplacementHo (A := A)) :=
  ⟨fibrantReplacementHoProjectionIso⟩

attribute [local instance] fibrantReplacementHoLifting

/-- The original weak comparison gives the identity isomorphism on the whole actual Ho(level)
category. -/
def fibrantReplacementHoIso : fibrantReplacementHo (A := A) ≅ 𝟭 (HomotopyCategory
  (EnrichedFunctorCat PointedCGWH.{u, v} A)) :=
  Localization.liftNatIso (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (fibrantReplacement (A := A) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (fibrantReplacementHo (A := A)) (𝟭 (HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)))
      fibrantReplacementProjectionIso.symm

/-- The induced action retains each literal original replacement map after projection. -/
theorem fibrantReplacementHo_map_projected {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (φ : X ⟶
  Y) :
    fibrantReplacementHo.map ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map φ)
      = (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map (fibrantReplacement.map
      φ) := by
  exact Functor.congr_hom fibrantReplacementHo_projection φ

/-- The full isomorphism is natural for every level homotopy-category morphism. -/
theorem fibrantReplacementHoIso_naturality
    {X Y : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)} (φ : X ⟶ Y) :
    fibrantReplacementHo.map φ ≫ fibrantReplacementHoIso.hom.app Y = fibrantReplacementHoIso.hom.app
      X ≫ φ :=
  fibrantReplacementHoIso.hom.naturality φ

/-- The actual replacement action is an equivalence of the level homotopy category. -/
theorem fibrantReplacementHo_isEquivalence : (fibrantReplacementHo (A := A)).IsEquivalence :=
  Functor.isEquivalence_of_iso fibrantReplacementHoIso.symm

/-- The literal original replacement followed by the actual level projection inverts level weak
maps. -/
theorem cofibrantFibrantReplacementHo_inverts :
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)).IsInvertedBy
      (cofibrantFibrantReplacement (A := A) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u,
      v} A)) :=
  fun _ _ φ hφ => Localization.inverts (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v}
    A)) (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (cofibrantFibrantReplacement.map φ) (cofibrantFibrantReplacement_map_mem_weakEquivalences φ hφ)

/-- The actual original replacement action on the constructed level homotopy category. -/
def cofibrantFibrantReplacementHo : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ⥤
  HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
  Localization.Construction.lift (cofibrantFibrantReplacement (A := A) ⋙ toHomotopyCategory
    (EnrichedFunctorCat PointedCGWH.{u, v} A)) cofibrantFibrantReplacementHo_inverts

/-- The whole functor equality retains the original replacement action on all projected arrows. -/
theorem cofibrantFibrantReplacementHo_projection :
    toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ⋙ cofibrantFibrantReplacementHo (A
      := A) = cofibrantFibrantReplacement (A := A) ⋙ toHomotopyCategory (EnrichedFunctorCat
      PointedCGWH.{u, v} A) :=
  Localization.Construction.fac _ _

/-- The exact constructed lifting comparison on the whole functor. -/
def cofibrantFibrantReplacementHoProjectionIso :
    toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ⋙ cofibrantFibrantReplacementHo (A
      := A) ≅ cofibrantFibrantReplacement (A := A) ⋙ toHomotopyCategory (EnrichedFunctorCat
      PointedCGWH.{u, v} A) :=
  eqToIso cofibrantFibrantReplacementHo_projection

/-- The actual strict construction supplies this lifting witness, without an incoming localization
dictionary. -/
@[instance_reducible]
def cofibrantFibrantReplacementHoLifting :
    Localization.Lifting (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
      (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A))
      (cofibrantFibrantReplacement (A := A) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u,
        v} A)) (cofibrantFibrantReplacementHo (A := A)) :=
  ⟨cofibrantFibrantReplacementHoProjectionIso⟩

attribute [local instance] cofibrantFibrantReplacementHoLifting

/-- The original weak comparison gives the identity isomorphism on the whole actual Ho(level)
category. -/
def cofibrantFibrantReplacementHoIso : cofibrantFibrantReplacementHo (A := A) ≅ 𝟭 (HomotopyCategory
  (EnrichedFunctorCat PointedCGWH.{u, v} A)) :=
  Localization.liftNatIso (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (cofibrantFibrantReplacement (A := A) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u,
      v} A)) (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (cofibrantFibrantReplacementHo (A := A)) (𝟭 (HomotopyCategory (EnrichedFunctorCat
      PointedCGWH.{u, v} A))) cofibrantFibrantReplacementProjectionIso

/-- The induced action retains each literal original replacement map after projection. -/
theorem cofibrantFibrantReplacementHo_map_projected {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A}
  (φ : X ⟶ Y) :
    cofibrantFibrantReplacementHo.map ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v}
      A)).map φ) = (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
      (cofibrantFibrantReplacement.map φ) := by
  exact Functor.congr_hom cofibrantFibrantReplacementHo_projection φ

/-- The full isomorphism is natural for every level homotopy-category morphism. -/
theorem cofibrantFibrantReplacementHoIso_naturality
    {X Y : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)} (φ : X ⟶ Y) :
    cofibrantFibrantReplacementHo.map φ ≫ cofibrantFibrantReplacementHoIso.hom.app Y =
      cofibrantFibrantReplacementHoIso.hom.app X ≫ φ :=
  cofibrantFibrantReplacementHoIso.hom.naturality φ

/-- The actual replacement action is an equivalence of the level homotopy category. -/
theorem cofibrantFibrantReplacementHo_isEquivalence : (cofibrantFibrantReplacementHo (A :=
  A)).IsEquivalence :=
  Functor.isEquivalence_of_iso cofibrantFibrantReplacementHoIso.symm

/-- The literal original replacement followed by the actual level projection inverts level weak
maps. -/
theorem fibrantCofibrantReplacementHo_inverts :
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)).IsInvertedBy
      (fibrantCofibrantReplacement (A := A) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u,
      v} A)) :=
  fun _ _ φ hφ => Localization.inverts (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v}
    A)) (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (fibrantCofibrantReplacement.map φ) (fibrantCofibrantReplacement_map_mem_weakEquivalences φ hφ)

/-- The actual original replacement action on the constructed level homotopy category. -/
def fibrantCofibrantReplacementHo : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ⥤
  HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
  Localization.Construction.lift (fibrantCofibrantReplacement (A := A) ⋙ toHomotopyCategory
    (EnrichedFunctorCat PointedCGWH.{u, v} A)) fibrantCofibrantReplacementHo_inverts

/-- The whole functor equality retains the original replacement action on all projected arrows. -/
theorem fibrantCofibrantReplacementHo_projection :
    toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ⋙ fibrantCofibrantReplacementHo (A
      := A) = fibrantCofibrantReplacement (A := A) ⋙ toHomotopyCategory (EnrichedFunctorCat
      PointedCGWH.{u, v} A) :=
  Localization.Construction.fac _ _

/-- The exact constructed lifting comparison on the whole functor. -/
def fibrantCofibrantReplacementHoProjectionIso :
    toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ⋙ fibrantCofibrantReplacementHo (A
      := A) ≅ fibrantCofibrantReplacement (A := A) ⋙ toHomotopyCategory (EnrichedFunctorCat
      PointedCGWH.{u, v} A) :=
  eqToIso fibrantCofibrantReplacementHo_projection

/-- The actual strict construction supplies this lifting witness, without an incoming localization
dictionary. -/
@[instance_reducible]
def fibrantCofibrantReplacementHoLifting :
    Localization.Lifting (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
      (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A))
      (fibrantCofibrantReplacement (A := A) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u,
        v} A)) (fibrantCofibrantReplacementHo (A := A)) :=
  ⟨fibrantCofibrantReplacementHoProjectionIso⟩

attribute [local instance] fibrantCofibrantReplacementHoLifting

/-- The original weak comparison gives the identity isomorphism on the whole actual Ho(level)
category. -/
def fibrantCofibrantReplacementHoIso : fibrantCofibrantReplacementHo (A := A) ≅ 𝟭 (HomotopyCategory
  (EnrichedFunctorCat PointedCGWH.{u, v} A)) :=
  Localization.liftNatIso (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (fibrantCofibrantReplacement (A := A) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u,
      v} A)) (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (fibrantCofibrantReplacementHo (A := A)) (𝟭 (HomotopyCategory (EnrichedFunctorCat
      PointedCGWH.{u, v} A))) fibrantCofibrantReplacementProjectionIso

/-- The induced action retains each literal original replacement map after projection. -/
theorem fibrantCofibrantReplacementHo_map_projected {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A}
  (φ : X ⟶ Y) :
    fibrantCofibrantReplacementHo.map ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v}
      A)).map φ) = (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
      (fibrantCofibrantReplacement.map φ) := by
  exact Functor.congr_hom fibrantCofibrantReplacementHo_projection φ

/-- The full isomorphism is natural for every level homotopy-category morphism. -/
theorem fibrantCofibrantReplacementHoIso_naturality
    {X Y : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)} (φ : X ⟶ Y) :
    fibrantCofibrantReplacementHo.map φ ≫ fibrantCofibrantReplacementHoIso.hom.app Y =
      fibrantCofibrantReplacementHoIso.hom.app X ≫ φ :=
  fibrantCofibrantReplacementHoIso.hom.naturality φ

/-- The actual replacement action is an equivalence of the level homotopy category. -/
theorem fibrantCofibrantReplacementHo_isEquivalence : (fibrantCofibrantReplacementHo (A :=
  A)).IsEquivalence :=
  Functor.isEquivalence_of_iso fibrantCofibrantReplacementHoIso.symm

/-- The Q identity comparison at a projected object is the original mapped π, with its exact lifting
comparison. -/
theorem cofibrantReplacementHoIso_hom_projected
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    cofibrantReplacementHoIso.hom.app
        ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).obj X) =
      cofibrantReplacementHoProjectionIso.hom.app X ≫
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
          (cofibrantReplacementCounit.app X) := by
  rw [cofibrantReplacementHoIso, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  change
    (cofibrantReplacementHoProjectionIso.hom.app X ≫
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
        (cofibrantReplacementCounit.app X)) ≫
      𝟙 ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).obj X) =
    cofibrantReplacementHoProjectionIso.hom.app X ≫
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
        (cofibrantReplacementCounit.app X)
  exact Category.comp_id _

/-- The inverse R identity comparison at a projected object is the original mapped ι. -/
theorem fibrantReplacementHoIso_inv_projected
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fibrantReplacementHoIso.inv.app
        ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).obj X) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
          (fibrantReplacementUnit.app X) ≫ fibrantReplacementHoProjectionIso.inv.app X := by
  rw [fibrantReplacementHoIso, Localization.liftNatIso_inv, Localization.liftNatTrans_app]
  change
    (𝟙 ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).obj X) ≫
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
        (fibrantReplacementUnit.app X)) ≫ fibrantReplacementHoProjectionIso.inv.app X =
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
      (fibrantReplacementUnit.app X) ≫ fibrantReplacementHoProjectionIso.inv.app X
  rw [Category.id_comp]

end HomotopicalAlgebra.EnrichedProjective.Native.Replacement
