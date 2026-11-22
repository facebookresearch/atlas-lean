/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeScalarComponentWeakPreservation
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.IndexCofibrantProperness
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Replacement

/-!
# Actual native cofibrant components and original scalar replacement maps

Every native projective cofibrant object's components are cofibrant by
evaluating its original zero inclusion. The original source Hom family and
same-cardinal generation data prove that evaluated inclusion is a base
cofibration. This applies to every original cofibrant replacement, with its
unchanged zero map and counit. Component cofibrancy of a replacement's target
is proved; no projective cofibrancy premise on an arbitrary caller is added.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.NativeCofibrantComponents

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

attribute [local instance] Native.modelCategory

/-- Evaluation of the original zero inclusion proves component cofibrancy for
every cofibrant object of the same native projective model. -/
theorem component_isCofibrant
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsCofibrant X] (a : I) :
    IsCofibrant (X.toEnrichedFunctor.obj a) := by
  have hi : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) (Diagrams.zeroTo X) :=
    (cofibration_iff _).mp
      ((isCofibrant_iff_of_isInitial (Diagrams.zeroTo X)
        Diagrams.zeroDiagramIsInitial).mp inferInstance)
  have hEval := IndexCofibrantProperness.originalNativeCofibration_component_cofibration
    hHom (Diagrams.zeroTo X) hi a
  exact (isCofibrant_iff_of_isInitial ((evaluation a).map (Diagrams.zeroTo X))
    (Diagrams.initialDiagram_component_isZero a).isInitial).mpr
      ((cofibration_iff _).mpr hEval)

/-- All original component functions remain those of the same native object. -/
theorem allComponents_isCofibrant
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsCofibrant X] :
    ∀ a : I, IsCofibrant (X.toEnrichedFunctor.obj a) :=
  component_isCofibrant hHom X

/-- The actual original same-cardinal cofibrant replacement has cofibrant
components at every original index, for every arbitrary caller object. -/
theorem originalQ_component_isCofibrant
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) (a : I) :
    IsCofibrant
      (((Replacement.cofibrantReplacement (B := B)).obj X).toEnrichedFunctor.obj a) := by
  let _ : IsCofibrant ((Replacement.cofibrantReplacement (B := B)).obj X) :=
    Replacement.isCofibrant_cofibrantReplacement X
  exact component_isCofibrant hHom _ a

/-- The full original replacement object has all cofibrant components. -/
theorem originalQ_allComponents_isCofibrant
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    ∀ a : I, IsCofibrant
      (((Replacement.cofibrantReplacement (B := B)).obj X).toEnrichedFunctor.obj a) :=
  originalQ_component_isCofibrant hHom X

/-- Actual scalar tensor preserves all original level-weak maps between native
cofibrant objects, deriving the required component hypotheses from the model. -/
theorem scalarMap_levelWeak_of_nativeCofibrant
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (T : PointedCGWH.{u, v}) [IsCofibrant T]
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y)
    (hf : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) f) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)
      ((EnrichedFunctorCat.tensorLeft T).map f) :=
  NativeScalarComponentWeakPreservation.tensorMap_levelWeak_of_componentCofibrant
    T f (allComponents_isCofibrant hHom X) (allComponents_isCofibrant hHom Y) hf

/-- The whole original Q counit is level weak after scalar tensor whenever the
caller's genuine components are cofibrant. The Q components are derived above. -/
theorem scalar_originalQcounit_levelWeak_of_componentCofibrant
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (T : PointedCGWH.{u, v}) [IsCofibrant T]
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (hX : ∀ a : I, IsCofibrant (X.toEnrichedFunctor.obj a)) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)
      ((EnrichedFunctorCat.tensorLeft T).map
        ((Replacement.cofibrantReplacementCounit (B := B)).app X)) :=
  NativeScalarComponentWeakPreservation.tensorMap_levelWeak_of_componentCofibrant
    T ((Replacement.cofibrantReplacementCounit (B := B)).app X)
      (originalQ_allComponents_isCofibrant hHom X) hX
      (Replacement.cofibrantReplacementCounit_mem_weakEquivalences X)

/-- Native cofibrancy of the original caller derives the entire original Q
counit comparison under every actual cofibrant scalar. -/
theorem scalar_originalQcounit_levelWeak_of_nativeCofibrant
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (T : PointedCGWH.{u, v}) [IsCofibrant T]
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsCofibrant X] :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)
      ((EnrichedFunctorCat.tensorLeft T).map
        ((Replacement.cofibrantReplacementCounit (B := B)).app X)) :=
  scalar_originalQcounit_levelWeak_of_componentCofibrant hHom T X
    (allComponents_isCofibrant hHom X)

end HomotopicalAlgebra.EnrichedProjective.Native.NativeCofibrantComponents
