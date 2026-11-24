/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.DGFrameCoefficientUnits

/-!
# Actual DG-frame interval/module source requests

The whole one-simplex module is obtained from the original complete
enriched functor. Both endpoint comparisons restrict the same native
induction unit along the original cosimplicial degeneracy, using its
actual split-retraction equation and every component of the fixed
restriction/extension adjunction. These requests do not posit a strict
natural transformation between arbitrary frame endpoint functors.

Source: Toen--Vaquie math/0503269v5, Section3.1 pp36--37 and the DG-module
mapping-space description; original normalized DG/module source
revisions and licenses remain in the imported models.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.DGFrameCoefficientUnitsWanted

open _root_.CategoryTheory _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedDGModuli
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DGFrameCoefficientUnits
open scoped Simplicial

universe u

/-- Construct the literal component-normalized restriction identification for an actual source split retraction. -/
def_wanted native_restriction_composite_identity (k : Type u) [CommRing k]
    (A B : DGCat k) (f : A ⟶ B) (g : B ⟶ A) (h : f ≫ g = 𝟙 A)
    (Rf : RestrictionModel f) (Rg : RestrictionModel g) :
  RestrictionCompositeIdentity f g h Rf Rg

/-- Construct the full uncurried/projective module carried by this same actual moduli simplex. -/
def_wanted native_moduli_simplex_module (k : Type u) [CommRing k]
    (T : DGCat k) (F : DGFrame k (oppositeCategory T))
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N) (P : StrictPerfectSystem N S)
    (A : SAlg k) (n : SimplexCategory) (e : ((moduliFunctor F P).obj A).obj (op n)) :
  SimplexModulePoint F P A n e

/-- The actual source endpoint and degeneracy maps induce their fixed tensor-generator envelope maps. -/
def_wanted native_frame_envelope_retraction (k : Type u) [CommRing k]
    (T : DGCat k) (F : DGFrame k (oppositeCategory T))
    (N : ShuffleAlgebraFunctor k) (A : SAlg k) :
  FrameEnvelopeRetraction F (N := N) A

variable {k : Type u} [CommRing k] {T : DGCat k} (F : DGFrame k (oppositeCategory T))
  {N : ShuffleAlgebraFunctor k} (A : SAlg k)
  (B : FrameEnvelopeRetraction F (N := N) A)
  (R : RestrictionModel B.retraction.functor) (E : ExtensionModel B.retraction.functor R)
  (S : ∀ i : Fin 2, RestrictionModel (B.endpoint i).functor)
  (I : ∀ i : Fin 2, RestrictionCompositeIdentity (B.endpoint i).functor
    B.retraction.functor (B.commutes i) (S i) R)
  (M : DGDerivedModules k (frameEnvelope F (N := N) A ⦋1⦌))

/-- Each actual endpoint map restricts the same induction unit, and is an objectwise weak module comparison. -/
theorem_wanted native_endpoint_induction_unit_quasi_isomorphism (i : Fin 2)
    (x : (frameEnvelope F (N := N) A ⦋0⦌)ᵒᵖ) :
  QuasiIso (moduleComponent (endpointInductionUnit F A B R E S I M i) x)

end WantedExt.AlgebraicGeometry.DGFrameCoefficientUnitsWanted
