/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModuleMappingComparison
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.StandardRightFreeEvaluation
public import Mathlib.CategoryTheory.Enriched.Opposite

public import MathlibExt.CategoryTheory.Enriched.OfObjectFunction

/-!
# The enriched index of free right sphere modules

The index category is induced from the opposite of the free right sphere modules at
tensor-unit coefficients. Its enriched Hom from `d` to `e` is the module mapping object
from the free module at `e` to the free module at `d`; identities and composition use
the module enrichment with the coefficient braiding.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory Opposite
open scoped MonoidalClosed CategoryTheory.MonObj



namespace PointedCGWH.SymmetricDRight

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal
  sphereSequenceMonObj sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction
  SymmetricModuleMappingComparison.literalEnrichedOrdinaryCategory

/-- The entire original standard RIGHT module carrier. -/
abbrev Carrier := SymmetricModuleMappingComparison.Carrier.{u, v}

/-- The genuine original standard RIGHT F_d S0, at the original actual free functor. -/
@[no_expose]
def freeObject (d : Operad.SmallFinBijGroupoid) : Carrier.{u, v} :=
  (SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} d).obj
    (𝟙_ PointedCGWH.{u, v})

/-- The original actual degree labels of D_R, without an incoming category or law. -/
structure Index where
  /-- The original degree label of the independent source object. -/
  asIndex : Operad.SmallFinBijGroupoid

/-- The independent original source object at the supplied degree. -/
def obj (d : Operad.SmallFinBijGroupoid) : Index := ⟨d⟩

/-- The independent mapping category is opposite to the actual original free modules. -/
def freeLabel (d : Index) : Carrier.{u, v}ᵒᵖ := op (freeObject d.asIndex)

/-- Full D_R enrichment is derived from the actual standard module mapping category. -/
instance enrichedCategory : EnrichedCategory PointedCGWH.{u, v} Index :=
  EnrichedCategory.ofObjectFunction freeLabel

/-- The actual independent D_R(d,e) is exactly R-Mod(F_e S0,F_d S0). -/
theorem Hom_eq (d e : Operad.SmallFinBijGroupoid) :
    (obj d ⟶[PointedCGWH.{u, v}] obj e) =
      SymmetricRightModuleMapping.Hom (freeObject e) (freeObject d) := by rfl

/-- Original source identity is the actual original module identity on F_d S0. -/
theorem identity_eq (d : Operad.SmallFinBijGroupoid) :
    eId PointedCGWH.{u, v} (obj d) =
      SymmetricRightModuleMapping.homEquiv (freeObject d) (freeObject d) (𝟙 (freeObject d)) :=
  (eHomEquiv_id PointedCGWH.{u, v} (freeObject d)).symm

/-- Original D_R composition flips both complete incoming Hom factors by the actual value braid
before the actual R-linear module composition. -/
theorem composition_eq (d e k : Operad.SmallFinBijGroupoid) :
    eComp PointedCGWH.{u, v} (obj d) (obj e) (obj k) =
      (β_ (SymmetricRightModuleMapping.Hom (freeObject e) (freeObject d))
        (SymmetricRightModuleMapping.Hom (freeObject k) (freeObject e))).hom ≫
          SymmetricModuleMappingComparison.originalComposition
            (freeObject k) (freeObject e) (freeObject d) := by
  rw [← SymmetricModuleMappingComparison.literalEnrichedCategory_composition]
  exact eComp_op_eq PointedCGWH.{u, v}
    (op (freeObject k)) (op (freeObject e)) (op (freeObject d))

/-- The whole original standard free functor value remains explicit. -/
theorem freeObject_eq (d : Operad.SmallFinBijGroupoid) : freeObject.{u, v} d =
    (SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} d).obj
      (𝟙_ PointedCGWH.{u, v}) := by rfl

end PointedCGWH.SymmetricDRight
