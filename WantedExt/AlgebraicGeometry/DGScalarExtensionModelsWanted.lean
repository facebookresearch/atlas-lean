/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.CategoryTheory.DGScalarExtensionModels

/-!
# Wanted enriched derived scalar extension

The output enrichment of restriction is specified on actual pointwise
components. Extension is normalized against every raw target module by
the enriched adjunction and its explicit unit formula. No strict DG
functorial cofibrant-replacement oracle is assumed.

References: Keller, Deriving DG categories, §6; Toën,
arXiv:math/0408337v7, §3; Toën--Vaquié, arXiv:math/0503269v5, §2.2.
-/

open CategoryTheory
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGScalarExtensionModels

universe u

/-- Enrich the literal precomposition restriction with its fixed components. -/
def_wanted enriched_dg_module_restriction (k : Type u) [CommRing k]
    (C D : DGCat k) (f : C ⟶ D) : RestrictionModel f

/-- Construct scalar extension on cofibrant objects with the displayed enriched adjunction. -/
def_wanted cofibrant_dg_module_scalar_extension (k : Type u) [CommRing k]
    (C D : DGCat k) (f : C ⟶ D) (R : RestrictionModel f) : ExtensionModel f R

/-- Scalar extension preserves the native localized finite-cell retractions. -/
theorem_wanted dg_scalar_extension_preserves_perfect (k : Type u) [CommRing k]
    (C D : DGCat k) (f : C ⟶ D) (R : RestrictionModel f) (L : ExtensionModel f R) :
  PreservesPerfect L
