/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.CategoryTheory.PerfectDGModuleModels
public import MathlibExt.CategoryTheory.NativeDGNerveModels

/-!
# Wanted small perfect realizations

Construct a small DG category quasi-equivalent to the actual
cofibrant perfect-module subcategory. Perfection is already fixed by
native finite cells and localized retractions. The actual coherent-nerve
quasicategory law is the completed source proof in
NativeDGNerveModels.dgNerve_quasicategory. No moduli geometry,
categorical descent or K-theory conclusion is an input.

References: Toën--Vaquié, arXiv:math/0503269v5, §2.2;
Lurie, Higher Algebra, Construction 1.3.1.13.
-/

namespace WantedExt.AlgebraicGeometry.PerfectDGModuleModelsWanted

open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.PerfectDGModuleModels

universe u v

/-- Choose an actual small enhanced model of the fixed perfect DG modules. -/
def_wanted small_perfect_dg_model (k : Type u) [CommRing k] (C : DGCat k) :
  SmallPerfectModel C

end WantedExt.AlgebraicGeometry.PerfectDGModuleModelsWanted
