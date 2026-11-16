/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.EtaleLogNativeCategory

/-!
# Native small-etale log category construction

The target fixes the existing log objects/Homs, every underlying scheme
map, and every original log-section identity/composite. Only their
native ringed-site assembly and categorical laws are requested here.
Source: Kato Section1; Talpo--Vistoli arXiv:1410.1164v2, Definition6.10.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.EtaleLogNativeCategory

universe u

public def_wanted nativeEtaleLogCategory
    [MathlibExt.AlgebraicGeometry.EtaleLogDiagrams.InverseImageTheory.{u}] :
    MathlibExt.AlgebraicGeometry.EtaleLogNativeCategory.NativeCategoryModel.{u}

end WantedExt.AlgebraicGeometry.EtaleLogNativeCategory
