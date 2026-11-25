/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @junekim623, Muse
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import MathlibExt.Algebra.Category.ModuleCat.Presheaf.Closed
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic

/-!
# Monoidal closed structure for sheaves of modules

Sheafification over a sheaf of commutative rings is monoidal. Day reflection
from presheaves gives the monoidal closed structure on sheaves of modules,
with the tensor-unit isomorphism.
-/
