/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Monoidal.RightModulePresentation
public import MathlibExt.CategoryTheory.Monoidal.RightModuleFree

/-!
# Generator and Hom formulas for the existing free right-module adjunction

Every object, map, unit, counit, and Hom function belongs to
`RightModuleFree.functor` and `RightModuleFree.adjunction`. The formulas expose
their actual monoidal-opposite construction. No second free functor or
adjunction is constructed, and no commutativity hypothesis is needed.
-/
