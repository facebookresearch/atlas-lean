/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import MathlibExt.NumberTheory.PrimeCounting.ThinnedWallisPrimeProduct
public import MathlibExt.NumberTheory.PrimeCounting.ThinnedWallisPrimeProductAsymptotic
public import MathlibExt.NumberTheory.PrimeCounting.ThinnedWallisPrimeProductConstant
public import MathlibExt.NumberTheory.PrimeCounting.WallisPrimeFactor

/-! # Thinned Wallis-type prime products modulo `2^m`

Re-exports the proved asymptotic, convergence criterion, constant formula and Wallis factor
identity from Mike Winkler, *Thinned Wallis-Type Prime Products in Residue Classes Modulo 2^m*,
INTEGERS 26 (2026), Article A90.
-/
