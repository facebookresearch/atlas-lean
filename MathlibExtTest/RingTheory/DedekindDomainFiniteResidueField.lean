/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import MathlibExt.RingTheory.DedekindDomain.FiniteResidueField

open IsDedekindDomain

/-- The residue field of the adic completion integers at a place of `ℤ` with
finite residue field is finite. -/
example (v : HeightOneSpectrum ℤ) [Finite (ℤ ⧸ v.asIdeal)] :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) :=
  v.finite_residueField_adicCompletionIntegers ℚ
