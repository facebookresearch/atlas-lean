/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.AdicCompleteDomain
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-- A finite domain algebra over `ℤ_[p]` is local; here the algebra is `ℤ_[p]` itself. -/
example (p : ℕ) [Fact p.Prime] : IsLocalRing ℤ_[p] :=
  IsLocalRing.of_isDomain_of_module_finite_of_isAdicComplete (R := ℤ_[p]) (S := ℤ_[p])
