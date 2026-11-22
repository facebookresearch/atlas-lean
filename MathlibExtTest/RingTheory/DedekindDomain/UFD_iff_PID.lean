/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DedekindDomain.UFD_iff_PID

@[expose] public section

/-- Corollary 3.15 at `ℤ`: `ℤ` is a UFD iff it is a PID. -/
example : UniqueFactorizationMonoid ℤ ↔ IsPrincipalIdealRing ℤ :=
  IsDedekindDomain.uniqueFactorizationMonoid_iff_isPrincipalIdealRing

/-- Corollary 3.15 at `ℤ`: `ℤ` is a PID iff its class group is trivial. -/
example : IsPrincipalIdealRing ℤ ↔ Subsingleton (ClassGroup ℤ) :=
  IsDedekindDomain.isPrincipalIdealRing_iff_subsingleton_classGroup

/-- Corollary 3.15 at `ℤ`: `ℤ` is a UFD iff its class group is trivial. -/
example : UniqueFactorizationMonoid ℤ ↔ Subsingleton (ClassGroup ℤ) :=
  IsDedekindDomain.uniqueFactorizationMonoid_iff_subsingleton_classGroup

/-- The class group of `ℤ` is trivial, via unique factorization. -/
example : Subsingleton (ClassGroup ℤ) :=
  IsDedekindDomain.uniqueFactorizationMonoid_iff_subsingleton_classGroup.mp
    inferInstance

/-- `ℤ` is a PID, via unique factorization and Corollary 3.15. -/
example : IsPrincipalIdealRing ℤ :=
  IsDedekindDomain.uniqueFactorizationMonoid_iff_isPrincipalIdealRing.mp
    inferInstance

/-- `ℤ` is a UFD, via the triviality of its class group and
Corollary 3.15. -/
example : UniqueFactorizationMonoid ℤ :=
  IsDedekindDomain.uniqueFactorizationMonoid_iff_subsingleton_classGroup.mpr
    (IsDedekindDomain.uniqueFactorizationMonoid_iff_subsingleton_classGroup.mp
      inferInstance)

/-- Corollary 3.15 at `ℚ`: the class group of a field is trivial. -/
example : Subsingleton (ClassGroup ℚ) :=
  IsDedekindDomain.uniqueFactorizationMonoid_iff_subsingleton_classGroup.mp
    inferInstance

/-- Corollary 3.15 at `ℚ`: `ℚ` is a PID, via unique factorization. -/
example : IsPrincipalIdealRing ℚ :=
  IsDedekindDomain.uniqueFactorizationMonoid_iff_isPrincipalIdealRing.mp
    inferInstance
