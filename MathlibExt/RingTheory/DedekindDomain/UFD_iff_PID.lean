/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# A Dedekind domain is a UFD iff it is a PID iff its class group is trivial

This is Corollary 3.15 of ATLAS `NumberTheoryI`, Section 3.2. Mathlib
has the two one-way ingredients separately — a Dedekind domain with
unique factorization is a principal ideal ring
(`IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid`),
a principal ideal ring has unique factorization
(`PrincipalIdealRing.to_uniqueFactorizationMonoid`, an instance), and
the class number is `1` iff the ring is a principal ideal ring
(`card_classGroup_eq_one_iff`) — but not the packaged three-way
equivalence stated here.

## Main results

* `IsDedekindDomain.uniqueFactorizationMonoid_iff_isPrincipalIdealRing`:
  a Dedekind domain is a UFD iff it is a PID.
* `IsDedekindDomain.isPrincipalIdealRing_iff_subsingleton_classGroup`:
  a Dedekind domain is a PID iff its class group is trivial.
* `IsDedekindDomain.uniqueFactorizationMonoid_iff_subsingleton_classGroup`:
  a Dedekind domain is a UFD iff its class group is trivial.
-/

@[expose] public section

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- **Dedekind domains: UFD iff PID.** A Dedekind domain $R$ is a unique factorization domain if
and only if it is a principal ideal domain.

Source: ATLAS NumberTheoryI, Section 3.2, Corollary 3.15 (first equivalence). -/
theorem uniqueFactorizationMonoid_iff_isPrincipalIdealRing :
    UniqueFactorizationMonoid R ↔ IsPrincipalIdealRing R := by
  constructor
  · intro h
    have := h
    exact IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid R
  · intro h
    have := h
    infer_instance

/-- **Dedekind domains: PID iff trivial class group.** A Dedekind domain $R$ is a principal ideal
domain if and only if its ideal class group is trivial.

Source: ATLAS NumberTheoryI, Section 3.2, Corollary 3.15 (second equivalence). -/
theorem isPrincipalIdealRing_iff_subsingleton_classGroup :
    IsPrincipalIdealRing R ↔ Subsingleton (ClassGroup R) := by
  constructor
  · intro h
    have := h
    rw [← Fintype.card_le_one_iff_subsingleton]
    exact card_classGroup_eq_one.le
  · intro h
    have := h
    let : Fintype (ClassGroup R) := Fintype.ofSubsingleton 1
    rw [← card_classGroup_eq_one_iff]
    exact Fintype.card_ofSubsingleton 1

/-- **Dedekind domains: UFD iff trivial class group.** A Dedekind domain $R$ is a unique
factorization domain if and only if its ideal class group is trivial.

Source: ATLAS NumberTheoryI, Section 3.2, Corollary 3.15 (combined). -/
theorem uniqueFactorizationMonoid_iff_subsingleton_classGroup :
    UniqueFactorizationMonoid R ↔ Subsingleton (ClassGroup R) :=
  uniqueFactorizationMonoid_iff_isPrincipalIdealRing.trans
    isPrincipalIdealRing_iff_subsingleton_classGroup

end IsDedekindDomain
