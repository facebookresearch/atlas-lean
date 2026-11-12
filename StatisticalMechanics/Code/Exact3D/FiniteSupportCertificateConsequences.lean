/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.TailSummabilitySkeleton

open scoped BigOperators









namespace StatMech
namespace Exact3D

namespace TailSummability
namespace FiniteSupportCertificate

variable {α : Type*} [DecidableEq α]
variable (C : FiniteSupportCertificate α)




theorem finitePrefix_eq_support_of_support_subset
    (hsupport_subset_prefix : C.support ⊆ C.finitePrefix) :
    C.finitePrefix = C.support :=
  Finset.Subset.antisymm C.finitePrefix_subset_support hsupport_subset_prefix



theorem tailSupport_eq_empty_of_support_subset
    (hsupport_subset_prefix : C.support ⊆ C.finitePrefix) :
    C.tailSupport = ∅ := by
  ext a
  constructor
  · intro ha
    have htail : a ∈ C.support ∧ a ∉ C.finitePrefix := by
      simpa [tailSupport] using ha
    exact False.elim <| htail.2 (hsupport_subset_prefix htail.1)
  · intro ha
    simp at ha



theorem support_sum_eq_finitePrefix_sum_of_support_subset
    (hsupport_subset_prefix : C.support ⊆ C.finitePrefix) :
    (∑ a ∈ C.support, C.weight a) =
      ∑ a ∈ C.finitePrefix, C.weight a := by
  simp [C.finitePrefix_eq_support_of_support_subset hsupport_subset_prefix]



theorem tsum_eq_finitePrefix_sum_of_support_subset
    (hsupport_subset_prefix : C.support ⊆ C.finitePrefix) :
    (∑' a, C.weight a) = ∑ a ∈ C.finitePrefix, C.weight a := by
  simpa [C.finitePrefix_eq_support_of_support_subset hsupport_subset_prefix]
    using C.tsum_eq_support_sum



theorem tail_sum_eq_zero_of_support_subset
    (hsupport_subset_prefix : C.support ⊆ C.finitePrefix) :
    (∑ a ∈ C.tailSupport, C.weight a) = 0 := by
  simp [C.tailSupport_eq_empty_of_support_subset hsupport_subset_prefix]



theorem envelope_tail_sum_eq_zero_of_support_subset
    (hsupport_subset_prefix : C.support ⊆ C.finitePrefix) :
    (∑ a ∈ C.tailSupport, C.envelope a) = 0 := by
  simp [C.tailSupport_eq_empty_of_support_subset hsupport_subset_prefix]

end FiniteSupportCertificate
end TailSummability

end Exact3D
end StatMech
