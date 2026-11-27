/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.SetPartitionNonSymmetricPeakCoefficients
public import MathlibExt.Combinatorics.Enumerative.SetPartitionNonSymmetricPeaks
public import MathlibExt.Combinatorics.Enumerative.SetPartitionSymmetricPeaks
public import MathlibExt.Combinatorics.Enumerative.SetPartitionSymmetricPeaksCoefficients

/-!
# Symmetric and non-symmetric peaks in set partitions

Statements from Walaa Asakly and Noor Kezil, *Counting Symmetric and Non-Symmetric Peaks in a Set
Partition*, INTEGERS 26 (2026), Article A8.

A partition of `[1, n]` with exactly `k` blocks is encoded by its canonical sequential form, a
surjective restricted-growth string `w : Fin n → Fin k` (`IsSurjectiveRestrictedGrowthString`;
block `i + 1` of the paper is the label `i`). A peak is a consecutive triple `a < b > c`; it is
symmetric if `a = c` (`symmetricPeakCount`, shared with the authors' compositions paper) and
non-symmetric otherwise; both are counted on the word `List.ofFn w` of labels (the shift of
labels does not change peaks). `S_{n,k}` is `Nat.stirlingSecond n k`.
-/

open Finset PowerSeries

namespace MetaMathlibExt

@[expose] public section

end

end MetaMathlibExt
