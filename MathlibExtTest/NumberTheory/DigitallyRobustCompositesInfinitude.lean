/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DigitallyRobustCompositesInfinitude

open MetaMathlibExt

example (bound : ℕ) : ∃ n > bound, IsDigitallyRobustComposite n := by
  obtain ⟨n, hn, hbound⟩ := infinitelyMany_digitallyRobustComposites.exists_gt bound
  exact ⟨n, hbound, hn⟩
