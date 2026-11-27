/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.WirsingConstantUpperBound

open MathlibExt.Analysis.WirsingConstant
open MathlibExt.Analysis.WirsingConstantWanted

-- The bound excludes 1/3 in the holomorphic model.
example : wirsingConstant < 1 / 3 :=
  mayerRoepstorffUpperBound_wanted.trans_lt (by norm_num)

-- Each holomorphic eigenvalue other than one has modulus below 1/3.
example {l : ℂ} (hl : IsHolomorphicEigenvalue l) (hl₁ : l ≠ 1) : ‖l‖ < 1 / 3 :=
  (norm_le_of_isHolomorphicEigenvalue hl hl₁).trans_lt (by norm_num)

-- The holomorphic model has neither 1/3 nor -1/3 as an eigenvalue (the docstring of
-- `IsEigenvalue` notes that the continuous model has the eigenvalue 1/3).
example : ¬ IsHolomorphicEigenvalue (1 / 3) := fun h =>
  (norm_le_of_isHolomorphicEigenvalue h (by norm_num)).not_gt (by norm_num)

example : ¬ IsHolomorphicEigenvalue (-1 / 3) := fun h =>
  (norm_le_of_isHolomorphicEigenvalue h (by norm_num)).not_gt (by norm_num [norm_neg])

-- The set whose supremum defines the Wirsing constant is bounded above, so the Wirsing constant
-- bounds the modulus of every holomorphic eigenvalue other than one.
example {l : ℂ} (hl : IsHolomorphicEigenvalue l) (hl₁ : l ≠ 1) : ‖l‖ ≤ wirsingConstant :=
  le_csSup bddAbove_norm_isHolomorphicEigenvalue ⟨l, hl, hl₁, rfl⟩
