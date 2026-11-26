/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.VonNeumannDoubleCommutant
import Mathlib.Analysis.VonNeumannAlgebra.Basic

open MathlibExt.Analysis.VonNeumannDoubleCommutantWanted.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- A bundled von Neumann algebra is weakly closed in its given representation.
example (M : VonNeumannAlgebra H) :
    IsClosed (ContinuousLinearMapWOT.ofCLM '' (M : Set (H →L[ℂ] H))) :=
  ((vonNeumann_doubleCommutant_tfae M.toStarSubalgebra).out 1 2).mp M.centralizer_centralizer

-- Conversely, strong closedness provides the field needed to bundle a von Neumann algebra.
example (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hS : IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
      (S : Set (H →L[ℂ] H)))) :
    ∃ M : VonNeumannAlgebra H, M.toStarSubalgebra = S :=
  ⟨⟨S, ((vonNeumann_doubleCommutant_tfae (S := S)).out 3 1).mp hS⟩, rfl⟩
