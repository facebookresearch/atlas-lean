/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Grading.Module

/-!
# Compatibility import for the coefficient self-module grading

The original `Grading.Module` owner provides `selfGenerator`, `self`, and
both application lemmas. This module publicly re-exports that owner for
clients using the focused `Grading.Module.Self` import.
-/
