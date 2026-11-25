/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CarmichaelIndex

open MetaMathlibExt

-- At zero the conclusion would fail because natural subtraction truncates.
example : carmichaelIndex 0 = 0 - 1 := by decide

-- Every residue modulo 2 is fixed. Modulo 6 exactly two residues fail.
example : carmichaelIndex 2 = 2 := by decide
example : carmichaelIndex 6 = 6 - 2 := by decide

-- At an odd composite modulus there can also be failures.
example : carmichaelIndex 9 = 3 := by decide
