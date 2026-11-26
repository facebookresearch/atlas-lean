/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.GirthFiveExtremalValues

open MathlibExt.Combinatorics.SimpleGraph.GirthFiveExtremalValuesWanted

-- At five vertices the first admissible cycle improves on a tree.
example : girthFiveExtremalNumber 5 = 5 := by
  have h := List.getElem_of_eq (i := 4) girthFiveExtremalNumber_one_to_twenty (by simp)
  rw [List.getElem_map, List.getElem_range] at h
  exact h

-- Check the inclusive upper endpoint of the one-based table.
example : girthFiveExtremalNumber 20 = 41 := by
  have h := List.getElem_of_eq (i := 19) girthFiveExtremalNumber_one_to_twenty (by simp)
  rw [List.getElem_map, List.getElem_range] at h
  exact h
