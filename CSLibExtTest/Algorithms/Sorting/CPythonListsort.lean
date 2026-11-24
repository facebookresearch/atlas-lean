/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExtTest.Algorithms.Sorting.CPythonListsort.Transcription.MergeAt
import CSLibExtTest.Algorithms.Sorting.CPythonListsort.Correctness.MergeAtCorrectness
import CSLibExtTest.Algorithms.Sorting.CPythonListsort.Correctness.FoundNewRunCorrectness
import CSLibExtTest.Algorithms.Sorting.CPythonListsort.Correctness.MergeForceCollapseCorrectness
import CSLibExtTest.Algorithms.Sorting.CPythonListsort.Correctness.ScanStepCorrectness
import CSLibExtTest.Algorithms.Sorting.CPythonListsort.Correctness.ListSortCorrectness
import CSLibExtTest.Algorithms.Sorting.CPythonListsort.Assembly.GallopCorrectness
import CSLibExtTest.Algorithms.Sorting.CPythonListsort.Assembly.MergeMemorySafety
import CSLibExtTest.Algorithms.Sorting.CPythonListsort.Assembly.PowerSortCostRegression

/-! Regression clients for the CPython listsort model. -/
