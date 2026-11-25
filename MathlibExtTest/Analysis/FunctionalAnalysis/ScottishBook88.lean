/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook88

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook88Wanted.Tests

open MathlibExt.Analysis.FunctionalAnalysis.ScottishBook88Wanted

-- The proved theorem applies: the Scottish Book Problem 88 claim is false.
example : ¬ ScottishBookProblem88Claim := mazur88_refuted

-- Any proof of the claim is contradictory.
example (h : ScottishBookProblem88Claim) : False := mazur88_refuted h

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook88Wanted.Tests
