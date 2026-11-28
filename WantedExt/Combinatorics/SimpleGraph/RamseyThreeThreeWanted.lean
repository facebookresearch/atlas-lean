/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`lean/ComparatorChallenges/CycleCliqueRamsey.lean` (openai/math,
https://github.com/openai/math), revision `3344da59991ed94f9ba711217b29c1d760badfa6`.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source file and the applicable license files name no copyright holder or authors.
Authors: OpenAI (project attribution in lean/formalization.yaml).
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.RamseyThreeFive

set_option autoImplicit false
set_option relaxedAutoImplicit false
