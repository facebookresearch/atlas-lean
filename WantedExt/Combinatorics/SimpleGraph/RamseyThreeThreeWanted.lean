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

import Batteries.Util.ProofWanted
import MathlibExt.Combinatorics.SimpleGraph.Ramsey

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SimpleGraph

/-- **The triangle–triangle Ramsey number is six.** Every graph on six vertices contains a
triangle or has a triangle in its complement. Five vertices do not suffice, as the cycle on
five vertices and its complement are both triangle-free. This is the exceptional triangle case
of the cycle–clique Ramsey formula, since the cycle on three vertices is the complete graph.

Source: [cycle–clique Ramsey numbers, exceptional $(3,3)$ case](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CycleCliqueRamsey.lean#L23-L27). -/
public theorem_wanted graphRamsey_three_three : graphRamsey 3 3 = 6

end SimpleGraph
