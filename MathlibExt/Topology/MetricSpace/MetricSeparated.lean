/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Topology.EMetricSpace.Defs

@[expose] public section

open EMetric Set
open scoped ENNReal

noncomputable section

namespace Metric
variable {X : Type*} [PseudoEMetricSpace X]

/-!
### Metric-separated sets

In this section we define the predicate `Metric.IsSeparated'` for `ε`-separated sets.
-/

/-- **Non-strictly separated sets.** Let $X$ be a pseudo-extended metric space (distances lie in
$[0, \infty]$ and distinct points may be at distance $0$), write $d$ for its extended distance,
and let $\varepsilon \in [0, \infty]$. A set $s \subseteq X$ is $\varepsilon$-separated if
$\varepsilon \le d(x, y)$ for all distinct points $x, y \in s$. -/
def IsSeparated' (ε : ℝ≥0∞) (s : Set X) : Prop := s.Pairwise (ε ≤ edist · ·)

end Metric
