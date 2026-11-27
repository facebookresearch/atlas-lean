/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Optimal Golomb rulers

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
the imported definitions `golombRulerLengths` and `optimalGolombLength` are taken from
leansolving/SqueezeBench at commit e2e19eef093a77882da57f348def029533ec2d5e,
`SqueezeBench/Problems/Golomb/Def.lean` (`RulerLengths` and `f`; authors
P. Manrique, H. Xia, S. Szeider), and the values from the "Known values"
table of `SqueezeBench/Problems/Golomb/README.md`, distributed under the
Apache License, Version 2.0. SqueezeBench ships no `NOTICE` file. Changes
made: renamed `RulerLengths`/`f` to `golombRulerLengths`/`optimalGolombLength`,
replaced SqueezeBench's local `IsSidon` on `Finset ℕ` by the repository's
`Set.IsSidon` (the same condition on the coerced set), inlined `nMin = 1`,
dropped the helper lemmas, and turned the README values (which SqueezeBench
marks as reporting only) into Batteries `theorem_wanted` declarations. The
trivial values for one and two marks are omitted.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.GolombRulers

@[expose] public section

namespace MathlibExt.Combinatorics.GolombRulersWanted

/-- **Optimal 27-mark Golomb ruler.** The optimal Golomb ruler length with $27$ marks is $553$.

Source: distributed.net OGR-27 exhaustive search, completed 2014; OEIS A003022;
listed in SqueezeBench `SqueezeBench/Problems/Golomb/README.md`. -/
public theorem_wanted optimalGolombLength_twentySeven : optimalGolombLength 27 = 553

/-- **Optimal 28-mark Golomb ruler.** The optimal Golomb ruler length with $28$ marks is $585$.

Source: distributed.net OGR-28 exhaustive search, completed 2022; OEIS A003022;
listed in SqueezeBench `SqueezeBench/Problems/Golomb/README.md`. -/
public theorem_wanted optimalGolombLength_twentyEight : optimalGolombLength 28 = 585

end MathlibExt.Combinatorics.GolombRulersWanted
