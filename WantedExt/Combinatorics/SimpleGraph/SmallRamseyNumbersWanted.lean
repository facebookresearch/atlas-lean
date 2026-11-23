/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Small classical Ramsey numbers

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
the values below are taken from the "Known values" tables of
leansolving/SqueezeBench at commit e2e19eef093a77882da57f348def029533ec2d5e
(`SqueezeBench/Problems/Ramsey/README.md` and
`SqueezeBench/Problems/Ramsey3/README.md`; authors P. Manrique, H. Xia,
S. Szeider), distributed under the Apache License, Version 2.0. SqueezeBench
ships no `NOTICE` file. Changes made: SqueezeBench marks these values as
reporting only and states no theorems about them; here each published value
or bound becomes a Batteries `theorem_wanted` about the repository's canonical
`SimpleGraph.graphRamsey` instead of SqueezeBench's `Ramsey.f` and
`Ramsey3.f`. Values already proved in `MathlibExt` (`R(3,3) = 6`,
`R(3,4) = 9`) and the trivial values `R(2,2) = 2`, `R(3,2) = 3` are omitted.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.Ramsey

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.SmallRamseyNumbersWanted

open _root_.SimpleGraph

/-!
`SimpleGraph.graphRamsey s t` is the least `N` such that every graph on `Fin N`
contains `K_s` or its complement contains `K_t`. SqueezeBench's `Ramsey.f n`
(diagonal) and `Ramsey3.f k` (`s = 3`) are the same quantity for `n, k ≥ 2`:
its `Forces N s t` asks for an `s`-clique in `G` or a `t`-clique in `Gᶜ`, which
is containment of `K_s` in `G` or of `K_t` in `Gᶜ`.

`R(3,3) = 6` is `SimpleGraph.graphRamsey_three_three` and `R(3,4) = 9` is
`SimpleGraph.graphRamsey_three_four` in `MathlibExt`. The open conjecture
`R(5,5) ≤ 43` is `OpenConjectures.Combinatorics.RamseyFiveFiveExactValue`.
-/

/-- **The value of $R(4, 4)$.** The classical Ramsey number $R(4, 4)$ equals $18$.

Source: R. E. Greenwood and A. M. Gleason, *Combinatorial relations and
chromatic graphs*, Canad. J. Math. 7 (1955), 1–7; S. P. Radziszowski, *Small
Ramsey Numbers*, Electron. J. Combin. Dynamic Survey DS1;
listed in leansolving/SqueezeBench `SqueezeBench/Problems/Ramsey/README.md`. -/
public theorem_wanted graphRamsey_four_four : graphRamsey 4 4 = 18

/-- **Exoo's lower bound for $R(5, 5)$.** The classical Ramsey number $R(5, 5)$ is at
least $43$.

Thus some simple graph on $42$ vertices contains no $K_5$ and no independent set of size $5$.

Source: G. Exoo, *A lower bound for R(5,5)*, J. Graph Theory 13 (1989),
97–98; Radziszowski, DS1; listed in SqueezeBench
`SqueezeBench/Problems/Ramsey/README.md`. -/
public theorem_wanted forty_three_le_graphRamsey_five_five : 43 ≤ graphRamsey 5 5

/-- **The Angeltveit–McKay upper bound for $R(5, 5)$.** The classical Ramsey number
$R(5, 5)$ is at most $46$.

Source: V. Angeltveit and B. D. McKay, *R(5,5) ≤ 46*, arXiv:2409.15709 (2024);
listed in SqueezeBench `SqueezeBench/Problems/Ramsey/README.md`. -/
public theorem_wanted graphRamsey_five_five_le_forty_six : graphRamsey 5 5 ≤ 46

/-- **The value of $R(3, 5)$.** The classical Ramsey number $R(3, 5)$ equals $14$.

Source: Greenwood and Gleason (1955), op. cit.; Radziszowski, DS1;
OEIS A000791; listed in SqueezeBench `SqueezeBench/Problems/Ramsey3/README.md`. -/
public theorem_wanted graphRamsey_three_five : graphRamsey 3 5 = 14

/-- **The value of $R(3, 6)$.** The classical Ramsey number $R(3, 6)$ equals $18$.

Source: G. Kéry, *On a theorem of Ramsey*, Mat. Lapok 15 (1964), 204–224
(upper bound), with the lower bound from Kalbfleisch (1966); Radziszowski,
DS1; OEIS A000791; listed in SqueezeBench
`SqueezeBench/Problems/Ramsey3/README.md`. -/
public theorem_wanted graphRamsey_three_six : graphRamsey 3 6 = 18

/-- **The value of $R(3, 7)$.** The classical Ramsey number $R(3, 7)$ equals $23$.

Source: J. G. Kalbfleisch, *Chromatic graphs and Ramsey's theorem*, Ph.D.
thesis, University of Waterloo (1966) (lower bound); J. E. Graver and
J. Yackel, *Some graph theoretic results associated with Ramsey's theorem*,
J. Combin. Theory 4 (1968), 125–175 (upper bound); Radziszowski, DS1;
OEIS A000791; listed in SqueezeBench `SqueezeBench/Problems/Ramsey3/README.md`. -/
public theorem_wanted graphRamsey_three_seven : graphRamsey 3 7 = 23

/-- **The value of $R(3, 8)$.** The classical Ramsey number $R(3, 8)$ equals $28$.

Source: C. Grinstead and S. Roberts, *On the Ramsey numbers R(3,8) and
R(3,9)*, J. Combin. Theory Ser. B 33 (1982), 27–51 (lower bound); B. D. McKay
and Zhang Ke Min, *The value of the Ramsey number R(3,8)*, J. Graph Theory 16
(1992), 99–105 (upper bound); Radziszowski, DS1; OEIS A000791; listed in
SqueezeBench `SqueezeBench/Problems/Ramsey3/README.md`. -/
public theorem_wanted graphRamsey_three_eight : graphRamsey 3 8 = 28

/-- **The value of $R(3, 9)$.** The classical Ramsey number $R(3, 9)$ equals $36$.

Source: Kalbfleisch (1966), op. cit. (lower bound); Grinstead and Roberts
(1982), op. cit. (upper bound); Radziszowski, DS1; OEIS A000791; listed in
SqueezeBench `SqueezeBench/Problems/Ramsey3/README.md`. -/
public theorem_wanted graphRamsey_three_nine : graphRamsey 3 9 = 36

/-- **Exoo's lower bound for $R(3, 10)$.** The classical Ramsey number $R(3, 10)$ is at
least $40$.

Source: G. Exoo, *On two classical Ramsey numbers of the form R(3,n)*, SIAM
J. Discrete Math. 2 (1989), 488–490; Radziszowski, DS1; listed in
SqueezeBench `SqueezeBench/Problems/Ramsey3/README.md`. -/
public theorem_wanted forty_le_graphRamsey_three_ten : 40 ≤ graphRamsey 3 10

/-- **Angeltveit's upper bound for $R(3, 10)$.** The classical Ramsey number $R(3, 10)$
is at most $41$.

Source: V. Angeltveit, *R(3,10) ≤ 41*, arXiv:2401.00392 (2024); Radziszowski,
DS1; listed in SqueezeBench `SqueezeBench/Problems/Ramsey3/README.md`. -/
public theorem_wanted graphRamsey_three_ten_le_forty_one : graphRamsey 3 10 ≤ 41

end MathlibExt.Combinatorics.SimpleGraph.SmallRamseyNumbersWanted
