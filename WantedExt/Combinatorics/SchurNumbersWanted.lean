/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Schur numbers

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
the definitions `schurForces` and `schurNumber` are taken from
leansolving/SqueezeBench at commit e2e19eef093a77882da57f348def029533ec2d5e,
`SqueezeBench/Problems/Schur/Def.lean` (`Forces` and `f`; authors P. Manrique,
H. Xia, S. Szeider), and the values from the "Known values" table of
`SqueezeBench/Problems/Schur/README.md`, distributed under the Apache
License, Version 2.0. SqueezeBench ships no `NOTICE` file. Changes made:
renamed `Forces`/`f` to `schurForces`/`schurNumber`, inlined `nMin = 1`,
dropped the helper lemmas, and turned the README values (which SqueezeBench
marks as reporting only) into Batteries `theorem_wanted` declarations. The
trivial value `S(1) = 1` is omitted.

This module imports `MathlibExt.Combinatorics.SchurNumbers`, which proves the
second and third Schur numbers and the lower bound for the sixth Schur number.
The definitions `schurForces` and `schurNumber` moved there with the lower
bound, with the same names, statements and docstrings. It also imports
`MathlibExt.Combinatorics.SchurNumberFour`, which proves the fourth Schur number;
that statement moved there with the same name, statement and docstring.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SchurNumbers
public import MathlibExt.Combinatorics.SchurNumberFour

@[expose] public section

namespace MathlibExt.Combinatorics.SchurNumbersWanted

/-- **The fifth Schur number.** The Schur number $S(5)$ equals $160$.

Source: M. J. H. Heule, *Schur Number Five*, Proc. AAAI 2018, 6598–6606
(arXiv:1711.08076), a DRAT-verified SAT proof; OEIS A045652; listed in
SqueezeBench `SqueezeBench/Problems/Schur/README.md`. -/
public theorem_wanted schurNumber_five : schurNumber 5 = 160

/-- **Upper bound for the sixth Schur number.** The Schur number $S(6)$ is at most $1836$.

Source: the multicolour Ramsey bound `R₆(3) ≤ 1838` (S. P. Radziszowski,
*Small Ramsey Numbers*, Electron. J. Combin. Dynamic Survey DS1) together with
`S(k) ≤ R_k(3) - 2`; the range `536 ≤ S(6) ≤ 1836` is stated in S. Eliahou and
D. F. Revuelta, *The Schur degree of additive sets*, arXiv:2006.01502; listed
in SqueezeBench `SqueezeBench/Problems/Schur/README.md`. -/
public theorem_wanted schurNumber_six_le : schurNumber 6 ≤ 1836

end MathlibExt.Combinatorics.SchurNumbersWanted
