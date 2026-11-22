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
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Fin.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MathlibExt.Combinatorics.SchurNumbersWanted

open Finset

/-- Every `k`-colouring of `{1, …, N}` has a monochromatic solution to
`x + y = z`, with `x = y` permitted (so these are the Schur numbers, not the
weak Schur numbers). -/
def schurForces (k N : ℕ) : Prop :=
  ∀ c : ℕ → Fin k, ∃ x ∈ Icc 1 N, ∃ y ∈ Icc 1 N, ∃ z ∈ Icc 1 N,
    x + y = z ∧ c x = c y ∧ c y = c z

/-- The Schur number `S(k)`: the largest `N` such that `{1, …, N}` splits into
`k` sum-free parts (OEIS A045652), computed as one less than the least forcing
`N` (OEIS A030126), and pinned to `0` at `k = 0`. -/
noncomputable def schurNumber (k : ℕ) : ℕ :=
  if k < 1 then 0 else sInf {N | schurForces k N} - 1

/-- `S(2) = 4`.

Source: exhaustive check; OEIS A045652; listed in leansolving/SqueezeBench
`SqueezeBench/Problems/Schur/README.md`. -/
public theorem_wanted schurNumber_two : schurNumber 2 = 4

/-- `S(3) = 13`.

Source: exhaustive check; OEIS A045652; listed in SqueezeBench
`SqueezeBench/Problems/Schur/README.md`. -/
public theorem_wanted schurNumber_three : schurNumber 3 = 13

/-- `S(4) = 44`.

Source: S. W. Golomb and L. D. Baumert, *Backtrack programming*, J. ACM 12
(1965), 516–524; OEIS A045652; listed in SqueezeBench
`SqueezeBench/Problems/Schur/README.md`. -/
public theorem_wanted schurNumber_four : schurNumber 4 = 44

/-- `S(5) = 160`.

Source: M. J. H. Heule, *Schur Number Five*, Proc. AAAI 2018, 6598–6606
(arXiv:1711.08076), a DRAT-verified SAT proof; OEIS A045652; listed in
SqueezeBench `SqueezeBench/Problems/Schur/README.md`. -/
public theorem_wanted schurNumber_five : schurNumber 5 = 160

/-- `S(6) ≥ 536`.

Source: H. Fredricksen and M. M. Sweet, *Symmetric sum-free partitions and
lower bounds for Schur numbers*, Electron. J. Combin. 7 (2000), R32; listed in
SqueezeBench `SqueezeBench/Problems/Schur/README.md`. -/
public theorem_wanted le_schurNumber_six : 536 ≤ schurNumber 6

/-- `S(6) ≤ 1836`.

Source: the multicolour Ramsey bound `R₆(3) ≤ 1838` (S. P. Radziszowski,
*Small Ramsey Numbers*, Electron. J. Combin. Dynamic Survey DS1) together with
`S(k) ≤ R_k(3) - 2`; the range `536 ≤ S(6) ≤ 1836` is stated in S. Eliahou and
D. F. Revuelta, *The Schur degree of additive sets*, arXiv:2006.01502; listed
in SqueezeBench `SqueezeBench/Problems/Schur/README.md`. -/
public theorem_wanted schurNumber_six_le : schurNumber 6 ≤ 1836

end MathlibExt.Combinatorics.SchurNumbersWanted
