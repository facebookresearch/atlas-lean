/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Cole's paradox: an annual with `b + 1` offspring matches an immortal perennial with `b`

Cole (1954) compares two life histories under discrete annual breeding, maturity at age one,
and no mortality at any age. A semelparous annual leaving `B` offspring has growth factor
`λ = B`, so `r = ln B`. An immortal iteroparous perennial leaving `b` offspring every year
satisfies the discrete Euler–Lotka equation `∑_{x ≥ 1} b λ^{-x} = 1`, whose only positive
solution is `λ = b + 1`, so `r = ln (b + 1)` (Cole's eq. (23)). Hence the annual matches the
perennial exactly when `B = b + 1`: one extra offspring per year compensates for immortality.
Cole calls this setting biologically unattainable; with juvenile or adult mortality the
equivalence changes, which is outside Cole's statement.

Sources: L. C. Cole, "The population consequences of life history phenomena", Q. Rev. Biol.
29 (1954) 103–137, pp. 117–119, eqs. (21), (23), (24).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace WantedExt.Biology.Ecology.ColeParadoxWanted

/-- **Growth factor of the immortal perennial** (Cole 1954, eq. (23)). For `b > 0` offspring
per year and `λ > 0`, the discrete Euler–Lotka equation `∑_{x ≥ 1} b λ^{-x} = 1` holds (as a
convergent series) if and only if `λ = b + 1`.

Source: Cole (1954), p. 118, eq. (23). -/
public theorem_wanted perennial_hasSum_iff {b lam : ℝ} (hb : 0 < b) (hlam : 0 < lam) :
    HasSum (fun x : ℕ => b * lam⁻¹ ^ (x + 1)) 1 ↔ lam = b + 1

/-- **Cole's paradox** (Cole 1954, pp. 117–118). Let the annual have growth factor `B > 0` and
the immortal perennial with `b > 0` offspring per year have growth factor `λ > 0` solving
`∑_{x ≥ 1} b λ^{-x} = 1`. Then the two intrinsic rates agree, `ln B = ln λ`, if and only if
`B = b + 1`.

Source: Cole (1954), pp. 117–118, eqs. (21), (23). -/
public theorem_wanted log_annual_eq_log_perennial_iff {B b lam : ℝ} (hB : 0 < B) (hb : 0 < b)
    (hlam : 0 < lam) (hper : HasSum (fun x : ℕ => b * lam⁻¹ ^ (x + 1)) 1) :
    Real.log B = Real.log lam ↔ B = b + 1

end WantedExt.Biology.Ecology.ColeParadoxWanted
