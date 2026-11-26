/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Ecology.ZeroDeterminantStrategyDotProductEqDivPdDet

/-!
# Tests for the Press–Dyson determinant lemma

The determinant lemma determines each stationary probability and implies uniqueness of a
stationary distribution when the constant-one determinant is nonzero.

Sources: W. H. Press and F. J. Dyson, "Iterated Prisoner's Dilemma contains strategies that
dominate any evolutionary opponent", Proc. Natl. Acad. Sci. USA 109 (2012) 10409–10413,
"Zero-determinant strategies", eqs. (1)–(7), and "X unilaterally sets Y's score", eqs. (8)–(10).
-/

namespace DomainsTest.Biology.Ecology.ZeroDeterminantStrategyDotProductEqDivPdDet

open Matrix WantedExt.Biology.Ecology.ZeroDeterminantStrategyWanted

example {p q : Fin 4 → ℝ} (hp : IsStrategy p) (hq : IsStrategy q)
    {v : Fin 4 → ℝ} (hv : IsStationary (markovMatrix p q) v)
    (hD : pdDet p q 1 ≠ 0) (i : Fin 4) :
    v i = pdDet p q (Pi.single i 1) / pdDet p q 1 := by
  simpa using dotProduct_eq_div_pdDet hp hq hv hD (Pi.single i 1)

example {p q : Fin 4 → ℝ} (hp : IsStrategy p) (hq : IsStrategy q)
    {v w : Fin 4 → ℝ} (hv : IsStationary (markovMatrix p q) v)
    (hw : IsStationary (markovMatrix p q) w) (hD : pdDet p q 1 ≠ 0) : v = w := by
  ext i
  have hv' := dotProduct_eq_div_pdDet hp hq hv hD (Pi.single i 1)
  have hw' := dotProduct_eq_div_pdDet hp hq hw hD (Pi.single i 1)
  simpa using hv'.trans hw'.symm

end DomainsTest.Biology.Ecology.ZeroDeterminantStrategyDotProductEqDivPdDet
