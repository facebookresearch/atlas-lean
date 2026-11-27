/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryDivisor
import all MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryTriperfect

/-!
# Prime factors at least `7` of biunitary divisor sums

The proof reuses the biunitary prime-power factorization and the primitive prime divisor
argument. For `u = g / 2 + 1`, the factor `p ^ u + 1` supplies a prime congruent to `1`
modulo `2 * u`, and `g ≥ 4` gives `u ≥ 3`.

## References

* Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
  Journal of Integer Sequences 28 (2025), Article 25.4.5, pp. 1–15, Lemma 8 (II),
  using equation (2) and Lemma 5.
* Charles R. Wall, *Bi-unitary perfect numbers*, Proceedings of the American Mathematical
  Society 33 (1972), 39–42, for the prime-power formula recalled in Yamada's Section 2.
* A. S. Bang, *Taltheoretiske Undersøgelser*, Tidsskrift for Mathematik, 5th series,
  4 (1886), 70–80 and 130–137, for the primitive divisor result in Yamada's Lemma 4.
  Yamada also credits the rediscoveries and extensions by K. Zsigmondy,
  *Zur Theorie der Potenzreste*, Monatshefte für Mathematik und Physik 3 (1892), 265–284;
  L. E. Dickson, *On the Cyclotomic Function*, American Mathematical Monthly 12 (1905), 86–89;
  and H.-J. Kanold, *Sätze über Kreisteilungspolynome und ihre Anwendungen auf einige
  zahlentheoretische Probleme, I*, Journal für die reine und angewandte Mathematik
  187 (1950), 169–182. See also Harold N. Shapiro, *Introduction to the Theory of Numbers*,
  John Wiley and Sons (1983), Theorem 6.4A.1.
-/

namespace MetaMathlibExt

/-- **Prime factors at least $7$ of biunitary divisor sums of odd prime powers.** For every odd
prime $p$ and every integer $g \ge 4$, the biunitary divisor sum $\sigma^{**}(p^g)$ has a prime
factor $q \ge 7$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 8 (II) (`jis-2025-25.4.5-lem-8`). -/
public theorem exists_prime_ge_seven_dvd_sigmaBiunitary_prime_pow (p g : ℕ)
    (hp : p.Prime) (hodd : p ≠ 2) (hg : 4 ≤ g) :
    ∃ q, q.Prime ∧ q ∣ sigmaBiunitary (p ^ g) ∧ 7 ≤ q :=
  exists_prime_ge_seven_dvd_sigmaBiunitary_prime_pow_aux (p := p) (g := g) hp hodd hg

end MetaMathlibExt
