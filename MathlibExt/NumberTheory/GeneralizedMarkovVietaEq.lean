/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedMarkovCharacteristic
public import Mathlib.Tactic.LinearCombination

/-!
# Vieta jumping identities for generalized Markov triples

A generalized Markov triple satisfies two integer identities expressing the
quadratic forms in two of its entries as a multiple of the third entry.
-/

namespace MetaMathlibExt

/-- **Vieta jumping identities for generalized Markov triples.** If $(a, b, c)$ is a
$k$-generalized Markov triple, then, as integers,
$a^2 + kab + b^2 = c\,((3 + 3k)ab - c - k(a + b))$ and
$b^2 + kbc + c^2 = a\,((3 + 3k)bc - a - k(b + c))$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2 (display after
Corollary 2.2). -/
public theorem IsGenMarkovTriple.vieta_eq {k a b c : ℕ} (h : IsGenMarkovTriple k a b c) :
    ((a : ℤ) ^ 2 + k * a * b + b ^ 2 = c * ((3 + 3 * k) * a * b - c - k * (a + b))) ∧
      ((b : ℤ) ^ 2 + k * b * c + c ^ 2 = a * ((3 + 3 * k) * b * c - a - k * (b + c))) := by
  have hZ : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 +
      (k : ℤ) * ((b : ℤ) * c + (c : ℤ) * a + (a : ℤ) * b) =
      (3 + 3 * (k : ℤ)) * a * b * c := by
    exact_mod_cast h.2.2.2
  constructor <;> linear_combination hZ

end MetaMathlibExt
