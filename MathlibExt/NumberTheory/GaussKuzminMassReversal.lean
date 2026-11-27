/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GaussKuzminSymmetryStablePlusNontrivialSymmetry

/-!
# Reversal symmetry of the Gauss–Kuzmin mass

The proof reuses the equality in `MetaMathlibExt.gaussKuzminMass_eq_abs_logb`.

## References

* Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
  Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
  Proposition 1.3 and Lemma 2.5.
-/

namespace MetaMathlibExt

/-- **Reversal symmetry of the Gauss–Kuzmin mass.** For every string $a$ of positive integers,
$P_{GK}(\overleftarrow{a}) = P_{GK}(a)$, where $P_{GK}$ is the Gauss–Kuzmin mass and
$\overleftarrow{a}$ is the reverse of $a$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Proposition 1.3 (`integers-2025-A89-prop-1-3`), equations (1.8) and (1.9). -/
public theorem gaussKuzminMass_reverse (a : List ℕ) (ha : (∀ x ∈ a, 0 < x)) :
    gaussKuzminMass a.reverse = gaussKuzminMass a :=
  (gaussKuzminMass_eq_abs_logb a ha).1.symm

end MetaMathlibExt
