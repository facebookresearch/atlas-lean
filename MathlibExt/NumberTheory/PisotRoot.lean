/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PisotNumber

namespace MetaMathlibExt

@[expose] public section

/-!
# Unique Pisot roots

Source: M. Panju, *Beta expansions for regular Pisot numbers*, Journal of Integer Sequences
14 (2011), Article 11.6.4,
[`panju2.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL14/Panju/panju2.tex).
-/

/-- **Unique Pisot root of a polynomial.** Let $P$ be a polynomial with real coefficients and $r$ a
real number. Then $r$ is the unique Pisot root of $P$ when $r$ is a Pisot number with $P(r) = 0$
and every Pisot number $s$ with $P(s) = 0$ equals $r$. -/
public def IsUniquePisotRoot (P : Polynomial ℝ) (r : ℝ) : Prop :=
  IsPisotNumber r ∧ P.IsRoot r ∧
    ∀ s, IsPisotNumber s → P.IsRoot s → s = r

end

end MetaMathlibExt
