/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.FallingKBinomialTransform

namespace MetaMathlibExt

@[expose] public section

/-- **Multiple binomial transform.** The binomial transform sends an integer sequence
$(a_i)_{i \ge 0}$ to the sequence $(b_n)_{n \ge 0}$ given by
$b_n = \sum_{i=0}^{n} \binom{n}{i} a_i$. For a natural number $r$, the $r$-fold binomial
transform of $a$ is obtained by applying the binomial transform $r$ times in succession; the
$0$-fold transform of $a$ is $a$ itself.

Sources:

* Jiaqiang Pan, *Multiple Binomial Transforms and Families of Integer Sequences*,
  Journal of Integer Sequences 13 (2010), lines 128–150:
  <https://cs.uwaterloo.ca/journals/JIS/VOL13/Pan/pan8.tex>.
* Jiaqiang Pan, *Some Properties of the Multiple Binomial Transform and the Hankel Transform of
  Shifted Sequences*, Journal of Integer Sequences 14 (2011), lines 104–118:
  <https://cs.uwaterloo.ca/journals/JIS/VOL14/Pan/pan12.tex>.

The archived sources have SHA-256 values
`1d0b3a962f3ebef6a30b664f7979f89bf9e80f8adddad71bfdbeef541daf0791` and
`b48df480b12f77923455a0db85c255217715a73eba7c7ad92ceb5855d434ef26`.

Concept `jis_term_c157679dc9eb88c4ba264101`; source statements
`jis_565fc7c3315ad99b5942cc67` and `jis_a569298bba80b28850af1658`.
-/
public def multipleBinomialTransform : ℕ → (ℕ → ℤ) → ℕ → ℤ
  | 0, a => a
  | n + 1, a => binomialTransform (multipleBinomialTransform n a)

end

end MetaMathlibExt
