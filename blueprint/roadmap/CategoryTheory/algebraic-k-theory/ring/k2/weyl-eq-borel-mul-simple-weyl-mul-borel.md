# Stable Steinberg Simple Weyl Generation

Adjacent simple-Weyl generation modulo the finite Borel: for bounded
distinct `i, j < n` and `u : Fˣ`, `weyl i j u = b₁ * W * b₂` with Borel
`b₁, b₂` and `W` an explicit finite product of adjacent unit-one simple Weyl
lifts `weyl k (k + 1) 1` (`k + 1 < n`), the standard palindrome realizing
transposition `(i j)` of length `2 * |j - i| - 1`.
Purpose: one-file generation packet feeding the Lemma-25 word induction; the
conclusion directly supplies Borel witnesses for downstream iteration.
The `i < j` branch strips the unit once (`weyl u = torus u * weyl 1`) and
applies the peel induction; the `j < i` branch reduces by `weyl_swap` to the
same palindrome for `(j i) = (i j)`. Characteristic-two safe.
Nonclaims: no arbitrary finite-Weyl word factorization, no Lemma-25
iteration, no full Bruhat existence, no Matsumoto theorem, no target kernel
containment, no quotient injectivity, and no universal central extension.
