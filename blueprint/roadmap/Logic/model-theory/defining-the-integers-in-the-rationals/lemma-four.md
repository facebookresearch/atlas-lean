# Robinson's Lemma 4

Let `p` and `q` be odd primes with `p ≡ 1 (mod 4)` and
`(q / p) = -1`, and let `M` be a rational number. Then `2 + p q M ^ 2 + p Z ^ 2 = X ^ 2 + q Y ^ 2`
has a solution in rational numbers `X, Y, Z` if and only if the denominator of `M` in lowest terms
is prime to `p` and to `q`. (That `p` is odd follows from `p ≡ 1 (mod 4)`.)

J. Robinson, "Definability and decision problems in arithmetic", *J. Symbolic Logic* 14 (1949),
Lemma 4, p. 108: "If `p` and `q` are odd primes with `p ≡ 1 (mod 4)` and such that `(q/p) = −1`,
then `2 + pqM² + pZ² = X² + qY²` has a solution for `X, Y, Z` if and only if the denominator of `M`
in lowest terms is prime to `p` and `q`." Capital letters denote rationals (p. 106). With
`M = n / d` in lowest terms and `m = 2 d ^ 2 + p q n ^ 2`, the equation is solvable exactly when
`X ^ 2 + q Y ^ 2 - p Z ^ 2` represents `m`. If `p ∣ d` or `q ∣ d`, then `m` is of one of the forms
that Robinson's Lemma 2 excludes (`lemma_two_only_if`). If `d` is prime to `p` and `q`, then `m` is
represented by `exists_sq_add_mul_sq_sub_mul_sq_eq`, which proves the needed case of the "if" half
of Lemma 2.
