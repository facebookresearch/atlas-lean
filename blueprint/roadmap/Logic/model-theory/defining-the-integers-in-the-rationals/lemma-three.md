# Robinson's Lemma 3

Let `p` be a prime with `p ≡ 3 (mod 4)` and let `M` be a rational
number. Then `2 + p M ^ 2 + p Z ^ 2 = X ^ 2 + Y ^ 2` has a solution in rational numbers `X, Y, Z`
if and only if the denominator of `M` in lowest terms is odd and prime to `p`.

J. Robinson, "Definability and decision problems in arithmetic", *J. Symbolic Logic* 14 (1949),
Lemma 3, p. 108: "If `p` is a prime `≡ 3 (mod 4)` then `2 + pM² + pZ² = X² + Y²` has a solution
for `X, Y`, and `Z` if and only if the denominator of `M` in lowest terms is odd and prime to `p`."
Capital letters denote rationals (p. 106). With `M = n / d` in lowest terms and
`m = 2 d ^ 2 + p n ^ 2`, the equation is solvable exactly when `X ^ 2 + Y ^ 2 - p Z ^ 2`
represents `m`. If `p ∣ d` or `2 ∣ d`, then `m` is of one of the forms that Robinson's Lemma 1
excludes (`lemma_one_only_if`). If `d` is odd and prime to `p`, then `m ≡ 1, 2 (mod 4)`, and `m` is
represented by `exists_sq_add_mul_sq_sub_mul_sq_eq`, which proves the needed case of the "if" half
of Lemma 1.
