# Robinson's Lemma 2, necessity of the conditions

Let `p` and `q` be odd primes with
`p ≡ 1 (mod 4)` and `(q / p) = -1`, and let `M` be a nonzero rational number. If
`X ^ 2 + q Y ^ 2 - p Z ^ 2 = M` has a solution in rational numbers `X, Y, Z`, then `M` is of
neither of the forms `p k S ^ 2` with `(k / p) = -1` and `q k S ^ 2` with `(k / q) = -1`, where
`k` is an integer and `S` a rational number. (That `p` is odd follows from `p ≡ 1 (mod 4)`.)

J. Robinson, "Definability and decision problems in arithmetic", *J. Symbolic Logic* 14 (1949),
Lemma 2, p. 108, states: "If `p` and `q` are odd primes with `p ≡ 1 (mod 4)` and `(q/p) = −1`,
then `X² + qY² − pZ²` represents a nonzero rational number `M` if and only if `M` is not of the
form `pk·S²` with `(k/p) = −1` or `qk·S²` with `(k/q) = −1`." Capital letters denote rationals and
small letters integers (p. 106). This theorem is the "only if" half: the conditions are the
obstructions at `p` and at `q`, proved here by descent, with quadratic reciprocity for
`(p / q) = (q / p)`. The whole lemma is `lemma_two`.
