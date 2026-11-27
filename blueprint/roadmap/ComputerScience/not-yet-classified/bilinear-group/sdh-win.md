# q-SDH win experiment

At a fixed secret exponent `x`, run the randomized
adversary on the `G1` power tuple `i ↦ exp1 (x ^ i)` for `i ≤ t`, on `g2` and
on `exp2 x`, and test whether its output `(c, h)` satisfies the pairing check
`e h (exp2 (x + c)) = e g1 g2`. The SDH parameter is `t`, the `q` of q-SDH,
renamed because `q` is the group order here.

The win predicate uses the pairing-check form rather than `(x + c)⁻¹`: writing
`h = exp1 a`, compat and injectivity reduce the pairing check to
`a * (x + c) = 1`, so the check rejects nonunit `x + c` at every order. When
`x + c` is a unit, it holds iff `h = exp1 ((x + c)⁻¹)` (`sdhCheck_iff`); at
prime order it is the success event of Boneh and Boyen, `c ≠ -x` and
`h = g1 ^ (1 / (x + c))` (`sdhCheck_iff_prime`).
