# The exponent $u(\alpha)$ of support data

For tuples $r = (r_1, \dots, r_d)$ and
$x = (x_1, \dots, x_d)$ of natural numbers and a natural number $\alpha$, let $\ell = \ell(r, x)$
be the integer of the support data and $s_1, \dots, s_d$ its complementary factors. Then
$u(\alpha) = \alpha \ell - \sum_{i=1}^{d} x_i \lfloor \alpha / s_i \rfloor$, computed in the
natural numbers: the subtraction is truncated at $0$, and $\lfloor \alpha / s_i \rfloor$ is
taken to be $0$ when $s_i = 0$.

The results that use $u$ assume valid support data and reflexivity.

## Sources

- Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article A60, Theorem 6.
