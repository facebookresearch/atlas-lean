# NP/NN duality

Let $a$ be the array of a triangular recurrence with parameters
$(\alpha, \beta, \gamma; \alpha', \beta', \gamma')$, with weights
$w(n, k) = \alpha(n + 1) + \beta k + \gamma$ and $w'(n, k) = \alpha'(n + 1) + \beta' k + \gamma'$,
and let $\tilde a$ be the array of the reflected recurrence, with parameters
$(\alpha' + \beta', -\beta', \gamma'; \alpha + \beta, -\beta, \gamma)$ and weights $\tilde w$,
$\tilde w'$. Then for all integers $n, k$ the negative-positive and negative-negative numbers
satisfy $\tilde a^{NP}_{n,k} = a^{NN}_{n,n-k}$ and $\tilde a^{NN}_{n,n-k} = a^{NP}_{n,k}$.
Moreover, $\tilde w(n, k) \ne 0$ for all integers $n < 0 \le k$ if and only if
$w'(n, k + 1) \ne 0$ for all integers $k \le n < 0$; and $\tilde w'(n, k + 1) \ne 0$ for all
integers $k \le n < 0$ if and only if $w(n, k) \ne 0$ for all integers $n < 0 \le k$.

Thus the divisor condition of Definition 1 for $\tilde a$ is equivalent to that of Definition 2
for $a$, and conversely, so the left-hand sides exist exactly when the right-hand sides do.
With junk value $0$ for a zero divisor, the two identities need no existence hypothesis.

## Sources

- Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Proposition 3.
