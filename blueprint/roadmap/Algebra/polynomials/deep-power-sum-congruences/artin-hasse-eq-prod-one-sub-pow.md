# The Artin–Hasse exponential as a product

Let $p$ be a prime, let $\mu$ be the Möbius
function and let $F(z) = \exp\big(\sum_{j \ge 0} z^{p^j} / p^j\big) \in \mathbb{Q}[[z]]$ be the
Artin–Hasse exponential. For $d \ge 1$ and $a \in \mathbb{Q}$ write
$(1 - z^d)^a = \exp\big(a \log(1 - z^d)\big)$, where $\log(1 - z^d) = -\sum_{k \ge 1} z^{dk}/k$.
Then for every $N \ge 0$, $F$ has the same coefficients of $z^0, \dots, z^N$ as the finite product
of the series $(1 - z^d)^{-\mu(d)/d}$ over the integers $1 \le d \le N$ not divisible by $p$.
Since the factors with $d > N$ are $1 + O(z^{N+1})$, this is the identity
$F(z) = \prod_{p \nmid d} (1 - z^d)^{-\mu(d)/d}$ read coefficientwise.

## Sources

- S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum Congruences*, INTEGERS 24 (2024), Article A46, Proposition 27 (`integers-2024-A46-prop-27`).
