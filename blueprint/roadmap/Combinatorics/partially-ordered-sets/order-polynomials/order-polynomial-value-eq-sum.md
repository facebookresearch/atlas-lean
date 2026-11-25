# Expansion of the order polynomial in binomial coefficients

For every $m \in \mathbb{N}$,

$$\Omega_P(m) = \sum_{s=0}^{p} e_P(s) \binom{m}{s},$$

where $e_P(s)$ counts the surjective order-preserving maps $P \to [s]$: an order-preserving map
$P \to [m]$ is a choice of its $s$-element image in $[m]$ followed by a surjective order-preserving
map onto it. Stanley sums from $s = 1$; the term $s = 0$ vanishes unless $P$ is empty, where it is
the only term.

Since $\binom{m}{s}$ is a polynomial in $m$ of degree $s$ and $e_P(p) = e(P)$, this expansion shows that
$\Omega_P$ is a polynomial of degree $p$ with leading coefficient $e(P)/p!$.

## Sources

- R. P. Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011, https://math.mit.edu/~rstan/ec/ec1.pdf, Section 3.15.3, display before Theorem 3.15.8.
