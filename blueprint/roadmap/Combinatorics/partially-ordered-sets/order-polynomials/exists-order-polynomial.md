# The order polynomial is a polynomial

For a finite poset $P$ with $p$ elements there is a polynomial $\Omega_P(x) \in \mathbb{Q}[x]$ of degree
$p$ with leading coefficient $e(P)/p!$ whose value at every $m \in \mathbb{N}$ is the number of
order-preserving maps $P \to [m]$; here $e(P)$ is the number of linear extensions of $P$.

Explicitly, $\Omega_P(x) = \sum_{s=0}^{p} e_P(s)\, x(x-1)\cdots(x-s+1)/s!$: the expansion in
binomial coefficients, with $e_P(p) = e(P) > 0$ giving the leading coefficient, as in Section
3.15.3 ("It follows that ...").

## Sources

- R. P. Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011, https://math.mit.edu/~rstan/ec/ec1.pdf, Section 3.12, after Proposition 3.12.1, and Section 3.15.3.
