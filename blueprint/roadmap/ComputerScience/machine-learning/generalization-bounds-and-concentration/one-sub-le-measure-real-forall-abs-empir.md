# Uniform deviation over a finite class, high-probability form

Under the hypotheses of the uniform deviation bound for a finite class, with $F$ nonempty and $\ell_\infty > 0$, for every $\delta \in (0, 1]$, with probability at least $1 - \delta$,

$$
|\hat R(f) - R(f)| \lt \ell_\infty \sqrt{\frac{\log(2 |F| / \delta)}{2 n}} \quad \text{for every } f \in F.
$$

Proof: for $t = \ell_\infty \sqrt{\log(2 |F| / \delta) / (2 n)}$ the tail bound $2 |F| \exp(-2 n t^2 / \ell_\infty^2)$ equals $\delta$; pass to the complementary event.

Combined with empirical risk minimization, it gives $R(\hat f) \le \min_{f \in F} R(f) + 2 \ell_\infty \sqrt{\log(2 |F| / \delta) / (2 n)}$ with probability at least $1 - \delta$.

## Sources

- F. Bach, *Learning Theory from First Principles*, MIT Press (2024); author PDF at <https://www.di.ens.fr/~fbach/ltfp_book.pdf>, Section 4.4.3 (finite number of models). The source states the bound with probability greater than $1 - \delta$ and a non-strict inequality; the strict event and the case $\delta = 1$ are derived.
