# Post-processing can only increase the tradeoff function

Let $P, Q$ be probability mass functions on a finite type $\Omega$ and $k$ a channel from $\Omega$ to probability mass functions on a finite type $\Omega_2$. For every $\alpha$ with $0 \le \alpha \le 1$,

$$
T(P, Q)(\alpha) \le T(P k, Q k)(\alpha),
$$

where $Pk$ and $Qk$ are the distributions obtained by passing $P$ and $Q$ through $k$, and $T$ is the [tradeoff function](tradeoff.md).

## Sources

- J. Dong, A. Roth and W. J. Su, *Gaussian Differential Privacy*, Journal of the Royal Statistical Society: Series B, 2022; arXiv:1905.02383, Lemma 2.9.
- P. Kairouz, S. Oh and P. Viswanath, *The Composition Theorem for Differential Privacy*, ICML 2015; IEEE Transactions on Information Theory, 2017; arXiv:1311.0776, Theorem 2.4.
