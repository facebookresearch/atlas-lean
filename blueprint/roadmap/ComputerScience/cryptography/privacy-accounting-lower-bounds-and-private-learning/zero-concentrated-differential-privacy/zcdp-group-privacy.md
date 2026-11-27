# Group privacy for zCDP scales quadratically

If $M$ is $\rho$-zCDP, then for datasets differing in at most $k$ entries, $D_\alpha(M(S) \| M(S')) \le k^2 \rho\,\alpha$ for all $\alpha > 1$: $M$ is $k^2\rho$-zCDP for groups of size $k$. This quadratic scaling is tight, as the Gaussian mechanism shows, and it is better than the linear-in-$k$ growth of $\varepsilon$ with exponentially growing $\delta$ for approximate differential privacy.

## Proof sketch

Use the weak triangle inequality for Rényi divergence: for $P, Q, R$ and conjugate weights, $D_\alpha(P \| R)$ is bounded by a combination of $D_{\alpha'}(P\|Q)$ and $D_{\alpha''}(Q\|R)$ at modified orders. Applied inductively along a chain of $k$ neighbouring datasets with orders chosen proportionally to the chain length, the linear-in-$\alpha$ bounds combine to $k^2\rho\alpha$; for Gaussians the divergence is exactly $\alpha k^2\Delta^2/(2\sigma^2)$ when the mean moves by $k\Delta$.

## Depends on

- [Zero-concentrated differential privacy](zero-concentrated-dp.md)

## Proof depends on

- [The Gaussian mechanism satisfies zCDP with parameter sensitivity squared over twice the variance](gaussian-mechanism-zcdp.md)

## Sources

- M. Bun, T. Steinke, "Concentrated Differential Privacy: Simplifications, Extensions, and Lower Bounds", TCC (2016), arXiv:1605.02065, Proposition 1.9, Lemma 5.2 and Proposition 5.3.
