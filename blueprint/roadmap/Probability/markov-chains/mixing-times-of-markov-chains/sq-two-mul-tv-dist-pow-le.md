# Mixing from a Poincaré inequality, for a lazy reversible chain

Let $K$ be a stochastic matrix reversible with respect to a probability vector $\pi > 0$, let $P = (I + K)/2$ be its lazy version, and suppose $P$ satisfies the Poincaré inequality $\sum_{x,y}(\psi(x)-\psi(y))^2\pi(x)\pi(y) \le B\sum_{x,y}(\psi(x)-\psi(y))^2\pi(x)P(x,y)$ for all $\psi$, with $B \ge 1$. Then for every starting state $x$ and every time $t$,

$$\bigl(2\, d_{TV}(P^t(x,\cdot), \pi)\bigr)^2 \;\le\; (1 - 1/B)^t\,\bigl(1/\pi(x) - 1\bigr).$$

It is an $L^2$ counterpart of Proposition 1(i) of A. Sinclair, *Combinatorics, Probability and Computing* 1 (1992) (stated there with $\lambda_{\max}$, after Diaconis and Stroock), for the lazy chain of Sinclair's Section 2 and of Sinclair and Jerrum, *Information and Computation* 82 (1989), Proposition 3.2: the centred density $P^t(x,\cdot)/\pi - 1$ has $\pi$-mean zero, each step of $P$ multiplies its squared $L^2(\pi)$ norm by at most $1 - 1/B$, and Cauchy–Schwarz bounds twice the total variation distance by that norm. Laziness replaces the spectral bound on the smallest eigenvalue: no eigenvalues are computed. With canonical paths, $B = \bar\rho(\Gamma)$ for the lazy chain gives the mixing time $O(\bar\rho\,(\log \pi(x)^{-1} + \log \varepsilon^{-1}))$.

## Background

- [The canonical-path Poincaré inequality](../canonical-paths-and-multicommodity-flow/sum-sq-sub-mul-le-of-elongated-path-load.md): the usual source of the hypothesis, with $B = \bar\rho(\Gamma)$.
