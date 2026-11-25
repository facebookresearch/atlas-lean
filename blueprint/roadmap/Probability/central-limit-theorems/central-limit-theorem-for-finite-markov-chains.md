# Central limit theorem for additive functionals of finite Markov chains

Let $P$ be an irreducible stochastic matrix on a finite nonempty set $S$, with
stationary probability vector $\pi$, and let $f:S\to\mathbb R$ satisfy
$\pi(f)=\sum_{y}\pi(y)f(y)=0$. Then the Poisson equation

$$(I-P)g=f,\qquad \pi(g)=0,$$

has a unique solution $g:S\to\mathbb R$. For the
[Markov chain](../markov-chains/finite-markov-chains/is-finite-markov-chain.md)
$(X_t)_{t\ge0}$ with transition matrix $P$ and any initial law,

$$\sum_{t=0}^{n-1}f(X_t)=g(X_0)-g(X_n)+M_n,\qquad
M_n=\sum_{t=1}^{n}\bigl(g(X_t)-(Pg)(X_{t-1})\bigr),$$

where $(M_n)$ is a martingale with bounded increments, and

$$\frac1{\sqrt n}\sum_{t=0}^{n-1}f(X_t)\ \xrightarrow{\ d\ }\ \mathcal N(0,\sigma^2),
\qquad \sigma^2=\pi\bigl(g^2-(Pg)^2\bigr)=\sum_{y}\pi(y)\bigl(g(y)^2-(Pg)(y)^2\bigr).$$

When $\sigma^2=0$ the limit is the point mass at $0$. Aperiodicity is not
needed: the variance limit uses only the strong law for irreducible chains.

## Depends on

- [Finite-state Markov chain](../markov-chains/finite-markov-chains/is-finite-markov-chain.md)

## Proof depends on

- [Strong law for finite irreducible Markov chains](../markov-chains/convergence-theorem-for-finite-markov-chains/strong-law-for-additive-functionals-of-finite-ir.md)
- [Stationary distribution is unique](../markov-chains/convergence-theorem-for-finite-markov-chains/stationary-unique.md)
- [Martingale central limit theorem for bounded increments](martingale-central-limit-theorem.md)

## Expansion

A proof page must establish:

- Solvability and uniqueness of the Poisson equation: for irreducible $P$, the
  kernel of $I-P$ is the constants and the range is $\{h:\pi(h)=0\}$.
- The telescoping decomposition above and the martingale property of $M_n$
  with increments bounded by $2\max_y|g(y)|$.
- Convergence of the normalized conditional variances
  $\frac1n\sum_{t=1}^{n}\bigl(P(g^2)-(Pg)^2\bigr)(X_{t-1})\to\sigma^2$ almost
  surely, from the strong law and $\pi P=\pi$.
- The martingale central limit theorem for bounded increments, and the
  negligibility of the bounded endpoint term $g(X_0)-g(X_n)$.
- The degenerate case $\sigma^2=0$ separately.

## Sources

- S. P. Meyn and R. L. Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition, Cambridge University Press (2009), Chapter 17 (central limit theorem via the Poisson equation)
- P. Hall and C. C. Heyde, *Martingale Limit Theory and Its Application*, Academic Press (1980), Chapter 3 (martingale central limit theorem)
