# Martingale convergence theorem

Let $(X_n)_{n \ge 0}$ be a real-valued martingale with respect to a filtration $(\mathcal{F}_n)_{n \ge 0}$ on a probability space $(\Omega, \mu)$, and suppose there is a real $C$ with $\mathbb{E}[X_n^+] \le C$ for every $n$, where $X_n^+$ is the positive part of $X_n$. Then there is an integrable $X_\infty : \Omega \to \mathbb{R}$ with $X_n \to X_\infty$ almost surely.

## Idea

A martingale is a fair game, and the theorem says that a fair game whose gains stay bounded on average cannot oscillate forever. Since $\mathbb{E}[X_n] = \mathbb{E}[X_0]$, the bound on positive parts bounds $\mathbb{E}|X_n| = 2\,\mathbb{E}[X_n^+] - \mathbb{E}[X_0]$. The proof counts upcrossings: by Doob's upcrossing inequality, the expected number of times $X_0, \dots, X_n$ crosses from below $a$ to above $b$ is at most $\mathbb{E}[(X_n - a)^+]/(b - a)$, uniformly in $n$. So almost surely no interval with rational endpoints is crossed infinitely often, the sequence converges in $[-\infty, \infty]$, and Fatou's lemma makes the limit integrable, hence finite. The convergence need not hold in $L^1$: a simple random walk started at $1$ and stopped at $0$ tends to $0$ almost surely while its mean stays $1$. Convergence in $L^1$ is equivalent to uniform integrability, also treated on this card.

## Statements

- [Martingale almost-sure convergence theorem](exists-ae-tendsto-of-pos-part-bdd-2.md)
- [Submartingale almost-sure convergence theorem](exists-ae-tendsto-of-pos-part-bdd.md): submartingale form
- [Supermartingale almost-sure convergence theorem](exists-ae-tendsto-of-neg-part-bdd.md): supermartingale form
- [L¹ bound for a submartingale with bounded positive parts](integral-norm-le.md): lemma used in the proof: $L^1$ bound from bounded positive parts
- [Expectations increase along a submartingale](integral-mono.md): lemma used in the proof: expectations increase along a submartingale
- [The $L^p$ martingale convergence theorem](tendsto-e-lp-norm-limit-process-of-e-lp.md): $L^p$ convergence
- [Equivalent conditions for uniform integrability of a submartingale](uniform-integrable-tfae.md): uniformly integrable submartingales
- [Equivalent conditions for uniform integrability of a martingale](uniform-integrable-tfae-2.md): uniformly integrable martingales
- [Square-integrable martingale convergence](ae-tendsto-of-tendsto-predictable-quad-v.md): square-integrable martingales
- [Almost-sure convergence of a martingale series](ae-exists-tendsto-sum-div-succ.md): series of bounded martingale differences divided by $k + 1$
