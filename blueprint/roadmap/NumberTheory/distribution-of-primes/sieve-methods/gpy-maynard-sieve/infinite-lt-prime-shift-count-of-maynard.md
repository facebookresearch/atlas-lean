# Maynard's reduction for one weight profile

Let $\theta, \rho \in \mathbb R$, $I > 0$ and $J \in \mathbb R$ with $\rho < \tfrac{\theta}{2} \cdot \tfrac{J}{I}$, and let $\delta_0 > 0$. Suppose that for every $\delta \in (0, \delta_0)$ there are weights $w_N(n) \ge 0$ and a normalisation $B(N)$, positive for large $N$, with

$$\frac{S_1(N)}{B(N)} \to I, \qquad \frac{S_2(N)}{B(N)} \to \Bigl(\frac{\theta}{2} - \delta\Bigr) J,$$

where $S_1, S_2$ are the sums of [the limiting step](infinite-lt-prime-shift-count-of-tendsto.md). Then infinitely many $n$ have more than $\rho$ of the $n + h$, $h \in H$, prime.

The hypothesis is the shape of Maynard's Proposition 4.1. If the primes have level of distribution $\theta$, $R = N^{\theta/2 - \delta}$ and $F$ is a smooth profile, Proposition 4.1 gives
$S_1 = (1 + o(1))\, B\, I_k(F)$ and $S_2 = (1 + o(1))\, B\, \tfrac{\log R}{\log N} \sum_m J_k^{(m)}(F)$ with $B = \varphi(W)^k N (\log R)^k / W^{k+1}$; since $\log R / \log N = \theta/2 - \delta$, this is the hypothesis with $I = I_k(F)$ and $J = \sum_m J_k^{(m)}(F)$. The asymptotics are hypotheses: the statement by itself says nothing about the distribution of primes.

## Informally uses

- [From the asymptotics of $S_1$ and $S_2$ to infinitely many prime-rich translates](infinite-lt-prime-shift-count-of-tendsto.md): applied with one $\delta$ small enough that $\rho I < (\theta/2 - \delta) J$.

## Background

- [Elliott–Halberstam estimate at level $\theta$](../../prime-gaps-short-intervals/bounded-gaps-between-primes/elliott-halberstam-at.md) and the [Bombieri–Vinogradov theorem](../../primes-in-progressions/bombieri-vinogradov-theorem/bombieri-vinogradov.md): the level-of-distribution inputs behind Proposition 4.1.

## Sources

- J. Maynard, "Small gaps between primes", *Ann. of Math.* 181 (2015), 383–413; theorem and display numbers are those of arXiv:1311.4600v3 (28 Oct 2019).
