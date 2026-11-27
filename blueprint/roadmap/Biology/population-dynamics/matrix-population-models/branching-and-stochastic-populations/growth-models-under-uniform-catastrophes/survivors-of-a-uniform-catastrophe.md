# Survivors of a uniform catastrophe

**Model.** A colony starts with one individual and gains individuals by a Poisson process of rate $\lambda > 0$; catastrophes strike at the times of an independent rate-1 Poisson process. A **uniform catastrophe** reduces a colony of size $i$ to size $j$ with probability $\mu_{ij} = 1/i$ for each $j \in \{0, 1, \dots, i-1\}$. Let $N$ be the number of survivors of the first catastrophe.

**Statement.**

1. The law of $N$ is

$$\mathbb{P}(N = n) = \frac{1}{\lambda + 1}\Big(\frac{\lambda}{\lambda+1}\Big)^{n}\, \Phi\Big(\frac{\lambda}{\lambda+1}, 1, n+1\Big), \qquad n \ge 0,$$

where $\Phi(z, s, a) = \sum_{j \ge 0} z^j/(j + a)^s$ is the Lerch transcendent; its generating function is

$$\mathbb{E}\big(s^N\big) = \frac{\ln\big(1 + \lambda(1-s)\big)}{\lambda(1-s)}, \qquad \mathbb{E}(N) = \frac{\lambda}{2}.$$

2. (No dispersal.) If the survivors stay in the same colony, the colony size is the continuous-time Markov chain with rates $q_{i,i+1} = \lambda$ and $q_{i,j} = 1/i$ for $0 \le j < i$, started at 1. This chain hits $0$ almost surely for every $\lambda > 0$: a single colony under uniform catastrophes always dies out.

## Expansion

At the first catastrophe the colony size is $1 + G$, where $G$, the number of Poisson births before an independent rate-1 exponential time, is geometric: $\mathbb{P}(G = k) = \frac{1}{\lambda+1}\big(\frac{\lambda}{\lambda+1}\big)^k$. Given size $i$, the survivor count is uniform on $\{0, \dots, i-1\}$, so $\mathbb{P}(N = n) = \sum_{k \ge n} \mathbb{P}(G = k)/(k+1)$, which is the Lerch series; summing the generating function gives the logarithm. Without dispersal, a catastrophe halves the size on average, so the drift of $\ln X$ is eventually negative, and a Foster–Lyapunov criterion shows that the embedded chain is positive recurrent; recurrence of state 0 means extinction.

## Proof depends on

- [Foster's criterion for positive recurrence](../../../../../Probability/markov-chains/foster-lyapunov-criteria/foster-s-criterion-for-positive-recurrence.md)

## Sources

- J. Amaya, V. V. Junior, F. P. Machado and A. Roldán-Correa, "Growth models under uniform catastrophes", *Journal of Statistical Physics* 193(11) (2026), 162, Proposition 2.1, Theorem 2.2; Foster's theorem as Theorem 4.1, <https://doi.org/10.1007/s10955-026-03718-8> (preprint arXiv:2602.06649).
