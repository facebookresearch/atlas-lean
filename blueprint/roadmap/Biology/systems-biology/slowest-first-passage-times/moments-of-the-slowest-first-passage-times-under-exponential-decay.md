# Moments of the slowest first passage times under exponential decay

Let $T_{N-k,N}$ be the $(k+1)$-st slowest of $N$ independent copies of a first passage time $\tau > 0$ with survival probability $S(t) = \mathbb P(\tau > t)$, as in the [Gumbel-type limit](gumbel-type-limit-of-the-slowest-first-passage-times.md). Write $H_k = \sum_{r=1}^k r^{-1}$, $\gamma$ for the Euler–Mascheroni constant and $\psi'(k+1) = \sum_{r \ge 0} (r + k + 1)^{-2}$.

1. **Moment convergence.** If $S(t) \sim A(\lambda t)^{-p} e^{-\lambda t}$ with $A, \lambda > 0$ and $p \in \mathbb R$, then for every integer $m \ge 1$ and fixed $k \ge 0$, $\mathbb E[(\lambda T_{N-k,N} - b_N)^m] \to \mathbb E[Y_k^m]$, with $b_N$ and $Y_k$ as in the Gumbel-type limit. In particular, as $N \to \infty$,

$$\mathbb E[T_{N-k,N}] = \lambda^{-1}\bigl(\ln N - p \ln\ln N + \ln A + \gamma - H_k + o(1)\bigr), \qquad \operatorname{Var}(T_{N-k,N}) = \lambda^{-2}\bigl(\psi'(k+1) + o(1)\bigr),$$

so the coefficient of variation behaves like $\sqrt{\psi'(k+1)}/\ln N \to 0$.

2. **Sharper expansion for a spectral gap.** If $S(t) - A e^{-\lambda t} = O(e^{-\beta t})$ with $A > 0$ and $\beta > \lambda > 0$, then for fixed $k \ge 0$,

$$\mathbb E[T_{N-k,N}] = \lambda^{-1}\bigl(H_N - H_k + \ln A\bigr) + O\bigl(N^{-(\beta/\lambda - 1)}\bigr),$$

$$\operatorname{Var}(T_{N-k,N}) = \lambda^{-2}\bigl(\psi'(k+1) - \psi'(N+1)\bigr) + O\bigl(N^{-(\beta/\lambda - 1)} \ln N\bigr).$$

These are the exact moments of the $(k+1)$-st largest of $N$ exponential variables of rate $\lambda$, shifted by $\lambda^{-1}\ln A$, up to the stated error. Convergence in distribution alone does not give part 1: the proof shows that $\{(\lambda T_{N-k,N} - b_N)^{2m}\}_N$ is uniformly integrable.

## Depends on

- [Gumbel-type limit of the slowest first passage times](gumbel-type-limit-of-the-slowest-first-passage-times.md)

## Expansion

$\mathbb E[Y_k] = -\mathbb E\ln(E_1 + \dots + E_{k+1}) = -\psi(k+1) = \gamma - H_k$ and $\operatorname{Var}(Y_k) = \psi'(k+1)$, because $E_1 + \dots + E_{k+1}$ is Gamma$(k+1, 1)$. Part 2 uses Rényi's representation of exponential order statistics, $T_{N-k,N} \approx \lambda^{-1}\bigl(\ln A + \sum_{i=1}^{N-k} E_i/(i+k)\bigr)$, after coupling $\tau$ with an exponential variable through its survival function.

## Sources

- S. D. Lawley and J. Johnson, *Slowest first passage times, redundancy, and menopause timing*, J. Math. Biol. (2023), <https://doi.org/10.1007/s00285-023-01921-9>; arXiv:2206.09255. Theorems 2 and 4.
