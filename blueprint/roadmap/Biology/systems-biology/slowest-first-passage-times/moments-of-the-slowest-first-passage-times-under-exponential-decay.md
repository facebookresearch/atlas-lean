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

## Proof depends on

- [Gumbel-type limit of the slowest first passage times](gumbel-type-limit-of-the-slowest-first-passage-times.md)

## Expansion

$\mathbb E[Y_k] = -\mathbb E\ln(E_1 + \dots + E_{k+1}) = -\psi(k+1) = \gamma - H_k$ and $\operatorname{Var}(Y_k) = \psi'(k+1)$, because $E_1 + \dots + E_{k+1}$ is Gamma$(k+1, 1)$. Part 2 compares moment integrals rather than coupling samples. Writing $\mathbb E[(\lambda T_{N-k,N} - \ln A)^m]$ (up to an exponentially small contribution from $\lambda T_{N-k,N} < \ln A$) as $\int_0^\infty m t^{m-1}\,\mathbb P(\lambda T_{N-k,N} - \ln A > t)\,dt$ and inserting the exact binomial law with $S(t + \ln A/\lambda) = e^{-\lambda t} + O(e^{-\beta t})$, the integrand differs from the one for $N$ independent unit-rate exponential variables by terms controlled by the $O(e^{-\beta t})$ remainder. For the exponential variables Rényi's representation gives the moments exactly: the $(k+1)$-st largest has the law of $\sum_{i=1}^{N-k} E_i/(i+k)$, with mean $H_N - H_k$ and variance $\psi'(k+1) - \psi'(N+1)$.

## Sources

- S. D. Lawley and J. Johnson, *Slowest first passage times, redundancy, and menopause timing*, J. Math. Biol. (2023), <https://doi.org/10.1007/s00285-023-01921-9>; arXiv:2206.09255. Numbering as in arXiv v2: Theorems 2 and 4 and, for part 2, the proof of Theorem 4 in the appendix, Equations (94)–(100) (journal version: Theorems 2 and 3, Appendix A.1).
