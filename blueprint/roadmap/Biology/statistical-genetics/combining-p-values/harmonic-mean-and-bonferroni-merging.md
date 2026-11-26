# Harmonic-mean and Bonferroni merging functions

Let $M_{r,K}$ be the power mean of $K$ p-values (with $M_{-\infty,K} = \min$ and $M_{-1,K}$ the harmonic mean).

**Very negative orders** (Proposition 8 of the source). For $r \in [-\infty, -1)$, the family

$$\frac{r}{r + 1} K^{1 + 1/r} M_{r,K}, \qquad K = 2, 3, \dots,$$

is a family of merging functions and is asymptotically precise; $r/(r+1)$ is read as $1$ at $r = -\infty$. At $r = -\infty$ this is the Bonferroni merging function $K \min(p_1, \dots, p_K)$.

**Harmonic mean** (Proposition 9). For $K > 2$ let $y_K$ be the unique solution in $(0, \infty)$ of $y^2 = K\bigl((y + 1)\ln(y + 1) - y\bigr)$ and set

$$a^H_K = \frac{(y_K + K)^2}{(y_K + 1) K}.$$

Then $a^H_K M_{-1,K}$ is a precise merging function, $a^H_K \le e \ln K$, and $a^H_K / \ln K \to 1$ as $K \to \infty$. Hence $(e \ln K) M_{-1,K}$ is a valid, conservative merging function for arbitrarily dependent p-values.

## Depends on

- [p-value merging functions](p-value-merging-function.md)
- [Merging p-values by generalized means](generalized-mean-merging-functions.md)

## Expansion

For $r \le -1$ the function $u \mapsto u^r$ is not integrable at $0$, so the generalized-mean theorem does not apply and the source uses a separate result for non-integrable $\phi$ (Theorem 7). The convergence $a^H_K/\ln K \to 1$ is slow: the source tabulates $a^H_K / \ln K \approx 1.62$ at $K = 100$ and $1.51$ at $K = 400$. Through closed testing, such merging functions also yield multiple-testing procedures generalizing Bonferroni-Holm (Appendix B).

## Sources

- V. Vovk and R. Wang, Combining p-values via averaging, Biometrika 107 (2020). <https://doi.org/10.1093/biomet/asaa027>; numbering follows the preprint <https://arxiv.org/abs/1212.4966> (version 5).
