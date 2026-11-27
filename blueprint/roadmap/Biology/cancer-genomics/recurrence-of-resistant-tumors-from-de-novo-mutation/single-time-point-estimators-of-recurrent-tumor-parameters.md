# Single-time-point estimators of recurrent-tumor parameters

**Model.** At treatment start a tumor consists of $n$ drug-sensitive cells forming a subcritical birth-death process $Z_0^n$ with birth rate $r_0$, death rate $d_0$ and net rate $\lambda_0 = r_0 - d_0 < 0$. Sensitive cells produce resistant mutants at total rate $Z_0^n(t)\, n^{-\alpha}$, $\alpha \in (0,1)$; each mutant founds a clone that is a supercritical birth-death process with rates $r_1, d_1$ and $\lambda_1 = r_1 - d_1 > 0$. Let $Z_1^n$ be the resistant population, $\gamma_n = \inf\{t \ge 0 : Z_1^n(t) \ge n\}$ the recurrence time, and $\zeta_n$ the solution of $\mathbb{E}[Z_1^n(t)] = n$, where

$$\mathbb{E}[Z_1^n(t)] = \frac{n^{1-\alpha} e^{\lambda_1 t}}{\lambda_1 - \lambda_0}\big(1 - e^{(\lambda_0-\lambda_1)t}\big), \qquad \zeta_n \sim \frac{\alpha}{\lambda_1}\log n .$$

Let $I_n(t)$ be the number of mutant clones born before $t$ that never go extinct, $\hat I_n(t)$ the number born before $t$ and alive at $t$, and $R_n(t) = \sum_i (X_{i,n}(t)/Z_1^n(t))^2$ the Simpson index of resistant clone sizes $X_{i,n}(t)$.

At recurrence observe $\gamma_n$, the sensitive count $Z_0^n = Z_0^n(\gamma_n)$, the clone count $I_n = I_n(\gamma_n)$ and the Simpson index $R_n = R_n(\gamma_n)$. Set

$$U_n = \frac{\sqrt{I_n R_n}}{\sqrt{I_n R_n - 2}} - 1 .$$

**Theorem 4.** If $\alpha < -\lambda_1/\lambda_0$, then

$$\hat\lambda_0^{(n)} = \frac{1}{\gamma_n}\log\frac{Z_0^n}{n}, \qquad \hat\lambda_1^{(n)} = -\frac{\hat\lambda_0^{(n)}}{U_n}, \qquad \hat r_1^{(n)} = \Big(\frac{1}{U_n} + 1\Big)\frac{n\,\hat\lambda_1^{(n)}}{I_n\, e^{\hat\lambda_1^{(n)}\gamma_n}},$$

$$\hat\alpha^{(n)} = 1 - \log_n I_n + \log_n\Big(\frac{\hat\lambda_1^{(n)}}{-\hat\lambda_0^{(n)}\,\hat r_1^{(n)}}\Big)$$

are consistent estimators of $\lambda_0, \lambda_1, r_1$ and $\alpha$. Moreover $n^u|\hat\lambda_0^{(n)} - \lambda_0| \to 0$ in probability for $u < \min\{(1-\alpha)/2,\ 1/2 + \alpha\lambda_0/(2\lambda_1)\}$, and $n^u|\hat\lambda_1^{(n)} - \lambda_1| \to 0$ for $u < \min\{(1-\alpha)/4,\ -\lambda_0\alpha/(2\lambda_1),\ 1/2 + \alpha\lambda_0/(2\lambda_1)\}$.

The condition $\alpha < -\lambda_1/\lambda_0$ ensures that sensitive cells are still present (in growing numbers) at recurrence, so $Z_0^n(\gamma_n)$ carries information about $\lambda_0$.

## Depends on

- [Clone number and Simpson index at tumor recurrence](clone-number-and-simpson-index-at-tumor-recurrence.md)

## Expansion

The sensitive population is $Z_0^n(\gamma_n) \approx n e^{\lambda_0\gamma_n}$, which gives $\hat\lambda_0$. Multiplying the limits of $I_n/n^{1-\alpha}$ and $n^{1-\alpha}R_n$ eliminates $n^{1-\alpha}$ and $r_1$: $I_n R_n \to 2(\lambda_1-\lambda_0)^2/(-\lambda_0(2\lambda_1 - \lambda_0))$, a function of $\lambda_1/\lambda_0$ alone, which inverts to $U_n \to -\lambda_0/\lambda_1$. The size relation $n = \mathbb{E}[Z_1^n(\zeta_n)]$ then yields $r_1$ via the clone count, and the clone-count limit $I_n \approx -\lambda_1 n^{1-\alpha}/(\lambda_0 r_1)$ is solved for $\alpha$ on the $\log_n$ scale. Consistency and the rates follow from the delta method applied to Theorems 1–3.

## Sources

- Kevin Leder, Ruping Sun, Zicheng Wang and Xuanming Zhang, "Parameter estimation from single patient, single time-point sequencing data of recurrent tumors", Journal of Mathematical Biology 89 (2024), 51, <https://doi.org/10.1007/s00285-024-02149-x>; numbering as in arXiv:2403.13081: Theorems 1–4, Propositions 1–2 and Corollary 1.
