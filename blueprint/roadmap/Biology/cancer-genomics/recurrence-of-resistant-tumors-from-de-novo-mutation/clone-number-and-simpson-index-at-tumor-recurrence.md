# Clone number and Simpson index at tumor recurrence

**Model.** At treatment start a tumor consists of $n$ drug-sensitive cells forming a subcritical birth-death process $Z_0^n$ with birth rate $r_0$, death rate $d_0$ and net rate $\lambda_0 = r_0 - d_0 < 0$. Sensitive cells produce resistant mutants at total rate $Z_0^n(t)\, n^{-\alpha}$, $\alpha \in (0,1)$; each mutant founds a clone that is a supercritical birth-death process with rates $r_1, d_1$ and $\lambda_1 = r_1 - d_1 > 0$. Let $Z_1^n$ be the resistant population, $\gamma_n = \inf\{t \ge 0 : Z_1^n(t) \ge n\}$ the recurrence time, and $\zeta_n$ the solution of $\mathbb{E}[Z_1^n(t)] = n$, where

$$\mathbb{E}[Z_1^n(t)] = \frac{n^{1-\alpha} e^{\lambda_1 t}}{\lambda_1 - \lambda_0}\big(1 - e^{(\lambda_0-\lambda_1)t}\big), \qquad \zeta_n \sim \frac{\alpha}{\lambda_1}\log n .$$

Let $I_n(t)$ be the number of mutant clones born before $t$ that never go extinct, $\hat I_n(t)$ the number born before $t$ and alive at $t$, and $R_n(t) = \sum_i (X_{i,n}(t)/Z_1^n(t))^2$ the Simpson index of resistant clone sizes $X_{i,n}(t)$.

**Theorem 1.** For every $\epsilon > 0$ and $u < (1-\alpha)/2$, $\ \mathbb{P}\big(n^u |\gamma_n - \zeta_n| > \epsilon\big) \to 0$.

**Theorem 2.** For every $\epsilon > 0$ and $u < \min\{(1-\alpha)/2,\ -\lambda_0\alpha/(2\lambda_1)\}$,

$$\mathbb{P}\Big(n^u\Big|\frac{I_n(\gamma_n)}{n^{1-\alpha}} + \frac{\lambda_1}{\lambda_0 r_1}\Big| > \epsilon\Big) \to 0 ,$$

and by Proposition 1 and Corollary 1 the same holds with the observable count $\hat I_n(\gamma_n)$ in place of $I_n(\gamma_n)$.

**Theorem 3.** For every $\epsilon > 0$ and $u < \min\{(1-\alpha)/4,\ (\lambda_1 - \lambda_0)\alpha/(2\lambda_1)\}$,

$$\mathbb{P}\Big(n^u\Big| n^{1-\alpha} R_n(\gamma_n) - \frac{2 r_1 (\lambda_1 - \lambda_0)^2}{\lambda_1(2\lambda_1 - \lambda_0)}\Big| > \epsilon\Big) \to 0 .$$

So at recurrence about $-\lambda_1 n^{1-\alpha}/(\lambda_0 r_1)$ resistant clones are present, and the Simpson index is of order $n^{-(1-\alpha)}$ with an explicit constant; both concentrate at polynomial rates in a single sample.

## Expansion

Mutant clones arrive as a Cox process with intensity $Z_0^n(s)n^{-\alpha} \approx n^{1-\alpha}e^{\lambda_0 s}$, each surviving forever with probability $\lambda_1/r_1$, so the expected number of surviving clones is $\frac{\lambda_1}{r_1}\int_0^\infty n^{1-\alpha}e^{\lambda_0 s}\,ds = -\lambda_1 n^{1-\alpha}/(\lambda_0 r_1)$ (almost all arrive in the first $O(1)$ time units). A surviving clone born at time $s$ has size of order $e^{\lambda_1(t-s)}$ times an exponential random variable, so its share of $Z_1^n$ is of order $n^{-(1-\alpha)}$ and the sum of squared shares gives the Simpson constant from the second moment of the exponential limit and the arrival profile. Concentration follows from second-moment bounds at the deterministic time $\zeta_n$ together with the polynomial closeness of $\gamma_n$ to $\zeta_n$ (Theorem 1). Clones that are alive at $\gamma_n$ but doomed are negligible because a doomed supercritical clone behaves as a subcritical one with birth and death rates swapped (Proposition 1).

## Sources

- Kevin Leder, Ruping Sun, Zicheng Wang and Xuanming Zhang, "Parameter estimation from single patient, single time-point sequencing data of recurrent tumors", Journal of Mathematical Biology 89 (2024), 51, <https://doi.org/10.1007/s00285-024-02149-x>; numbering as in arXiv:2403.13081: Theorems 1–4, Propositions 1–2 and Corollary 1.
