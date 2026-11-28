# Reproduction number and endemic threshold of staged waning immunity under booster vaccination

**Model.** Split the susceptible class of an SIRS-type model into immunity stages $S_0, S_1, \dots, S_n$, from maximal immunity ($S_0$, entered at recovery or vaccination) to none ($S_n$, entered at birth), with transmission rates $0 \le \beta_0 \le \beta_1 \le \dots \le \beta_n$ and $\beta_0 < \beta_n$. Immunity wanes stage by stage at rate $\delta$; infectives recover at rate $r$ straight into $S_0$; births and deaths occur at equal rate $\mu$; and a fraction $p_i \in [0,1]$ of stage $i$ is boosted at rate $\omega$ back into $S_0$ ($p_0 = 0$). With $\omega_i = p_i\omega$, $\delta_i = (1-p_i)\delta$ and the normalization $\sum_i S_i + I = 1$,

$$
\begin{aligned}
\dot S_0 &= \sum_{i=1}^n \omega_i S_i - \delta S_0 + rI - \beta_0 I S_0 - \mu S_0,\\
\dot S_i &= -\omega_i S_i + \delta_{i-1}S_{i-1} - \delta_i S_i - \beta_i I S_i - \mu S_i, \qquad 0 < i < n,\\
\dot S_n &= \mu - \omega_n S_n + \delta_{n-1}S_{n-1} - \beta_n I S_n - \mu S_n,\\
\dot I &= I\sum_{i=0}^n \beta_i S_i - (r+\mu) I .
\end{aligned}
$$

Two booster schemes are compared: (A) boosting any stages except the last ($p_n = 0$), and (B) boosting only the least-immune stage ($p_i = 0$ for $i < n$, $\omega_n > 0$).

**Statement.**

1. *Infection-free waning.* With $I(0) = 0$ and no vaccination, the unique equilibrium is $S_n = 1$, $S_i = 0$ for $i < n$, and it is globally exponentially stable.
2. *Reproduction number.* For the general model the disease-free equilibrium $(S_{i,D})$ is unique and explicit, and it is asymptotically stable if $\sum_i \beta_i S_{i,D} < r + \mu$ and unstable if $\sum_i\beta_i S_{i,D} > r + \mu$, so

$$
R_0 = \frac{\sum_{i=0}^n \beta_i S_{i,D}}{r + \mu}.
$$

3. *Scheme A is useless at equilibrium.* Under scheme A the disease-free state is $S_n = 1$ for any coverages, and $R_0 = \beta_n/(r+\mu)$, independent of the $p_i$.
4. *Scheme B helps.* Under scheme B, $R_0$ is strictly decreasing in $\omega_n$ and strictly below $\beta_n/(r+\mu)$ for every $\omega_n > 0$. For small $\delta$,

$$
R_0 \approx \frac{\omega_n\beta_0 + \mu\beta_n}{(\omega_n + \mu)(r + \mu)} .
$$

5. *Endemic equilibrium (slow waning).* There is $\delta_0 > 0$ such that for $\delta \le \delta_0$, scheme B (and scheme A, with $\omega_n = 0$) has no endemic equilibrium in the feasible region if $(\omega_n + \mu)(\mu + r) > \beta_0\omega_n + \beta_n\mu$, and exactly one if $(\omega_n + \mu)(\mu + r) < \beta_0\omega_n + \beta_n\mu$; in the latter case the endemic equilibrium is asymptotically stable. Its prevalence $I^*$ lies within $O(\sqrt\delta)$ of the root in $[0,1]$ of

$$
1 + \frac{r}{\beta_0 x + \mu} - \frac{\beta_n}{\beta_n x + \mu + \omega_n} - \frac{\omega_n\beta_0}{(\beta_0 x + \mu)(\beta_n x + \mu + \omega_n)} = 0 .
$$

So, at fixed vaccination rate, boosting individuals who have fully lost immunity is the only targeting of these two that lowers the threshold quantity.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof sketch

Without infection the susceptible subsystem is linear with lower bidiagonal Jacobian having eigenvalues $-\delta - \mu$ (repeated) and $-\mu$; the left eigenvector $(1,\dots,1)$ for $-\mu$ encodes conservation, and variation of parameters gives exponential convergence to $e_n$. The disease-free state solves a linear system whose solution by Cramer's rule is a product formula in the $\delta_i$ and the diagonal entries, with the free constant fixed by normalization. Linearizing $\dot I$ at the disease-free state gives the single growth rate $\sum_i\beta_i S_{i,D} - (r+\mu)$, which yields item 2. Under scheme A no flow leaves $S_n$ except by death, so $S_{n,D} = 1$. Under scheme B the bound $\sum_i \beta_i S_{i,D} < \beta_n$ uses $\beta_i \le \beta_n$ with strict inequality on the mass moved to $S_0$; as $\delta \to 0$ the mass sits on $S_0$ and $S_n$ in proportions $\omega_n : \mu$. Endemic equilibria are treated perturbatively: at $\delta = 0$ the equilibrium equations collapse to the displayed scalar equation in $x = I^*$, which has a unique root in $[0,1]$ under the stated inequality, and an implicit-function argument controls the $O(\sqrt\delta)$ displacement and uniqueness for small $\delta$.

## Sources

- Shoshana Elgart, "A perturbative approach to the analysis of many-compartment models characterized by the presence of waning immunity", *Journal of Mathematical Biology* 87 (2023), 61, <https://doi.org/10.1007/s00285-023-01994-6>. Preprint version: arXiv:2109.05605 (2021), Section 3, Theorems 3.1, 3.2, 3.4 and 3.9 and Lemmas 3.6 and 3.8, <https://doi.org/10.48550/arXiv.2109.05605>.
