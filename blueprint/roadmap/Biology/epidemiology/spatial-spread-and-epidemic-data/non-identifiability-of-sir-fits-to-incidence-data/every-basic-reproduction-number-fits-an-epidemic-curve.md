# Every basic reproduction number fits an epidemic curve

**Model.** With $\rho = \beta\tau$ the basic reproduction number and $\tau > 0$ the mean infectious period, consider

$$
S' = -\frac{\rho S I}{\tau}, \qquad I' = \frac{\rho S I - I}{\tau}, \qquad S(-\infty) = 1,
$$

on the whole time line; the incidence is $-S'$ and the final size depends only on $\rho$. A *target triple* $(A_f, \mu_f, \sigma_f)$ prescribes the total number of cases, the mean time and the standard deviation of an observed incidence curve. A function $A\cdot(-S'(t))$ is a *good fit* to the triple if its total mass, mean time and standard deviation equal $A_f$, $\mu_f$ and $\sigma_f$.

**Results.**
1. *(Symmetries.)* If $(S, I)$ solves the model with $\tau = 1$ and $-S'$ has mean time $0$, then for every $a > 0$ and $\mu \in \mathbb{R}$, $(S, I)\bigl(\tfrac{t - \mu}{a}\bigr)$ solves the model with $\tau = a$; the incidence keeps its total mass, has mean time $\mu$, and has standard deviation multiplied by $a$.
2. *(Theorem.)* For every target triple and every $\rho > 1$ there exist a scale $A > 0$, an infectious period $\tau > 0$, and a solution with that $\rho$ and $\tau$ whose scaled incidence $A\cdot(-S_1')$ is a good fit. The source proves this for each $\rho$ for which the model with $\tau = 1$ has a nonconstant solution whose incidence has mean time $0$; such a solution exists for every $\rho > 1$. Indeed the disease-free state $(1,0)$ then has the unstable eigenvalue $\rho - 1$, its one-dimensional unstable manifold gives a nonconstant solution with $S(-\infty) = 1$, its incidence decays exponentially as $t \to -\infty$ (rate $\rho - 1$) and as $t \to +\infty$ (rate $1 - \rho S(\infty) > 0$), so it has finite mean and standard deviation, and a time shift makes the mean $0$. Hence matching mean, spread and size of an outbreak puts no constraint on $\mathcal{R}_0$.
3. *(Multigroup version.)* For the $N$-group model $S_i' = -S_i\sum_j \frac{\rho_{ij}}{\tau_j} I_j$, $I_i' = S_i\sum_j \frac{\rho_{ij}}{\tau_j}I_j - \frac{I_i}{\tau_i}$, $S_i(-\infty) = 1$, any nonconstant solution whose incidence has finite mean and standard deviation can be rescaled (a common factor $\phi$ on all $\tau_j$, a time shift and an amplitude $A$) to fit any target triple, so the good fits form an $N^2$-dimensional family indexed by the matrix $(\rho_{ij})$.

## Depends on

- [Final-size equation (Kermack–McKendrick 1927)](../../kermack-mckendrick-sir-model/final-size-eq.md)

## Proof sketch

Writing the model with $\rho$ and $\tau$ separates shape from time scale: changing $\tau$ only stretches time, and the solution on $(-\infty, \infty)$ can be shifted freely, so two of the three summary statistics (mean time and spread) are adjusted by a time translation and a dilation, and the third (size) by the reporting factor $A$, which absorbs under-ascertainment or population size. None of these touches $\rho$. Fitting summary features of a single outbreak therefore leaves $\mathcal{R}_0$ undetermined, and estimates of it from such fits reflect the details of curve shape or prior choices rather than the three dominant characteristics of the data.

## Sources

- B. Shayak, Sana Jahedi and James A. Yorke, "Ambiguity in identifying parameters of an SIR model when fitting epidemic incidence data", *Mathematical Biosciences and Engineering* 23 (2026), 913–939, <https://doi.org/10.3934/mbe.2026036>. Preprint version: arXiv:2404.04181 (2024), Theorem 1, Proposition 1, Theorem 2, <https://doi.org/10.48550/arXiv.2404.04181>.
