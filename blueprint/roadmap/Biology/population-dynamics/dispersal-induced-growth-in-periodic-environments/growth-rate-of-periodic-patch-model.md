# Growth rate of a linear patch model with periodic local growth rates

This page covers the setting and the growth-rate characterisation of Katriel (2022), Sections 2.1, 3.1 and 4, used for [dispersal-induced growth](dispersal-induced-growth-all-sink-case.md).

**Model.** Populations $x_i(t)$ on $N$ patches have $2\pi$-periodic continuous local growth rates $r_i(\theta)$, evaluated at $\theta = \omega t$ (frequency $\omega > 0$), and disperse at rate $m \ge 0$:
$$x' = [R(\omega t) + mL]\, x, \qquad R(\theta) = \mathrm{diag}(r_1(\theta), \dots, r_N(\theta)),$$
where $L$ is symmetric, irreducible, has nonnegative off-diagonal entries $L_{ij}$ and zero row sums ($L_{ii} = -\sum_{j \ne i} L_{ij}$). For two patches, $x_1' = r_1(\omega t)x_1 + m(x_2 - x_1)$, $x_2' = r_2(\omega t)x_2 + m(x_1 - x_2)$. Write $\bar r_i = \frac{1}{2\pi}\int_0^{2\pi} r_i$; patch $i$ is a source if $\bar r_i > 0$ and a sink if $\bar r_i < 0$. Let $\lambda(A)$ denote the largest eigenvalue of a symmetric matrix $A$.

**Statement.** For $m > 0$:

1. **Common growth rate.** Every solution with positive initial data stays positive, and $\Lambda[x_i] = \lim_{t\to\infty} t^{-1}\ln x_i(t)$ exists and is the same for all $i$ and all such initial data. This common value $\Lambda(m, \omega)$ is the principal Floquet exponent, $\Lambda = \frac{\omega}{2\pi}\ln \rho(X(2\pi/\omega))$ with $X$ the fundamental matrix, and equals the principal eigenvalue of the periodic problem $\omega u' = [R(\theta) + mL]u - \Lambda u$, $u(\theta + 2\pi) = u(\theta)$ (Lemma 1). $\Lambda$ is real-analytic in $(m, \omega)$.
2. **Monotonicity in frequency (Lemma 2).** $\partial_\omega \Lambda(m, \omega) \le 0$, strictly unless all differences $r_i - r_j$ are constant.
3. **Low-frequency limit (Lemma 5).** $\displaystyle\lim_{\omega \to 0^+}\Lambda(m, \omega) = \Lambda_0(m) := \frac{1}{2\pi}\int_0^{2\pi} \lambda\big(R(\theta) + mL\big)\, d\theta$.
4. **High-frequency limit (Lemma 8).** $\displaystyle\lim_{\omega \to \infty}\Lambda(m, \omega) = \Lambda_\infty(m) := \lambda(\bar R + mL)$, $\bar R = \mathrm{diag}(\bar r_1, \dots, \bar r_N)$.
5. **Constant rates (Lemma 6).** For a diagonal $D$, $\lambda(D + mL)$ is nonincreasing in $m$, strictly decreasing unless all $d_i$ are equal, tends to $\frac1N\sum_i d_i$ as $m \to \infty$, and is at most $\max_i d_i$. Hence with time-independent rates and all patches sinks, $\Lambda < 0$: dispersal alone cannot rescue sinks without temporal variation.

For two patches, $\lambda(R(\theta) + mL) = \tfrac12\big(r_1 + r_2 + \sqrt{(r_1 - r_2)^2 + 4m^2}\big) - m$.

## Depends on

- [Threshold dynamics of compartmental epidemic models in periodic environments](../../epidemiology/next-generation-matrix-and-the-basic-reproductio/threshold-dynamics-in-periodic-environments.md)

## Expansion

$R(\omega t) + mL$ is cooperative and irreducible, so the fundamental matrix has positive entries (Kamke-Muller) and the monodromy matrix $X(T)$, $T = 2\pi/\omega$, has a simple positive Perron root $\rho$ with positive eigenvector $v$. Then $\phi(t) = e^{-\lambda t}X(t)v$ with $\lambda = T^{-1}\ln\rho$ is $T$-periodic, and every positive solution is squeezed between constant multiples of $e^{\lambda t}\phi(t)$, which gives the common growth rate. Lemmas 2, 5 and 8 are results of Liu et al. (2022) on principal eigenvalues of time-periodic cooperative systems, applied to the periodic problem. Lemma 6 follows from the min-max principle, since $L$ is negative semidefinite with top eigenvalue $0$ and eigenvector $(1, \dots, 1)$.

## Sources

- G. Katriel, Dispersal-induced growth in a time-periodic environment, *J. Math. Biol.* (2022), <https://doi.org/10.1007/s00285-022-01791-7>; preprint <https://arxiv.org/abs/2104.01589> (lemma and equation numbers follow the preprint).
