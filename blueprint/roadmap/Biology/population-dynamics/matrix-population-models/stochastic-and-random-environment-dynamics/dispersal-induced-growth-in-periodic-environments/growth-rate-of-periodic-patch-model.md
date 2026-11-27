# Growth rate of a linear patch model with periodic local growth rates

This page covers the setting and the growth-rate characterisation of Katriel (2022), Sections 2.1, 3.1 and 4, used for [dispersal-induced growth](dispersal-induced-growth-all-sink-case.md).

**Model.** Populations $x_i(t)$ on $N$ patches have $2\pi$-periodic continuous local growth rates $r_i(\theta)$, evaluated at $\theta = \omega t$ (frequency $\omega > 0$), and disperse at rate $m \ge 0$:

$$x' = [R(\omega t) + mL]\, x, \qquad R(\theta) = \mathrm{diag}(r_1(\theta), \dots, r_N(\theta)),$$

where $L$ is symmetric, irreducible, has nonnegative off-diagonal entries $L_{ij}$ and zero row sums ($L_{ii} = -\sum_{j \ne i} L_{ij}$). The two-patch examples here and on the pages that cite this one take $L_{12} = L_{21} = 1$, $L_{11} = L_{22} = -1$ (Example 1 of the source): $x_1' = r_1(\omega t)x_1 + m(x_2 - x_1)$, $x_2' = r_2(\omega t)x_2 + m(x_1 - x_2)$. A general two-patch $L$ has $L_{12} = L_{21} = a > 0$, and its formulas follow from these by replacing $m$ with $ma$. Write $\bar r_i = \frac{1}{2\pi}\int_0^{2\pi} r_i$; patch $i$ is a source if $\bar r_i > 0$ and a sink if $\bar r_i < 0$. Let $\lambda(A)$ denote the largest eigenvalue of a symmetric matrix $A$.

**Statement.** For $m > 0$:

1. **Common growth rate.** Every solution with positive initial data stays positive, and $\Lambda[x_i] = \lim_{t\to\infty} t^{-1}\ln x_i(t)$ exists and is the same for all $i$ and all such initial data. This common value $\Lambda(m, \omega)$ is the principal Floquet exponent, $\Lambda = \frac{\omega}{2\pi}\ln \rho(X(2\pi/\omega))$, where $X$ is the principal [fundamental matrix](../../../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/fundamental-matrix-linear-system.md), $X' = [R(\omega t) + mL]X$ with $X(0) = I$ (Eq. (18)), whose entries are strictly positive for every $t > 0$, and $\rho$ is the spectral radius; and equals the principal eigenvalue of the periodic problem $\omega u' = [R(\theta) + mL]u - \Lambda u$, $u(\theta + 2\pi) = u(\theta)$ (Lemma 1). $\Lambda$ is real-analytic in $(m, \omega)$.
2. **Monotonicity in frequency (Lemma 2).** $\partial_\omega \Lambda(m, \omega) \le 0$, strictly unless all differences $r_i - r_j$ are constant.
3. **Low-frequency limit (Lemma 5).** $\displaystyle\lim_{\omega \to 0^+}\Lambda(m, \omega) = \Lambda_0(m) := \frac{1}{2\pi}\int_0^{2\pi} \lambda\big(R(\theta) + mL\big)\, d\theta$.
4. **High-frequency limit (Lemma 8).** $\displaystyle\lim_{\omega \to \infty}\Lambda(m, \omega) = \Lambda_\infty(m) := \lambda(\bar R + mL)$, $\bar R = \mathrm{diag}(\bar r_1, \dots, \bar r_N)$.
5. **Constant rates (Lemma 6).** For a diagonal $D$, $\lambda(D + mL)$ is nonincreasing in $m$, strictly decreasing unless all $d_i$ are equal, tends to $\frac1N\sum_i d_i$ as $m \to \infty$, and is at most $\max_i d_i$. Hence with time-independent rates and all patches sinks, $\Lambda < 0$: dispersal alone cannot rescue sinks without temporal variation.

For two patches with $L_{12} = L_{21} = 1$, $\lambda(R(\theta) + mL) = \tfrac12\big(r_1 + r_2 + \sqrt{(r_1 - r_2)^2 + 4m^2}\big) - m$.

## Depends on

- [Fundamental matrix of a linear system](../../../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/fundamental-matrix-linear-system.md)

## Proof depends on

- [Perron–Frobenius theorem for primitive nonnegative matrices](../../../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius-for-primitive-nonnegative-matri.md)

## Expansion

$R(\omega t) + mL$ is cooperative and irreducible, so the principal fundamental matrix has positive entries for $t > 0$ (Kamke-Muller). The monodromy matrix $X(T)$, $T = 2\pi/\omega$, is therefore entrywise positive, hence primitive, and the [Perron–Frobenius theorem for primitive nonnegative matrices](../../../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius-for-primitive-nonnegative-matri.md) gives a simple positive Perron root $\rho$ with positive eigenvector $v$. The normalisation $X(0) = I$ matters: for another fundamental matrix $Y = XC$ the formula would use $\rho(Y(T))$, which already for $C = 2I$ shifts the exponent by $\ln 2/T$. Then $\phi(t) = e^{-\lambda t}X(t)v$ with $\lambda = T^{-1}\ln\rho$ is $T$-periodic, and every positive solution is squeezed between constant multiples of $e^{\lambda t}\phi(t)$, which gives the common growth rate. Lemmas 2, 5 and 8 are results of Liu et al. (2022) on principal eigenvalues of time-periodic cooperative systems, applied to the periodic problem. Lemma 6 follows from the min-max principle, since $L$ is negative semidefinite with top eigenvalue $0$ and eigenvector $(1, \dots, 1)$. The same monodromy-matrix construction defines the periodic reproduction number in [threshold dynamics of compartmental epidemic models in periodic environments](../../../../epidemiology/next-generation-matrix-and-the-basic-reproductio/threshold-dynamics-in-periodic-environments.md), a related setting that this page does not use.

## Sources

- G. Katriel, Dispersal-induced growth in a time-periodic environment, *J. Math. Biol.* 85 (2022), article 24, <https://doi.org/10.1007/s00285-022-01791-7>; preprint <https://arxiv.org/abs/2104.01589> (lemma and equation numbers follow the preprint).
