# Curran's bound for shifted moments of the zeta function under the Riemann hypothesis

Assume the Riemann hypothesis. For every natural number $m$ and all real exponents
$\beta_1, \dots, \beta_m \ge 0$ there are real constants $C$ and $T_0$ such that, for every real
$T \ge T_0$ and all real shifts $\alpha_1, \dots, \alpha_m$ with $|\alpha_k| \le T/2$,

$$
\int_T^{2T} \prod_{k=1}^{m} \Bigl|\zeta\Bigl(\frac12 + i (t + \alpha_k)\Bigr)\Bigr|^{2\beta_k} dt
\le C \, T (\log T)^{\beta_1^2 + \dots + \beta_m^2}
\prod_{1 \le j < k \le m} \Bigl|\zeta\Bigl(1 + i (\alpha_j - \alpha_k) + \frac{1}{\log T}\Bigr)\Bigr|^{2\beta_j\beta_k}.
$$

The bound removes the factor $(\log T)^{\varepsilon}$ from Chandee's bound for these moments.

## Sources

- A. Hamieh, H. Kadiri, G. Martin and N. Ng (eds.), *Moments of L-functions Problem List*, arXiv:2405.17800 (2024), Moments of the Riemann zeta function, Problem (5) on p. 6 (N. Ng: improve Chandee's Theorem 1.2), which records that Curran solved the problem.
- M. J. Curran, *Correlations of the Riemann zeta function*, Mathematika 70 (2024), no. 4, e12268, arXiv:2303.10123, Theorem 1.1, <https://doi.org/10.1112/mtk.12268>.
