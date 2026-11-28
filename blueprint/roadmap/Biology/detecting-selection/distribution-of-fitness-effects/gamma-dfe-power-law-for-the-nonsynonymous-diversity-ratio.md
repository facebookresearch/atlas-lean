# Gamma-DFE power law for the nonsynonymous-to-synonymous diversity ratio

Under the Poisson random field model with scaled mutation rate $\theta$ and scaled genic selection $\sigma = 2Ns$, the expected heterozygosity contributed by sites with selection $\sigma$, relative to neutral sites, is

$$h(\sigma) = \frac{\int_0^1 2x(1-x)\,\varphi_{\theta,\sigma}(x)\,dx}{\int_0^1 2x(1-x)\,\varphi_{\theta,0}(x)\,dx} = \frac{2}{1 - e^{-2\sigma}} - \frac1\sigma \quad (\sigma \ne 0), \qquad h(0) = 1.$$

For a deleterious mutation write $y = 2N|s| > 0$, so $h(-y) = \dfrac1y - \dfrac{2}{e^{2y} - 1}$, and $0 < h(-y) \le \min(1, 1/y)$. Suppose synonymous sites are neutral, nonsynonymous sites have the same mutation rate, and every nonsynonymous mutation is deleterious with $|s|$ following the [gamma DFE](gamma-dfe.md) of shape $a > 0$ and rate $r > 0$ (fixed, independent of $N$). Define

$$\frac{\pi_N}{\pi_S}(N) = \int_0^\infty h(-2Nx)\,\frac{r^a x^{a-1} e^{-rx}}{\Gamma(a)}\,dx.$$

**Proposition.** If $0 < a < 1$, then

$$N^a\,\frac{\pi_N}{\pi_S}(N) \longrightarrow \frac{(r/2)^a}{\Gamma(a)} \int_0^\infty y^{a-1}\,h(-y)\,dy \in (0, \infty) \qquad (N \to \infty),$$

so $\log(\pi_N/\pi_S) = -a \log N + C + o(1)$: the slope of $\log(\pi_N/\pi_S)$ against $\log N$ (or against $\log \pi_S$ when $\pi_S \propto N$ with a constant mutation rate) is minus the gamma shape parameter. If $a \ge 1$ the integral diverges at infinity and the decay of $\pi_N/\pi_S$ is no longer $N^{-a}$.

## Depends on

- [Gamma distribution of fitness effects](gamma-dfe.md)
- [Sawyer–Hartl Poisson random field density](../../population-genetics/diffusion-theory/poisson-random-field-model/prf-density.md)

## Expansion

With $\varphi_{\theta,\sigma}(x) = \theta u_\sigma(1-x)/(x(1-x))$, the heterozygosity is $2\theta\int_0^1 u_\sigma(v)\,dv = 2\theta\bigl[(1 - e^{-2\sigma})^{-1} - (2\sigma)^{-1}\bigr]$, which tends to $\theta$ as $\sigma \to 0$; this gives $h$. Since $e^{2y} - 1 > 2y$, $h(-y) > 0$, and $h(-y) \le 1/y$ is immediate; $h(-y) \le 1$ follows from $u_{-y}(v) \le v$. The substitution $y = 2Nx$ gives $N^a\,\pi_N/\pi_S = \frac{(r/2)^a}{\Gamma(a)}\int_0^\infty y^{a-1} h(-y)\, e^{-ry/(2N)}\,dy$; the factor $e^{-ry/(2N)}$ increases to $1$, and monotone convergence applies because $\int_0^\infty y^{a-1}\min(1, 1/y)\,dy = 1/a + 1/(1-a) < \infty$ for $0 < a < 1$. Chen, Glémin and Lascoux (2020) test this relation, due to Welch, Eyre-Walker and Waxman (2008), across 59 species and find slopes steeper than $-a$, which they attribute to linked positive selection lowering $\pi_S$ more than $\pi_N/\pi_S$.

## Sources

- J. Chen, S. Glémin and M. Lascoux, "From drift to draft: how much do beneficial mutations actually contribute to predictions of Ohta's slightly deleterious model of molecular evolution?", Genetics (2020), <https://doi.org/10.1534/genetics.119.302869>, PMCID PMC7153929 (equations (1a)–(1b) and the among-species regressions). The limit and its constant are derived above.
