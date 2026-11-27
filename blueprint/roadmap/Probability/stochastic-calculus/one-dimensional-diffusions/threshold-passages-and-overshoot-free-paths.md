# Threshold passages of a one-dimensional diffusion

Let $X$ be a regular diffusion on $[0, 1]$ with scale function $S$, started at $p$, and let $0 < p < y < 1$. Assume that $S(0)$ is finite and that the endpoint $0$ is accessible, so that the first exit time from $(0, y)$ is almost surely finite and the scale ratio below is a real number; without this, the diffusion may never reach $0$ and the formulas below need limits through interior levels $\varepsilon \downarrow 0$. By Karlin and Taylor (1981, Chapter 15) the probability of reaching $y$ before $0$ is $h(p) = (S(p) - S(0))/(S(y) - S(0))$, and, on the interval $(0, y)$, the path stopped at the first exit time $T$ from $(0, y)$ has Green's function $G_{0,y}$. Since the paths are continuous, the threshold is reached exactly, without overshoot, and $T$ is then the first arrival time at $y$. The moments of the arrival time on the event $\{X_T = y\}$ are the case $c = 0$, $d = y$, $g = 1$ of the exit-weighted path functionals between prescribed frequencies; in particular

$$E_p[T;\ X_T = y] = \int_0^yG_{0,y}(p, \xi)\,h(\xi)\,d\xi,$$

and division by $h(p)$ gives the moments of the arrival time conditioned on reaching $y$ before loss. The conditioned path is the Doob $h$-transform of the stopped diffusion, whose drift gains the term $V\,\partial_x\log h$ with $V$ the infinitesimal variance (Zhao, Lascoux, Overall and Waxman 2013, Appendix A, equation (A2) with $h$ in place of the fixation probability). These forward first-arrival quantities differ from retrospective allele ages, which condition on the present frequency of an allele of unknown origin time rather than on a future arrival.

## Depends on

- [Path functionals between prescribed frequencies](../../../Probability/stochastic-calculus/one-dimensional-diffusions/functionals-between-prescribed-frequencies.md)
- [The scale-function ratio does not depend on the base point](../../../Biology/population-genetics/diffusion-theory/scale-and-speed-of-one-dimensional-diffusions/fixation-prob-eq-ratio-scale-function-fr.md)
- [Dirichlet Green's function of a one-dimensional diffusion](../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/green-function.md)
- [Mean age of an allele at a given frequency](../../../Biology/population-genetics/diffusion-theory/allele-age-and-the-maruyama-effect/mean-age.md)
- [Scale function of a one-dimensional diffusion](../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/scale-function.md)

## Expansion

1. Hitting probabilities of interior thresholds from the scale function.
2. The diffusion stopped at $0$ and $y$ and its Green's function $G_{0,y}$, as in Karlin and Taylor (1981, Chapter 15) on $(0, y)$, obtained from the $[0, 1]$ form by restricting the diffusion to the subinterval and not the $[0, 1]$ formula itself; and the Doob conditioning on reaching $y$.
3. The conditioned moments of the first-arrival time as the case $g = 1$ of the exit-weighted functionals.
4. The comparison with the retrospective mean age of an allele observed at frequency $y$.

## Sources

- S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press, New York (1981), Chapter 15 (exit probabilities from the scale function and the Green's function of the diffusion stopped on leaving an interval).
- S. Zhao, M. Lascoux, A. D. J. Overall and D. Waxman, The characteristic trajectory of a fixing allele: a consequence of fictitious selection that arises from conditioning, Genetics 195 (2013), 993–1006, Appendix A. <https://doi.org/10.1534/genetics.113.156059>
- R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed., Springer, New York (2008), Chapter 7, Sections 7.3–7.7 (the diffusion facts cited above from Karlin and Taylor, Chapter 15). <https://doi.org/10.1007/978-0-387-78168-6>
