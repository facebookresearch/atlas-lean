# Path functionals between prescribed frequencies

Let $X$ be a regular diffusion on $[0, 1]$ with drift $\mu$, infinitesimal variance $\sigma^2$, scale function $S$ and speed density $m$, and let $0 \le c < p < d \le 1$ with $c$ and $d$ accessible. Stop the path at the first exit time $T$ from $(c, d)$; both $c$ and $d$ are stopping (killing) boundaries for the functional, and the side of exit is the observation. By Karlin and Taylor (1981, Chapter 15) the path started at $p$ leaves at $d$ with probability $h(p) = (S(p) - S(c))/(S(d) - S(c))$, and, on the interval $(c, d)$, $E_p\int_0^Tg(X_s)\,ds = \int_c^dG_{c,d}(p, \xi)\,g(\xi)\,d\xi$, where $G_{c,d}$ is their Green's function with endpoints $c$ and $d$.

The functionals conditioned on the exit side follow by the Markov property: on $\{s < T\}$ the conditional probability of exit at $d$ given the path up to $s$ is $h(X_s)$, so

$$E_p\Bigl[\int_0^Tg(X_s)\,ds;\ X_T = d\Bigr] = \int_c^dG_{c,d}(p, \xi)\,g(\xi)\,h(\xi)\,d\xi,$$

and dividing by $h(p)$ gives the mean conditioned on exit at $d$; exit at $c$ uses $1 - h$. Iterating the same step, the $n$-th moment of $A = \int_0^Tg(X_s)\,ds$ on the event of exit at $d$ is $n!$ times the $n$-fold integral of $G_{c,d}(p, \xi_1)g(\xi_1)G_{c,d}(\xi_1, \xi_2)g(\xi_2)\cdots G_{c,d}(\xi_{n-1}, \xi_n)g(\xi_n)h(\xi_n)$. The conditioned path is the Doob $h$-transform of the killed diffusion; Zhao, Lascoux, Overall and Waxman (2013, Appendix A, equations (A1)–(A3)) show that such conditioning adds $V\,\partial_x\log h$ to the drift, with $V$ the infinitesimal variance. Maruyama and Kimura (1975, abstract) compute any moment of the sum of an arbitrary function of the frequency along paths between two specified frequencies and apply it to the mean age of a mutant and to the total frequency of heterozygotes.

## Depends on

- [Dirichlet Green's function of a one-dimensional diffusion](../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/green-function.md)
- [Sojourn density conditioned on fixation](../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/conditional-green.md)
- [The scale-function ratio does not depend on the base point](../../../Biology/population-genetics/diffusion-theory/scale-and-speed-of-one-dimensional-diffusions/fixation-prob-eq-ratio-scale-function-fr.md)
- [Scale function of a one-dimensional diffusion](../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/scale-function.md)

## Expansion

1. The process stopped on leaving $(c, d)$, with $c$ and $d$ accessible, and its Green's function $G_{c,d}$ in scale and speed form, as in Karlin and Taylor (1981, Chapter 15) on $(c, d)$; it is obtained from the $[0, 1]$ form by restricting the diffusion to the subinterval (equivalently by an affine change of variable) and is not the $[0, 1]$ formula itself.
2. Exit probabilities as the scale ratio $h$ and its complement.
3. The exit-weighted mean and the $n$-th moments by iterated conditioning, and the conditional versions after division by $h(p)$ or $1 - h(p)$.
4. The limits $c \downarrow 0$ and $d \uparrow 1$ when the endpoints are accessible, recovering the fixation-conditioned sojourn density at $c = 0$, $d = 1$.

## Sources

- S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press, New York (1981), Chapter 15 (exit probabilities from the scale function and the Green's function of the diffusion stopped on leaving an interval).
- S. Zhao, M. Lascoux, A. D. J. Overall and D. Waxman, The characteristic trajectory of a fixing allele: a consequence of fictitious selection that arises from conditioning, Genetics 195 (2013), 993–1006, Appendix A. <https://doi.org/10.1534/genetics.113.156059>
- T. Maruyama and M. Kimura, Moments for sum of an arbitrary function of gene frequency along a stochastic path of gene frequency change, Proc. Natl. Acad. Sci. USA 72 (1975), 1602–1604, abstract. <https://doi.org/10.1073/pnas.72.4.1602>
