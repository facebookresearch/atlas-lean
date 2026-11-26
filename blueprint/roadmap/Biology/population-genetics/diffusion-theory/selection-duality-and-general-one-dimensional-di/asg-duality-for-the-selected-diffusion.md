# Ancestral selection graph and duality for the selected diffusion

Here $M = 2N$ is the number of gene copies, time is measured in units of $M$ generations, $\sigma = 2Ns$, and the Wright–Fisher diffusion with genic selection has generator $Lf = \frac12x(1-x)f'' + \sigma x(1-x)f'$ on $[0, 1]$ with absorbing endpoints. Write $Y = 1 - X$ for the frequency of the disfavored allele. By the [selection duality](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/generator-one-sub-pow.md), $L[(1 - x)^n] = \binom n2\bigl((1 - x)^{n-1} - (1 - x)^n\bigr) + n\sigma\bigl((1 - x)^{n+1} - (1 - x)^n\bigr)$, the generator of the line-counting process $K_t$ of the ancestral selection graph applied to $n \mapsto (1 - x)^n$. The process-level duality is $E_y[Y_t^{\,n}] = E_n[y^{K_t}]$ for all $n \ge 1$, $y \in [0, 1]$ and $t \ge 0$, where $K$ jumps from $k$ to $k - 1$ at rate $\binom k2$ (coalescence) and from $k$ to $k + 1$ at rate $\sigma k$ (branching) (Baake and Wakolbinger 2018, Proposition 1, equation (7), with mutation rate $\vartheta = 0$, so that their killed graph is never killed or pruned; the graph is that of Krone and Neuhauser 1997). The sampling interpretation is that $n$ genes sampled at time $t$ are all of the disfavored type if and only if all their ancestors in the graph at time $0$ are. The target is this process-level duality: non-explosion of $K$ (for large $k$, coalescence dominates branching), the integrability conditions of the general duality theorem, and the sampling interpretation.

## Depends on

- [Selection duality](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/generator-one-sub-pow.md)
- [Generator of the ancestral selection graph line-counting process](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/asg-generator.md)

## Expansion

1. The branching–coalescing graph and its line-counting process, with [generator](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/asg-generator.md) and [stationary law](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/asg-stationary.md).
2. Non-explosion and positive recurrence of the line-counting process.
3. The generator identity for $H(y, n) = y^n$ with the rates above.
4. The duality from the generator identity, via the general duality theorem with its integrability conditions (Ethier and Kurtz 1986, Section 4.4), and the sampling interpretation.

## Sources

- Original result: S. M. Krone and C. Neuhauser, Ancestral processes with selection, Theor. Popul. Biol. 51 (1997), 210–237. <https://doi.org/10.1006/tpbi.1997.1299>
- E. Baake and A. Wakolbinger, Lines of descent under selection, J. Stat. Phys. 172 (2018), 156–174, <https://doi.org/10.1007/s10955-017-1921-9>, Section 4, equation (6) and Proposition 1.
- S. N. Ethier and T. G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, New York, 1986, Section 4.4.
