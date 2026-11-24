# Ancestral selection graph and duality for the selected diffusion

Here $M = 2N$ is the number of gene copies, time is measured in units of $M$ generations, $\sigma = 2Ns$, and the Wright–Fisher diffusion with genic selection has generator $Lf = \frac12x(1-x)f'' + \sigma x(1-x)f'$ on $[0, 1]$ with absorbing endpoints. Write $Y = 1 - X$ for the frequency of the disfavoured allele. By the [selection duality](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/generator-one-sub-pow.md), $L[(1 - x)^n] = \binom n2\bigl((1 - x)^{n-1} - (1 - x)^n\bigr) + n\sigma\bigl((1 - x)^{n+1} - (1 - x)^n\bigr)$, the generator of the line-counting process $K_t$ of the ancestral selection graph applied to $n \mapsto (1 - x)^n$. The process-level duality is $E_y[Y_t^{\,n}] = E_n[y^{K_t}]$ for all $n \ge 1$, $y \in [0, 1]$ and $t \ge 0$, where $K$ jumps from $k$ to $k - 1$ at rate $\binom k2$ (coalescence) and from $k$ to $k + 1$ at rate $\sigma k$ (branching) (Krone and Neuhauser 1997, as presented by Etheridge in her lectures on selection). The sampling interpretation is that $n$ genes sampled at time $t$ are all of the disfavoured type if and only if all their ancestors in the graph at time $0$ are. The target is this process-level duality: non-explosion of $K$ (for large $k$, coalescence dominates branching), the integrability conditions of the general duality theorem, and the sampling interpretation.

## Depends on

- [Selection duality](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/generator-one-sub-pow.md)
- [Generator of the ancestral selection graph line-counting process](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/asg-generator.md)

## Expansion

1. The branching–coalescing graph and its line-counting process, with [generator](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/asg-generator.md) and [stationary law](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/asg-stationary.md).
2. Non-explosion and positive recurrence of the line-counting process.
3. The generator identity for $H(y, n) = y^n$ with the rates above.
4. The duality from the generator identity, via the general duality theorem with its integrability conditions, and the sampling interpretation.

## Sources

- Original result: S. M. Krone and C. Neuhauser, Ancestral processes with selection, Theor. Popul. Biol. 51 (1997), 210–237. <https://doi.org/10.1006/tpbi.1997.1299> The duality follows Etheridge's lectures on selection.
- A. Etheridge, Some mathematical models from population genetics III: Adding selection, lecture notes, University of Oxford.
