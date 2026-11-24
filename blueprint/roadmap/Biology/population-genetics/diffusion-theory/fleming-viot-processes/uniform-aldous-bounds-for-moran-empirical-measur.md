# Uniform Aldous bounds for Moran empirical-measure projections

Let $E$ be a compact metric space, $B f(x) = \int (f(y) - f(x))\, \kappa(x, dy)$ a bounded jump-type mutation generator with total rate at most $\lambda < \infty$, and $\mu^N$ the empirical measure of the [Moran system of $N$ particles](moran-particle-system-with-feller-mutation-on-a.md), in which each ordered pair resamples at rate $1/2$. For $f \in C(E)$,

$$\langle f, \mu^N_t \rangle = \langle f, \mu^N_0 \rangle + \int_0^t \langle Bf, \mu^N_s \rangle\, ds + M^{N,f}_t,$$

where $M^{N,f}$ is a càdlàg square-integrable martingale whose [predictable quadratic variation](../../../../Probability/martingales/stopping-times-and-martingale-problems/predictable-quadratic-variation-of-dynkin-martin.md) has a density $\Gamma_N(f)$ with

$$\Gamma_N(f) \le \frac{4 \lambda \|f\|^2}{N} + 2\|f\|^2:$$

the mutation of each of the $N$ particles contributes at most $\lambda (2\|f\|)^2 / N^2$, and resampling contributes $\sum_{i \ne j} \frac12 \bigl(f(x_i) - f(x_j)\bigr)^2 / N^2 \le 2\|f\|^2$. Hence for every bounded stopping time $\tau$ and $\delta > 0$,

$$\mathbb E\bigl|\langle f, \mu^N_{\tau + \delta} \rangle - \langle f, \mu^N_\tau \rangle\bigr|^2 \le 2\|Bf\|^2 \delta^2 + 2(4\lambda + 2)\|f\|^2 \delta,$$

uniformly in $N \ge 1$, and every jump of $\langle f, \mu^N \rangle$ has size at most $2\|f\|/N$. Applied to a countable dense family of $f \in C(E)$, with $\mathcal M_1(E)$ compact, these bounds verify the [Aldous tightness criterion](../../../../Probability/convergence-of-measures/skorokhod-space/aldous-tightness-criterion-in-d-0-t-e-with-initi.md). Since $\mathcal D(B) = C(E)$, no core is needed. The increment bound is essential: deterministic continuous paths such as $\sin(nt)$ have no jumps and are not tight.

## Depends on

- [Moran particle system with Feller mutation on a compact type space](moran-particle-system-with-feller-mutation-on-a.md)
- [Predictable quadratic variation of Dynkin martingales for bounded-generator jump processes](../../../../Probability/martingales/stopping-times-and-martingale-problems/predictable-quadratic-variation-of-dynkin-martin.md)
- [Aldous tightness criterion in D([0,T],E) with initial and compact-containment conditions](../../../../Probability/convergence-of-measures/skorokhod-space/aldous-tightness-criterion-in-d-0-t-e-with-initi.md)

## Expansion

A full proof page must still establish the semimartingale decomposition, the computation of $\Gamma_N(f)$ and the increment bound by optional stopping.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, tightness via martingale decompositions, <https://onlinelibrary.wiley.com/doi/book/10.1002/9780470316658>
