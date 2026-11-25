# Wright–Fisher diffusions with time-dependent selection and mutation

When selection, mutation or population size change in time, the frequency follows a diffusion with time-dependent coefficients, written by Zhao, Lascoux, Overall and Waxman (2013, Appendix A, equation (A1)) as the forward equation $-\partial_tK = -\frac12\partial_x^2(VK) + \partial_x(MK)$ with infinitesimal variance $V(x, t)$ and drift $M(x, t)$, together with the probability $P_{fix}(T \mid x, t)$ that an allele at frequency $x$ at time $t$ is fixed by time $T$; the corresponding transition laws form a two-parameter evolution family rather than a semigroup. Evans, Shvets and Slatkin (2007, Section 5) treat a Wright–Fisher diffusion with constant selection and time-varying relative size $\rho(t)$, with drift $Sx(1 - x)$ and variance $x(1 - x)/\rho(t)$, and derive ordinary differential equations for the moments of the frequency density.

The part stated here concerns selection and mutation. With $V(x, t) = x(1 - x)/\nu(t)$ and drift $b_t(x) = \alpha(t)x(1 - x) + \frac12(\theta_1(t)(1 - x) - \theta_2(t)x)$ in time units of the reference size, the fixation probability by time $T$ solves the backward equation

$$\partial_tP + \frac{x(1 - x)}{2\nu(t)}\partial_x^2P + b_t(x)\,\partial_xP = 0, \qquad P(T \mid 0, t) = 0, \quad P(T \mid 1, t) = 1 \text{ when } \theta_1 = \theta_2 = 0,$$

with terminal value the indicator of $\{1\}$ at $t = T$; and running the process on the genetic clock $A(t) = \int_0^t\nu(s)^{-1}ds$, which makes the variance $x(1 - x)$, multiplies the drift by $\nu$: in genetic time the scaled selection coefficient and mutation rates at time $t$ are $\nu(t)\alpha(t)$ and $\nu(t)\theta_i(t)$, which is the chain rule $\frac{d}{du} = \nu(t)\frac{d}{dt}$ for $u = A(t)$. The definition of the time-inhomogeneous martingale problem and the deterministic clock change itself are separate statements.

## Depends on

- [Time-changed neutral diffusion under deterministic population-size change: construction and fixation](../fixation-and-absorption-in-the-wright-fisher-dif/time-changed-neutral-diffusion-under-determinist.md)
- [Fixation probability in a population of changing size](../../../../Biology/population-genetics/diffusion-theory/fixation-and-absorption-in-the-wright-fisher-dif/fixation-probability-in-a-population-of-changing-size.md)

## Expansion

1. Time-dependent drifts from selection and mutation, and the associated evolution family.
2. The backward equation for the fixation probability by time $T$ and its boundary and terminal conditions.
3. The transformation of the selection and mutation drifts under the genetic clock.
4. The moment equations of Evans, Shvets and Slatkin for constant selection and varying size.

## Sources

- S. Zhao, M. Lascoux, A. D. J. Overall and D. Waxman, The characteristic trajectory of a fixing allele: a consequence of fictitious selection that arises from conditioning, Genetics 195 (2013), 993–1006, Appendix A, equations (A1)–(A4). <https://doi.org/10.1534/genetics.113.156059>
- S. N. Evans, Y. Shvets and M. Slatkin, Non-equilibrium theory of the allele frequency spectrum, Theor. Popul. Biol. 71 (2007), 109–119, Section 5. <https://doi.org/10.1016/j.tpb.2006.06.005>
