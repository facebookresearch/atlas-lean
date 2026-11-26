# Occupation measure of the transient birth–death process

**Process.** Consider the birth–death model of constitutive transcription $\varnothing \xrightarrow{\alpha} X \xrightarrow{\beta} \varnothing$ with transcription rate $\alpha > 0$ and efflux rate $\beta > 0$ (splicing, degradation or export). Its chemical master equation on $x \in \mathbb{N}_0$ is

$$\frac{dP(x; t)}{dt} = \alpha \big[P(x - 1; t) - P(x; t)\big] + \beta \big[(x + 1) P(x + 1; t) - x P(x; t)\big],$$

with $P(-1; t) = 0$. The mean $y(t)$ solves the reaction rate equation $y' = \alpha - \beta y$, so $y(t) = c\, e^{-\beta t} + \alpha / \beta$ with $c = y_0 - \alpha/\beta$.

**Fact.** If the initial law is $\mathrm{Poisson}(y_0)$, then $P(\cdot\,; t) = \mathrm{Poisson}(y(t))$ for all $t \ge 0$, i.e. the probability generating function is $G(z; t) = e^{(z - 1) y(t)}$, and $P(\cdot\,; t) \to \mathrm{Poisson}(\alpha/\beta)$ as $t \to \infty$.

**Occupation measure.** If a cell is observed at a latent process time $t$ drawn from a sampling law $f$, the probability of observing $x$ molecules is the occupation measure $P(x) = \int P(x; t)\, df(t) = \mathbb{E}_f[P(x; t)]$, and its generating function is $H(z) = \mathbb{E}_f[G(z; t)]$. For the uniform law $df = T^{-1} dt$ on $[0, T]$ and $u = z - 1$,

$$H(z) = \frac{1}{T} \int_0^T e^{u\, y(t)}\, dt = \frac{e^{u \alpha / \beta}}{\beta T} \Big[\mathrm{Ei}(u c) - \mathrm{Ei}\big(u c\, e^{-\beta T}\big)\Big],$$

where $\mathrm{Ei}$ is the exponential integral. This mixture of Poisson laws is not a standard parametric family. If instead cells are desynchronized and $T \to \infty$, the time average converges to the stationary law (ergodic theorem): $P(x) = \lim_{T \to \infty} T^{-1} \int_0^T P(x; t)\, dt = \lim_{t \to \infty} P(x; t)$.

## Expansion

The Poisson form follows by checking that $P(x; t) = y(t)^x e^{-y(t)}/x!$ satisfies the master equation whenever $y' = \alpha - \beta y$, or equivalently that $G$ satisfies the first-order PDE $\partial_t G = (z - 1)(\alpha G - \beta \partial_z G)$. Linearity of expectation passes the sampling law through the generating function. With $y(t) = c e^{-\beta t} + \alpha/\beta$ the substitution $w = u c\, e^{-\beta t}$, $dt = -dw/(\beta w)$ turns $\int_0^T \exp(u c e^{-\beta t})\, dt$ into $\beta^{-1}\int_{u c e^{-\beta T}}^{u c} e^w w^{-1}\, dw$, which is the difference of exponential integrals. The point of the construction is that sequencing has no intrinsic clock: stationary distributions are justified only when observations are unsynchronized over a long window, while transient processes such as those used for RNA velocity require the occupation measure itself.

## Sources

- G. Gorin, M. Fang, T. Chari and L. Pachter, "RNA velocity unraveled", PLoS Computational Biology 18 (2022), e1010492, section on stochastic models and occupation measures, Eqs. (8)–(16), <https://doi.org/10.1371/journal.pcbi.1010492> (PMC9499228).
