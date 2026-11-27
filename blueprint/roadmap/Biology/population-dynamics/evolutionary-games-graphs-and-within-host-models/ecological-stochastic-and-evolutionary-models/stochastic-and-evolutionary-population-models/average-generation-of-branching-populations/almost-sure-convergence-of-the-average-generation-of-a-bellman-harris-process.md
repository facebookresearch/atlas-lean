# Almost-sure convergence of the average generation of a Bellman–Harris process

**Setting.** In a supercritical Bellman–Harris process, each individual lives for an independent lifetime $L$ (non-lattice distribution) and at death produces $N$ offspring, with $h = \mathbb{E}N > 1$ and $v = \mathbb{E}N(N-1) < \infty$. Let $Z(t)$ be the number of individuals alive at time $t$, $G(t)$ the sum of their generation numbers (the number of ancestors of each individual, summed), and $\alpha > 0$ the Malthusian parameter, $h\int_0^\infty e^{-\alpha u}\,d\mathbb{P}(L\le u) = 1$. Then $Z(t)e^{-\alpha t} \to c\,\mathcal{W}_Z$ a.s. and in $L^2$, with $\mathbb{E}\mathcal{W}_Z = 1$ and

$$c = \frac{h-1}{h^2\alpha\int_0^\infty u e^{-\alpha u}\,d\mathbb{P}(L\le u)},\qquad \alpha' = \frac{1}{h^2\int_0^\infty u e^{-\alpha u}\,d\mathbb{P}(L\le u)} .$$

**Theorem ($L^2$ convergence).** $\mathcal{W}_G(t) = G(t)/(c\,h\alpha'\,t e^{\alpha t})$ converges in $L^2$ to a nonnegative $\mathcal{W}_G$ with $\mathbb{E}\mathcal{W}_G = 1$ and

$$\operatorname{Var}(\mathcal{W}_G) = \frac{(v+h)\int_0^\infty e^{-2\alpha u}d\mathbb{P}(L\le u) - 1}{1 - h\int_0^\infty e^{-2\alpha u}d\mathbb{P}(L\le u)} > 0 .$$

**Theorem (same randomness).** $\mathcal{W}_G = \mathcal{W}_Z$ almost surely: the population size and the total generation share the same random limit.

**Theorem (almost-sure convergence).** If $\int_0^\infty \mathbb{E}\big[(\mathcal{W}_G(t) - \mathcal{W}_Z)^2\big]\,dt < \infty$, then $\mathcal{W}_G(t) \to \mathcal{W}_Z$ almost surely. Consequently, if moreover $\mathbb{E}N^2 < \infty$,

$$\lim_{t\to\infty}\frac{G(t)}{t\,Z(t)} = h\alpha' = -\lim_{p\to0}\lim_{t\to\infty}\frac{1}{pt}\log\frac{Z^+(t)}{Z(t)}\quad\text{a.s.},$$

where $Z^+(t)$ counts individuals still carrying a neutral heritable label that each newborn loses irreversibly with probability $p$ (assuming $\liminf_t Z^+(t) > 0$). So the average generation grows linearly at rate $h\alpha'$ along almost every surviving path, and it can be read off from the decay of a one-way neutral label.

## Expansion

The joint generating function of $(G(t), G(t+\tau), Z(t), Z(t+\tau))$ satisfies a renewal-type integral equation obtained by conditioning on the ancestor's lifetime. Second moments then solve renewal equations with a defective measure $h^2\int e^{-2\alpha u}dP(L\le u) \cdot$(normalized), and a uniform-in-$\tau$ renewal theorem shows $\mathcal{W}_G(t)$ is Cauchy in $L^2$, giving the limit and its variance. Computing $\mathbb{E}[(\mathcal{W}_G - \mathcal{W}_Z)^2] = 0$ from the same asymptotics identifies the limits. Almost-sure convergence follows from the integrability condition by a Borel–Cantelli argument on a grid plus control of fluctuations between grid points. With label loss probability $p$, the labelled subpopulation is a Bellman–Harris process with mean offspring $h(1-p)$, whose Malthusian parameter is $\alpha - p\,h\alpha' + o(p)$.

## Sources

- Gianfelice Meli, Tom S. Weber and Ken R. Duffy, "Sample path properties of the average generation of a Bellman–Harris process", Journal of Mathematical Biology 79 (2019), 673–704, <https://doi.org/10.1007/s00285-019-01373-0>; numbering as in arXiv:1807.07031: Proposition 2, Theorems 2–4 and Corollary 3 (Section 3).
