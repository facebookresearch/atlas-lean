# Evolutionary branching criterion with competition-induced dormancy

**Model.** In an individual-based adaptive-dynamics model with carrying capacity $K$, each individual has a trait $x$ in a compact set $\mathcal X \subset \mathbb{R}$ and is either active or dormant. Active individuals of trait $x$ reproduce at rate $\lambda(x)$ (the offspring mutating with probability $u_K m(x)$, mutation steps drawn from a kernel $M$) and die naturally at rate $\mu(x)$; an active $x$ suffers competition from each active $y$ at rate $\alpha(x,y)/K$, and at such an event it becomes dormant with probability $p(x)$ and dies otherwise. Dormant individuals die at rate $\kappa(x)$ and resuscitate at rate $\sigma(x)$. In the limit $K \to \infty$ with rare mutations ($e^{-VK} \ll u_K \ll 1/(K\log K)$ for all $V > 0$), the trait process converges, on the mutation time scale, to a polymorphic evolution sequence, and in the small-mutation limit to the canonical equation of adaptive dynamics; evolutionary branching at a singular strategy $x^*$ occurs under second-derivative conditions on the invasion fitness $f(y,x)$, generalising the criterion of Metz et al.

**Concrete model.** Take $\mathcal X = [-2,2]$, $\mu = 0$, $m(x) = m$, Gaussian mutation steps, Gaussian birth and competition kernels

$$\lambda(x) = e^{-x^2/(2\sigma_b^2)}, \qquad \alpha(x,y) = e^{-(x-y)^2/(2\sigma_\alpha^2)},$$

no dormant death ($\kappa = 0$), constant resuscitation rate $\sigma$, and dormancy probability

$$p(x) = 1 - e^{-|x|^r/(2\sigma_p^2)}, \qquad \sigma_p, r > 0 .$$

**Theorem (branching with dormancy).** Let $r = 2$ and assume the stability condition $\frac{1}{\sigma_p^2} < \frac{1}{\sigma_b^2}$. Then the trait process converges locally to the singular strategy $x^* = 0$, and evolutionary branching occurs there if

$$\frac{1}{\sigma_\alpha^2} - \frac{1}{\sigma_b^2} + \frac{1}{\sigma_p^2} > 0 .$$

Without dormancy the classical condition is $\frac{1}{\sigma_\alpha^2} - \frac{1}{\sigma_b^2} > 0$, i.e. $\sigma_\alpha < \sigma_b$; the extra positive term $1/\sigma_p^2$ means that **dormancy always enlarges the parameter range for evolutionary branching**.

## Proof sketch

Escaping competition into dormancy acts like a frequency-dependent refuge: individuals whose traits are far from the crowded centre become dormant more often instead of dying, which reduces the cost of competition for deviant traits and adds curvature $1/\sigma_p^2$ to the invasion fitness in the mutant direction. At $x^* = 0$ branching requires the singularity to be convergence stable while the invasion fitness is convex in the mutant trait (the general criterion compares second derivatives of $f$ at $(x^*,x^*)$); with Gaussian kernels and $r = 2$ both conditions reduce to comparisons of inverse squared widths.

## Sources

- Jochen Blath, Tobias Paul, András Tóbiás and Maite Wilke Berenguer, "The impact of dormancy on evolutionary branching", *Theoretical Population Biology* 156 (2024), 66–76, <https://doi.org/10.1016/j.tpb.2024.02.003>. Preprint version: arXiv:2209.01792 (2022), Section 2 (the micro-model and Theorems 2.1, 2.2 and 2.4) and Section 3.1 (Theorem 3.1), <https://doi.org/10.48550/arXiv.2209.01792>.
