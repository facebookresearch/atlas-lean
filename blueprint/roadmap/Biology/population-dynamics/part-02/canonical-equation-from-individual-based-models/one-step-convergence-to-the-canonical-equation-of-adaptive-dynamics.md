# One-step convergence of individual-based models to the canonical equation of adaptive dynamics

**Individual-based model.** An asexual population with traits in a compact $\mathcal X \subset \mathbb R$ has carrying-capacity parameter $K$ and is described by $\nu^K_t = K^{-1}\sum_i\delta_{x_i}$. An individual with trait $x$ gives birth at rate $b(x)$ and dies at rate $d(x) + \sum_j c(x,x_j)/K$ (logistic competition). With probability $u_K m(x)$ a birth is mutant, with trait $x + \sigma_K h$, where $h \in \mathbb Z$ has law $M(x,dh)$ (finitely supported); otherwise the child is a clone. Assume $b,d,c$ bounded, $b(x) - d(x) > 0$, $c(x,x) \ge \underline c > 0$, plus the regularity conditions of the paper. The monomorphic equilibrium density is $\bar z(x) = (b(x) - d(x))/c(x,x)$ and the **invasion fitness** of a mutant $y$ in an $x$-resident population is

$$f(y,x) = b(y) - d(y) - c(y,x)\,\bar z(x),$$

so $f(x,x) = 0$. Assume $\partial_1 f(x,x) \ne 0$ for all $x$, which rules out coexistence and branching.

**Theorem.** Suppose that for some small $\alpha > 0$, as $K \to \infty$,

$$K^{-1/2+\alpha} \ll \sigma_K \ll 1, \qquad \exp(-K^\alpha) \ll u_K \ll \frac{\sigma_K^{1+\alpha}}{K\ln K}.$$

Start from a monomorphic population at trait $x_0$ with $N^K_0/K \to \bar z(x_0)$ in law and bounded in $L^p$ for some $p > 1$. Then for every $T > 0$ the rescaled processes $\big(\nu^K_{t/(Ku_K\sigma_K^2)}\big)_{0\le t\le T}$ converge in probability in the Skorokhod topology on $\mathbb D([0,T],\mathcal M(\mathcal X))$ to $\bar z(x_t)\,\delta_{x_t}$, where $x_t$ solves the **canonical equation of adaptive dynamics**

$$\frac{dx_t}{dt} = \int_{\mathbb Z} h\,\big[h\,m(x_t)\,\bar z(x_t)\,\partial_1 f(x_t,x_t)\big]_+\,M(x_t,dh), \qquad x_{t=0} = x_0.$$

Large population, rare mutation and small mutation steps are taken simultaneously rather than successively, under conditions keeping birth–death and invasion time scales separated.

## Depends on

- [Fitness gradient](../../classification-of-adaptive-dynamics-singular-str/fitness-gradient.md)

## Expansion

Each mutant invasion has three phases: a branching-process phase in which the mutant reaches density of order $\sigma_K$ with probability $\approx [\sigma_K h\,\partial_1 f(x,x)]_+/b$, a Lotka–Volterra phase of duration $O(\ln K/\sigma_K)$ in which mutant and resident exchange, and a final phase in which the resident goes extinct; the conditions on $u_K$ ensure that no further mutant appears before the invasion is complete. Because $\sigma_K \to 0$, the competitive Lotka–Volterra dynamics are nearly degenerate and fixation takes a diverging time, so the law of large numbers over a fixed horizon used in successive-limit proofs fails; the proof instead controls the stochastic system directly near the slow manifold. Summing trait jumps of size $\sigma_K h$ at rate $Ku_Km\,b\,\bar z$ times the invasion probability over the time scale $1/(Ku_K\sigma_K^2)$ yields the canonical-equation drift.

## Sources

- Martina Baar, Anton Bovier, Nicolas Champagnat, "From stochastic, individual-based models to the canonical equation of adaptive dynamics – in one step", arXiv (2015). Section 2 (model, Assumption 1), Section 3 (Definitions 3.3–3.5, Proposition 3.6), Section 4 (Assumption 3, Theorem 4.1), Section 6 (first invasion phase). <https://doi.org/10.48550/arXiv.1505.02421>. Published version: The Annals of Applied Probability 27(2) (2017), 1093–1170, <https://doi.org/10.1214/16-aap1227>; locators above refer to the arXiv version.
