# Actuator envelope for removal control of quasi-stationary branching populations

**Model.** Individuals of a subcritical age-structured (Bellman-Harris) branching population die at age-dependent hazard $\mu(a)$ and, at death, leave $n$ offspring with probability $p_n$ (mean $m < 1$, childless probability $p_0$). The population dies out a.s.; conditioned on survival it converges to its Yaglom limit, the quasi-stationary operating point. A preventive removal (culling) control adds an age-dependent mortality $u(a) \ge 0$ that leaves the offspring law unchanged. Write $\mu_\infty$ for the large-age limit of the hazard and $\bar L = (1-p_0)\mu_\infty$.

**Structural fact.** Absorption happens only from single-individual states, through a childless death (rate $p_0\mu(a)$) or a removal (rate $u(a)$), so the killing rate is $\kappa_u(\delta_a) = p_0\mu(a) + u(a)$, while the generator of the non-absorbed dynamics does not depend on $u$. Removal changes the killing but not the Foster-Lyapunov drift.

**Theorem (actuator envelope).** Under the source's regularity hypotheses, if the controlled process admits an admissible Foster-Lyapunov certificate $(V,\lambda_1,C)$ for convergence to its quasi-stationary distribution, then

$$\sup_{a\ge0}\bigl[p_0\mu(a) + u(a)\bigr] < \lambda_1 \le (1-p_0)\mu_\infty, \qquad\text{so}\qquad u(a) < (1-p_0)\mu_\infty - p_0\mu(a) \quad \forall a \ge 0.$$

The certifiable control class is contained in $\{u \ge 0 : \|\kappa_u\|_\infty < \bar L\}$, and authority shrinks at ages where the natural childless rate is already high.

**Decay rate.** The controlled first-moment decay rate $\lambda_0(u)$ is the unique root of the Euler-Lotka equation built from the offspring intensity $m\mu(a)\bar G_u(a)$, $\bar G_u(a) = \exp\bigl(-\int_0^a(\mu + u)\bigr)$:

$$\int_0^\infty m\,\mu(a)\,\bar G_u(a)\,e^{\lambda_0(u)a}\,da = 1 .$$

Only proportional actuation $u = c\mu$ keeps the controlled process in the Bellman-Harris class, with effective offspring mean $m/(1+c)$.

## Expansion

Convergence to a quasi-stationary law is certified by a drift inequality whose rate $\lambda_1$ must exceed the maximal killing rate. Since control cannot alter the drift of the surviving population, it can only raise the killing rate, and the drift rate itself is capped by the large-age behaviour of the hazard: for old single individuals the Lyapunov function grows without bound, forcing $\lambda_1 \le (1-p_0)\mu_\infty$. The envelope is therefore a structural limit on how far culling can move the quasi-stationary equilibrium, independent of the control law; the source illustrates it numerically on foot-and-mouth disease surveillance.

## Sources

- O. Arezki, A. Zemouche, "Removal-Only Actuation in Age-Structured Branching Populations: Fundamental Limits of Equilibrium Placement" (2026), Section 3 invariance lemma, actuator-envelope theorem (Eqs. env0, envelope, envclass) and first-moment decay characterization, <https://doi.org/10.48550/arXiv.2608.10641>.
