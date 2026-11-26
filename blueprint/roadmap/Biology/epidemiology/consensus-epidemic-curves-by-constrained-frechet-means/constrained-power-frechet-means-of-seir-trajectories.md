# Existence, uniqueness and robustness of constrained power Fréchet means of SEIR trajectories

**Constrained power Fréchet mean.** For objects $u_1,\dots,u_J$ in a metric space $(\Omega,d)$, a constraint set $C \subset \Omega$ and $q > 0$, a constrained power Fréchet mean is

$$\hat u_q \in \arg\min_{u\in C}\ \frac1J\sum_{j=1}^J d(u,u_j)^q .$$

$q = 2$ gives the (constrained) Fréchet mean and $q = 1$ the geometric median.

**Proposition.**

1. If $C$ is non-empty and compact, a minimizer exists. If $\Omega$ is a Hilbert space with $d(u,v) = \|u - v\|$ and $C$ is non-empty, closed and convex, a minimizer exists. If moreover the objects $u_j(\theta)$ depend continuously on a parameter $\theta$ in a compact $\Theta \subset \mathbb R^p$ and the constraint correspondence $\theta \mapsto \mathcal C(\theta)$ has non-empty values and a weakly sequentially closed graph, then a joint minimizer $(\hat u_q,\hat\theta)$ exists.
2. (Uniqueness) In a Hilbert space with $C$ closed, convex and non-empty, the minimizer is unique when $q > 1$.
3. (Robustness for $q = 1$) In the same setting with $J \ge 3$, fix $u_1,\dots,u_{J-1}$ and let $u_J^{(n)}$ be arbitrary with $\|u_J^{(n)}\| \to \infty$. Then the minimizers $\hat u_1^{(n)}$ remain bounded: one outlier cannot carry the median away.

**SEIR consensus curve.** Let $\mathcal Y = H^1([0,T])^2$ hold pairs $y = (E,I)$ of exposed and infectious trajectories, with the $H^1$ distance. Given $J$ reported trajectories $y_j$ and shifts $(\mathcal T_\delta y_j)(t) = y_j^{\rm ext}(t + \delta)$, consider the feasible set $\mathcal F$ of $(y,\sigma,\gamma,\boldsymbol\delta)$ with $\sigma \in [\sigma_{\min},\sigma_{\max}]$, $\gamma \in [\gamma_{\min},\gamma_{\max}]$ ($0 < \sigma_{\min}$, $0 < \gamma_{\min}$), shifts $\delta_j \in [-\delta_{\max},\delta_{\max}]$ with $\sum_j\delta_j = 0$, and

$$E \ge 0, \quad I \ge 0, \quad N - E - I - \gamma\int_0^t I(s)\,ds \ge 0, \quad I' = \sigma E - \gamma I \ \text{ on } [0,T].$$

The consensus curve is $(\hat y_q,\hat\sigma,\hat\gamma,\hat{\boldsymbol\delta}) \in \arg\min_{\mathcal F}\frac1J\sum_j d(y,\mathcal T_{\delta_j}y_j)^q$.

**Corollary.** For every $q > 0$, $\mathcal F \ne \emptyset$ and a consensus curve exists; it determines a full SEIR state $(S,E,I,R)$ with $R = \gamma\int_0^\cdot I$ and $S = N - E - I - R$. For $q = 1$ the consensus curve stays bounded in $\mathcal Y$ when one input curve diverges.

## Expansion

Existence uses weak lower semicontinuity of $u \mapsto \|u - u_j\|^q$ and weak compactness of bounded closed convex sets (or a weakly closed graph over a compact parameter set); for the SEIR feasible set, the linear ODE constraint and the integral inequality are preserved under weak $H^1$ limits because $H^1([0,T])$ embeds compactly into $C([0,T])$. Uniqueness for $q > 1$ follows from strict convexity of $\|\cdot\|^q$ in a Hilbert space. For $q = 1$, the objective grows like $\frac1J\big(\|u - u_J^{(n)}\| + \sum_{j<J}\|u - u_j\|\big)$; the triangle inequality shows that moving toward the outlier gains at most $1/J$ per unit distance while losing $(J-1)/J$, so for $J \ge 3$ the minimizer stays in a bounded set.

## Sources

- Yui Tomo, Shu Tamano, Daisuke Yoneoka, "Estimating Consensus Epidemic Trajectories via a Constrained Power Fréchet Mean with Functional Time Registration", arXiv (2026). Propositions 3.1–3.3, definition of the feasible set and consensus curve, Corollaries 4.1–4.2. <https://doi.org/10.48550/arXiv.2605.10069>
