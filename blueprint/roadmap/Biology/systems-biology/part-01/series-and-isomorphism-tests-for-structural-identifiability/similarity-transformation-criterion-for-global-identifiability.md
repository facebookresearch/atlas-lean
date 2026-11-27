# Similarity-transformation criterion for global structural identifiability

**Setting.** Consider the analytic input-affine model

$$\dot x = f(x,\theta) + \sum_{i=1}^m g_i(x,\theta)u_i,\qquad y = h(x,\theta),\qquad x(0) = x_0(\theta),$$

on an open set of $\mathbb{R}^n$, with parameter $\theta \in \Theta$. The model is *locally reduced* at $x_0(\theta)$ if it satisfies the controllability (accessibility) rank condition and the observability rank condition there.

**Criterion (local state isomorphism).** Let $\theta, \theta' \in \Theta$ be such that the model is locally reduced at $x_0(\theta)$ and $x_0(\theta')$, and let $V$ be an open neighbourhood of $x_0(\theta)$. Suppose that for every such $\theta'$, the existence of an analytic map $\lambda: V \to \mathbb{R}^n$ with $\operatorname{rank}\,\partial\lambda/\partial x = n$ on $V$ and

$$\lambda(x_0(\theta)) = x_0(\theta'),\qquad f(\lambda(x),\theta') = \frac{\partial\lambda}{\partial x}(x)\,f(x,\theta),$$

$$g_i(\lambda(x),\theta') = \frac{\partial\lambda}{\partial x}(x)\,g_i(x,\theta)\ (i = 1,\dots,m),\qquad h(\lambda(x),\theta') = h(x,\theta)\quad (x \in V)$$

forces $\theta' = \theta$. Then the model is globally structurally identifiable at $\theta$; conversely, global identifiability at $\theta$ holds only if every such $\lambda$ comes with $\theta' = \theta$.

## Expansion

By the local state isomorphism theorem, two locally reduced analytic systems produce the same input–output map exactly when their vector fields, output maps and initial states are related by a local diffeomorphism $\lambda$ as above. Identifiability is then the statement that the only parameter value admitting such an isomorphism with the model at $\theta$ is $\theta$ itself. In practice the conjugacy conditions form a system of first-order linear inhomogeneous partial differential equations for $\lambda$; when the observability rank condition holds, $\lambda$ can be shown to be linear in some formulations, which reduces the test to algebra, but checking the rank conditions and solving the PDE system becomes costly for large nonlinear models.

## Sources

- Chis OT, Banga JR, Balsa-Canto E, "Structural identifiability of systems biology models: a critical comparison of methods", PLoS One (2011), Methods: "Similarity transformation approach", Theorem 1 and conditions (10)–(14), <https://doi.org/10.1371/journal.pone.0027755>, PMCID PMC3222653.
