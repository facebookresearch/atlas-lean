# Weak well-posedness of the Wright–Fisher SPDE under one-sided drift bounds

Consider the stochastic heat equation with Wright–Fisher noise

$$
\partial_tu=\tfrac12\Delta u+b(u)+\sqrt{\nu\,u(1-u)}\,\dot W,
$$

for the local frequency $u(t,x)\in[0,1]$ of an allele in a continuous one-dimensional population. Here $\dot W$ is space–time white noise, $\nu>0$, and the spatial domain is one of: (i) $E=\mathbb R$; (ii) the circle $\mathbb R/\mathbb Z$; (iii) $[0,1]$ with Dirichlet boundary conditions $u(0)=u(1)=0$; (iv) $[0,1]$ with Neumann boundary conditions. The drift $b:[0,1]\to\mathbb R$ models selection, mutation or migration and is only assumed Borel measurable with

$$
-Cu\le b(u)\le C(1-u)\qquad(u\in[0,1])\ \text{for some }C<\infty,
$$

which forces $b(0)\ge0\ge b(1)$. This is essentially the necessary condition for $[0,1]$-valued solutions.

**Theorem.** For every, possibly random, Borel-measurable initial condition $u_0:E\to[0,1]$ there is a weak (Walsh mild) solution, and it is unique in law. Moreover, the law is continuous in the drift. If the drifts $b^n$ satisfy the bound with a common $C$ and $b^n\to b$ pointwise, then the corresponding solutions converge to the solution with drift $b$, locally uniformly in distribution.

So the noise regularizes: no continuity of $b$ is needed, in contrast with the deterministic reaction–diffusion equation, which can be ill-posed for discontinuous $b$.

## Expansion

For continuous $b$, the bound is equivalent to writing $b(u)=\mu(\tilde b(u)-u)$ with $\tilde b:[0,1]\to[0,1]$ continuous and either constant or polynomially bounded, $\min\{\tilde b,1-\tilde b\}\ge\min\{u,1-u\}^n$. These are exactly the functions that admit a Bernoulli factory (Keane–O'Brien). A Bernoulli factory for $\tilde b$ lets selection events be run as votes along the genealogy of a branching–coalescing particle system. This gives a moment duality between $u_t$ and the dual's voting outcomes, and the duality determines the law. Measurable drifts are handled by approximation and the continuity statement. This generalizes the earlier regularization-by-noise results for the same equation.

## Sources

- J. Koskela and O. Tough, "Well-posedness for Wright–Fisher SPDEs with measurable drift", arXiv:2609.23518 (2026), Section 1 (SPDE (eq:SPDE 1), assumption (eq:assumption on tilde b), Theorems 1.1 and 1.3) and Section 2 (Lemma 2.1, Theorem 2.3). <https://doi.org/10.48550/arXiv.2609.23518>
