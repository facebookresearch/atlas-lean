# Stick-breaking process

Let $(\Omega, \mu)$ be a measure space and $X$ a measurable space. A stick-breaking process on $(\Omega, \mu)$ consists of

- measurable proportions $\beta_0, \beta_1, \dots : \Omega \to \mathbb{R}$, with $\beta_k \in [0, 1]$ $\mu$-almost surely for each $k$;
- measurable atoms $\theta_0, \theta_1, \dots : \Omega \to X$;
- a measure $H$ on $X$, the base measure, which is the law of every atom $\theta_k$ under $\mu$;

such that the proportions are mutually independent, the atoms are mutually independent, and the sequence $(\beta_k)_k$ is independent of the sequence $(\theta_k)_k$. The laws of the proportions are arbitrary; Ishwaran and James (2001) take $\beta_k \sim \mathrm{Beta}(a_k, b_k)$, and [Sethuraman's representation of the Dirichlet process](is-dirichlet.md) takes $\beta_k \sim \mathrm{Beta}(1, \alpha)$.
