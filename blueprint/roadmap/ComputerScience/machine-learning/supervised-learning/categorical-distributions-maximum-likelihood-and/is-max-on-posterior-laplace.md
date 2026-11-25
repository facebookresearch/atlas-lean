# Laplace smoothing is a MAP estimate

Let $\alpha$ be a finite nonempty set of categories and $n : \alpha \to \mathbb{N}$ the observed counts. Under the Dirichlet prior with all concentrations equal to $2$, the add-one smoothed estimate maximizes the unnormalized posterior $\prod_a \theta_a^{n(a)} \cdot \prod_a \theta_a$ over all probability vectors $\theta$ on $\alpha$.
