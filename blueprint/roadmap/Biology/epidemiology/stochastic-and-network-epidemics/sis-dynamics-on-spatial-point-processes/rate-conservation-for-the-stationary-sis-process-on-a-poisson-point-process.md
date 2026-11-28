# Rate conservation for the stationary SIS process on a Poisson point process

Individuals are the points of a homogeneous Poisson point process of intensity $\lambda$ in $\mathbb R^2$, possibly moving. Each infected point recovers at rate $\beta$. A susceptible point at the origin is infected at rate $\alpha I_\Phi(0)$, where $I_\Phi(0)$ is the number of infected points within distance $a$ (so the mean number of neighbours is $\mu=\lambda\pi a^2$). In a stationary regime, let $\Phi$ and $\Psi$ be the point processes of infected and susceptible individuals, $p$ the steady-state fraction infected, and $\mathbb E^0_\Psi$ the Palm expectation at a typical susceptible point. Then, by the rate conservation principle (stationary infection flux equals recovery flux),

$$
p\,\beta=(1-p)\,\alpha\,\mathbb E^0_\Psi\big[I_\Phi(0)\big],
$$

where the paper absorbs $\alpha$ into the infection-rate functional $I_\Phi$.

**Conditional threshold bound.** Under the *repulsion conjecture* $\mathbb E^0_\Psi[I_\Phi(0)]\le\mathbb E[I_\Phi(0)]$ (a typical susceptible sees no more infection than a typical location), this gives $p\le1-\beta/(\alpha\mu)$ whenever $p>0$, and therefore the critical recovery rate satisfies

$$
\beta_c\le\alpha\mu .
$$

This is the mean-field threshold: survival requires the infection rate times the mean degree to exceed the recovery rate.

## Proof sketch

In steady state the mean rate at which infected points recover, $\lambda p\beta$ per unit area, equals the mean rate at which susceptibles become infected, $\lambda(1-p)$ times the Palm-average infection rate seen by a susceptible. Conservation equations of the same kind for second moment measures give integral equations for the pair correlation functions under random-waypoint mobility. Closing them needs a heuristic factorization of the third moment measure. The resulting phase diagrams, including that lower mobility does not always favour extinction, are heuristic and not part of this node.

## Sources

- François Baccelli and Nithin Ramesan, "A computational framework for evaluating the role of mobility on the propagation of epidemics on point processes", *Journal of Mathematical Biology* 84 (2022), 4, <https://doi.org/10.1007/s00285-021-01692-1>. Preprint version: arXiv:2009.08515 (2020), Section 3 (Lemma 1, repulsion conjecture, Lemma 2), <https://doi.org/10.48550/arXiv.2009.08515>.
