# Non-swapping velocity of a swelling medium and its Laplace–Beltrami tangential part

**Setting.** Let the packed density $n(x,t) = \tau(x,t)^{-1}\mathbf{1}_{\Omega_N(t)}$ be the equilibrium of $N$ non-overlapping particles of volume $\tau(x,t)$ in a confining effective potential $W(x,t)$, where $\Omega_N(t) = \{0 \le W(\cdot,t) \le U_N(t)\}$. Let $\pi(x,t) = \int_{\{W(\cdot,t) \le W(x,t)\}}\tau^{-1}\,dy$ be the number of particles enclosed by the level set through $x$; its level sets $\Sigma_p(t) = \{\pi(\cdot,t) = p\}$, $p \in (0,N)$, are the potential level sets labeled by enclosed particle number, with outward normal $\nu = \nabla\pi/|\nabla\pi|$. The **non-swapping** heuristic says particles never exchange positions, so each particle stays on the surface enclosing the same number of particles.

**Theorem (normal velocity).** The surface $\Sigma_p(t)$ moves with normal speed $w_\perp = -\partial_t\pi/|\nabla\pi|$. Any velocity field $v$ with $v\cdot\nu = w_\perp$ satisfies the continuity equation $\partial_t n + \nabla\cdot(nv) = 0$ in the averaged sense

$$ \big\langle \delta\circ(\pi(\cdot,t) - p),\ \partial_t n + \nabla\cdot(nv) \big\rangle = 0 \qquad \text{for all } t > 0,\ p \in (0,N). $$

**Theorem (tangential velocity).** Writing $v = w_\perp\nu + v_\parallel$, full mass conservation imposes on each $\Sigma_p(t)$

$$ \nabla\cdot(\tau^{-1}v_\parallel) = f, \qquad f := -\partial_t\tau^{-1} - \nabla\cdot(\tau^{-1}w_\perp\nu), $$

where $f$ has zero average on each level surface. Selecting $v_\parallel$ by minimal parallel kinetic energy on each $\Sigma_p(t)$ forces $v_\parallel = -\nabla_\parallel\theta$ (surface gradient), with $\theta$ solving

$$ -\nabla_\parallel\cdot(\tau^{-1}\nabla_\parallel\theta) = f \ \text{ on } \Sigma_p(t), \qquad \langle\delta\circ(\pi - p), \theta\rangle = 0 . $$

This weighted Laplace–Beltrami problem has a unique solution, with $\theta \in C^0\big((0,N)\times(0,\infty); H^1(\Sigma_p(t))\big)$. Under spherical symmetry $\theta = 0$ and the motion is purely normal; in general $d \ge 2$, $v_\parallel \ne 0$.

The resulting velocity, normal part tied to level-set motion and tangential part given by a Laplace–Beltrami inversion on each level set, has a geometric structure that a Darcy law $v = -\nabla p$ does not produce.

## Expansion

The normal speed of a level set of $\pi$ follows by differentiating $\pi(X(t'),t') = p$ along the normal ray. Non-swapping fixes only the normal component, because particles may slide along their level surface without changing the number enclosed. Mass balance restricted to the surface gives the divergence constraint on $v_\parallel$, which leaves a whole affine family. Minimizing $\int_{\Sigma_p}\tau^{-1}|v_\parallel|^2$ under that constraint gives, through a Lagrange multiplier, a surface gradient. Coercivity comes from the spectral gap of the Laplace–Beltrami operator on the closed surface $\Sigma_p(t)$ (the zero eigenvalue is simple, with constant eigenfunctions), and Lax–Milgram then gives existence and uniqueness on the zero-average subspace.

## Depends on

- [Packing equilibrium of an incompressible swelling medium under confinement](packing-equilibrium-of-an-incompressible-swelling-medium-under-confinement.md)

## Sources

- Pierre Degond, Marina A. Ferreira, Sara Merino-Aceituno and Mickaël Nahon, "A new continuum theory for incompressible swelling materials", arXiv:1707.02166 (2017), Section 4 (Lemma 4.2, Theorem 4.8), Section 5 (Theorem 5.3, Proposition 5.4), <https://doi.org/10.48550/arXiv.1707.02166>.
