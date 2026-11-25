# Maxwell's equations in a homogeneous linear medium

Let $\Omega \subseteq \mathbb R^3$ be open, $J \subseteq \mathbb R$ an open interval, and $\epsilon > 0$, $\mu > 0$ and $\sigma \ge 0$ the
permittivity, permeability and conductivity of a homogeneous isotropic linear medium filling $\Omega$. A pair of continuously
differentiable vector fields $E, H : \Omega \times J \to \mathbb R^3$ solves the source-free Maxwell equations in this medium if

$$\nabla \cdot E = 0, \qquad \nabla \cdot H = 0, \qquad \nabla \times E = -\mu \frac{\partial H}{\partial t}, \qquad
\nabla \times H = \sigma E + \epsilon \frac{\partial E}{\partial t}.$$

With $D = \epsilon E$, $B = \mu H$ and the conduction current $\sigma E$, these are Maxwell's equations with no free charge and no
impressed current. The vacuum is the case $\epsilon = \epsilon_0$, $\mu = \mu_0$, $\sigma = 0$; a lossless medium has $\sigma = 0$.
For twice continuously differentiable fields the curl equations give $\partial_t (\nabla \cdot H) = 0$ and
$\epsilon\, \partial_t (\nabla \cdot E) = -\sigma\, \nabla \cdot E$, so the divergence equations hold for all times once they hold at
one time.

## Sources

- J. D. Jackson, *Classical Electrodynamics*, 3rd edition, Wiley, 1999, Chapter 6 (the macroscopic Maxwell equations and constitutive relations).
- D. M. Pozar, *Microwave Engineering*, 4th edition, Wiley, 2012, Chapter 1 (Maxwell's equations in material media).
