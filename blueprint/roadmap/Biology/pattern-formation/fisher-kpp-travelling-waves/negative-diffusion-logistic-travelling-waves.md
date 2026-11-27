# Smooth monotone travelling waves of a logistic equation with sign-changing aggregation diffusivity

This page covers the main existence result of Li, van Heijster, Marangell and Simpson (2020) for a reaction-diffusion equation whose diffusivity becomes negative at intermediate densities (forward-backward diffusion modelling aggregation of grouped cells).

**Model.** For $U = U(x,t)$ with $x \in \mathbb{R}$, $t \ge 0$, consider

$$\frac{\partial U}{\partial t} = \frac{\partial}{\partial x}\Big( D(U) \frac{\partial U}{\partial x} \Big) + R(U), \qquad R(U) = \lambda U (1 - U),$$

$$D(U) = D_i (1 - 4U + 3U^2) + D_g (4U - 3U^2),$$

with proliferation rate $\lambda > 0$ and diffusivities of isolated and grouped agents satisfying $D_i > 4 D_g > 0$. This $D$ arises as the continuum limit of a lattice model of isolated and grouped agents (Johnston et al. 2017), here with equal proliferation rates and no death. Under $D_i > 4D_g$, $D$ is convex and

$$D(U) > 0 \ \text{on}\ [0,\alpha) \cup (\beta, 1], \qquad D(U) < 0 \ \text{on}\ (\alpha, \beta),$$

$$\alpha, \beta = \frac{2}{3} \mp \frac{\sqrt{D_i^2 + 4D_g^2 - 5 D_i D_g}}{3 (D_i - D_g)}, \qquad \tfrac13 < \alpha < \tfrac23 < \beta < 1 .$$

In particular $D(0) = D_i$ and $D(1) = D_g$.

**Theorem (Theorem 1 of the source).** For every speed

$$c \ge c^* := 2\sqrt{\lambda D_i}$$

the equation admits a smooth, monotone, nonnegative travelling wave $U(x,t) = u(x - ct)$ with $u(z) \to 1$ as $z \to -\infty$ and $u(z) \to 0$ as $z \to +\infty$.

**Complementary statements (Section 2.2).** Write $c_\beta := 2\sqrt{D'(\beta) R(\beta)}$. Then $c_\beta < c^*$ (Lemma 2), and

- for $c_\beta < c < c^*$ smooth travelling waves connecting $1$ to $0$ still exist, but they are not monotone and oscillate around $0$, so they take negative values;
- for $0 < c < c_\beta$ there are no smooth travelling waves (only shock-fronted ones may exist).

The minimal speed $c^*$ is the Fisher-KPP minimal speed for the diffusivity $D(0) = D_i$ at the invaded state: the negative-diffusion region does not change it.

The passage of the travelling-wave orbit through the singular lines $u = \alpha$ and $u = \beta$ ("holes in the wall") is justified in the source by appeal to canard theory for a regularised slow-fast system (Remark 2); the details are not written out there.

## Depends on

- [Fronts of speed $c$ exist exactly for $c$ at or above the minimal speed](exists-is-front-iff.md)
- [Every Fisher-KPP front speed is at least the minimal speed](two-mul-sqrt-le-of-is-front.md)

## Proof depends on

- [Poincaré–Bendixson theorem](../../../Dynamics/low-dimensional-dynamics/poincar-bendixson-theorem/poincare-bendixson.md)

## Expansion

With $z = x - ct$ and $p = D(u)\, du/dz$ the wave equation becomes the singular system $D(u) u' = p$, $D(u) p' = -cp - D(u)R(u)$, singular on the lines $u = \alpha, \beta$. Rescaling the independent variable by $D(u)\, d\xi = dz$ gives the regular system

$$\frac{du}{d\xi} = p, \qquad \frac{dp}{d\xi} = -cp - D(u) R(u),$$

which has the same orbits but reversed orientation where $D < 0$. Its equilibria are $(0,0), (\alpha,0), (\beta,0), (1,0)$ with eigenvalues $\tfrac12\big(-c \pm \sqrt{c^2 - 4F(u)}\big)$, $F = (DR)'$. Lemma 1: $(1,0)$ and $(\alpha,0)$ are saddles; $(0,0)$ is a stable node iff $c \ge c^*$, and $(\beta,0)$ is a stable node iff $c \ge c_\beta$. Lemma 3: for $c \ge c^*$, the triangle bounded by $p = 0$, $u = \alpha$ and the line $p = -\tfrac{c}{2} u$ is positively invariant, because $c^2/4 \ge \lambda \sup_{(0,\alpha)} D(u)(1-u) = \lambda D_i$. Lemma 4 builds an analogous region through $(\beta,0)$, using $D_i > 4D_g$ to show the required speed is below $c^*$. Poincare-Bendixson then yields heteroclinic orbits $(1,0) \to (\beta,0)$, $(\alpha,0) \to (\beta,0)$ and $(\alpha,0) \to (0,0)$; reversing the middle one and concatenating gives the wave of the original equation.

When instead $D_i < 4D_g$ (so $D > 0$ on $[0,1]$), the same method only brackets the minimal speed: $2\sqrt{\lambda D_i} \le \hat c \le \sup_{u \in (0,1)} 2\sqrt{\lambda (1-u) D(u)}$ (Section 4.1, eq. (38)).

## Sources

- Y. Li, P. van Heijster, R. Marangell and M. J. Simpson, Travelling wave solutions in a negative nonlinear diffusion-reaction model, *J. Math. Biol.* 81 (2020), 1495–1522, <https://doi.org/10.1007/s00285-020-01547-1>, PMCID PMC7717045.
