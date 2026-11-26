# Branch of cycles connecting an equilibrium and infinity

Consider a planar system with a parameter $\lambda \in [0,1]$,

$$x' = f(x,y;\lambda), \qquad y' = g(x,y;\lambda),$$

where $f,g$ are continuously differentiable in $(x,y)$ and jointly continuous in all arguments. The system has a **branch of cycles connecting the origin and infinity** if for every bounded open domain $G \ni (0,0)$ there is some $\lambda \in [0,1]$ for which the system has a cycle contained in $\bar G$ that touches $\partial G$.

**Proposition.** Suppose that

1. the origin is the only equilibrium for every $\lambda \in [0,1]$;
2. the Jacobian $J(\lambda)$ at the origin is invertible for every $\lambda \in [0,1]$;
3. the spectrum of $J(0)$ lies in the open right half-plane and the spectrum of $J(1)$ in the open left half-plane;
4. the system has no cycles for $\lambda = 0$ and for $\lambda = 1$.

Then the system has a branch of cycles connecting the origin and infinity: a cycle born at a Hopf bifurcation inside $(0,1)$ blows up to infinity before $\lambda$ reaches $1$.

**Application to predators with competition–cooperation.** For positive $a,b,c,d$ consider

$$x' = x(a - by), \qquad y' = y\big(-c + dx + f(y;\lambda)\big), \qquad x,y > 0,$$

where $f(y;\lambda) > 0$ (cooperation) below a threshold $\bar y(\lambda)$ and $f(y;\lambda) < 0$ (competition) above it, e.g. $f = \arctan y - \lambda y$. Assume $c > f(a/b;\lambda)$ for all $\lambda$, so the unique positive equilibrium is $(x_*,y_*) = \big(d^{-1}(c - f(a/b;\lambda)),\ a/b\big)$. If

$$\partial_y f(y_*;0) > 0, \qquad \partial_y f(y_*;1) < 0,$$

and $(y - y_*)\big(f(y;0) - f(y_*;0)\big) > 0$, $(y - y_*)\big(f(y;1) - f(y_*;1)\big) < 0$ for all $y > 0$, $y \ne y_*$, then the system has a branch of positive cycles connecting $(x_*,y_*)$ and infinity. These conditions hold in particular when $f(\cdot;0)$ is strictly increasing and $f(\cdot;1)$ is strictly decreasing.

## Depends on

- [First integral of the Lotka–Volterra system](../../population-dynamics/lotka-volterra-predator-prey-model/first-integral.md)

## Expansion

Conditions 2–3 force an Andronov–Hopf bifurcation in $(0,1)$ and rule out homoclinic orbits. If some bounded $G$ admitted no orbit touching $\partial G$, then $\bar G$ would isolate the invariant set $S_\lambda$ for all $\lambda$; by condition 4 and Poincaré–Bendixson $S_0 = S_1 = \{0\}$, but the Conley indices of a repeller and an attractor differ, contradicting homotopy invariance of the Conley index. For the predator–prey example, a logarithmic change of variables moves the equilibrium to the origin, and $V = d(x - x_*\ln x) + b(y - y_*\ln y)$ satisfies $\dot V = b(y - y_*)(f(y;\lambda) - f(y_*;\lambda))$, which excludes cycles at $\lambda = 0,1$.

## Sources

- E. Bouse, D. Rachinskii, "Blow up of a cycle in Lotka–Volterra type equations with competition–cooperation terms and quasi-linear systems", arXiv (2010). Section 2 (Proposition on planar systems and the Lotka–Volterra example). <https://doi.org/10.48550/arXiv.1007.4424>
