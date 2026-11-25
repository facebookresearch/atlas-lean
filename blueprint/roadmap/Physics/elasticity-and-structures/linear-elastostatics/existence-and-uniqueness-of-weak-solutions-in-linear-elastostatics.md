# Existence and uniqueness of weak solutions in linear elastostatics

This node covers the weak formulation of the mixed displacement-traction problem of linear elasticity. Let $\Omega \subset \mathbb{R}^3$
be a bounded connected open set with Lipschitz boundary, split as $\partial\Omega = \overline{\Gamma_D} \cup \overline{\Gamma_N}$ with $\Gamma_D$ of
positive surface measure. Let the elasticity tensor $\mathbb{C}(x)$ be measurable and bounded, with the symmetries
$\mathbb{C}_{ijkl} = \mathbb{C}_{jikl} = \mathbb{C}_{klij}$, and uniformly positive definite on symmetric matrices:
$\mathbb{C}(x)\varepsilon : \varepsilon \ge c_0 |\varepsilon|^2$ for some $c_0 > 0$. Let $f \in L^2(\Omega)^3$ and $g \in L^2(\Gamma_N)^3$, and
$V = \{v \in H^1(\Omega)^3 : v = 0 \text{ on } \Gamma_D\}$. Then there is exactly one $u \in V$ with

$$\int_\Omega \mathbb{C}\,\varepsilon(u) : \varepsilon(v)\,dx = \int_\Omega f\cdot v\,dx + \int_{\Gamma_N} g\cdot v\,dA \quad \text{for all } v \in V,$$

where $\varepsilon(v) = \tfrac12(\nabla v + \nabla v^{\mathsf T})$, and $u$ is the unique minimizer over $V$ of the total potential energy.

## Depends on

- [Existence and uniqueness of weak solutions](../../../Analysis/partial-differential-equations/weak-solutions-of-elliptic-equations/exists-unique-weak-solution.md)

## Expansion

A good expansion states Korn's inequality on $V$, which gives coercivity of the bilinear form, and the trace theorem, which gives
continuity of the load functional, as separate nodes, and then applies the Lax-Milgram theorem. The derivation of the weak form from the
balance law and the constitutive law for smooth solutions is a separate node.

## Sources

- P. G. Ciarlet, *Mathematical Elasticity, Volume I: Three-Dimensional Elasticity*, North-Holland, 1988, for the weak formulation, Korn's inequality and existence.
