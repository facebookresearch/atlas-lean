# Equilibria and competitive exclusion in Lotka–Volterra competition with fear

**Model.** Two competitors $u, v \ge 0$, where $v$ is "fearful" of $u$: fear of level $k \ge 0$ divides the birth term of $v$ by $1 + ku$,

$$\frac{du}{dt} = a_1 u - b_1 u^2 - c_1 uv, \qquad \frac{dv}{dt} = \frac{a_2 v}{1 + ku} - b_2 v^2 - c_2 uv,$$

with positive intrinsic growth rates $a_i$, intraspecific competition $b_i$ and interspecific competition $c_i$.

**Theorem (equilibria).** The boundary equilibria $(0,0)$, $(a_1/b_1, 0)$ and $(0, a_2/b_2)$ always exist. Interior equilibria are the positive roots $v^*$ of a quadratic obtained by eliminating $u$ on the $u$-nullcline $u = (a_1 - c_1 v)/b_1$; two positive interior equilibria exist when

$$b_1 b_2 > 2c_1c_2, \qquad k < \frac{b_1^2 a_2 - a_1 c_2 b_1}{a_1^2 c_2},$$

and both roots satisfy $v^* < a_1/c_1$. Hence, unlike the classical model, fear permits bistability between an interior equilibrium and a boundary equilibrium.

**Theorem (spatial competitive exclusion).** On a bounded domain $\Omega \subset \mathbb{R}^n$ with Neumann boundary conditions, diffusion rates $d_1, d_2 > 0$, flat positive initial data and a spatially varying fear function $k(x) \in C^1(\Omega)$ with $k \ge 0$ vanishing only on a null set, if

$$\frac{a_1}{a_2} > \max\left\{\frac{b_1}{c_2}, \frac{c_1}{b_2}\right\},$$

then the solution $(u, v)$ converges uniformly to $(a_1/b_1, 0)$ as $t \to \infty$.

## Expansion

Fear only lowers the per-capita growth of $v$, so $(u, v)$ is bounded by comparison with the classical fear-free Lotka–Volterra system: $v \le \bar v$ where $(\bar u, \bar v)$ solves the system with $k \equiv 0$. Under the classical exclusion condition $\bar v \to 0$, and nonnegativity squeezes $v \to 0$; the $u$-equation then reduces to logistic growth with limit $a_1/b_1$. Fear can therefore never rescue the weaker competitor, but by bending the $v$-nullcline it can create interior equilibria and a saddle-node bifurcation in $a_1$, where the classical model only has exclusion or coexistence.

## Sources

- Vaibhava Srivastava, Eric M. Takyi and Rana D. Parshad, "The effect of "fear" on two species competition", Mathematical Biosciences and Engineering 20 (2023), 8814–8855, <https://doi.org/10.3934/mbe.2023388>; numbering as in arXiv:2210.10280: Theorem 2.1, Theorem 2.18 and Theorem 3.9.
