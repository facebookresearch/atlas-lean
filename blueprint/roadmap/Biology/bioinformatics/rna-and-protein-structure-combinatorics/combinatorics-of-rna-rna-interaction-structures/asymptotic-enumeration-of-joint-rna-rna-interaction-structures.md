# Asymptotic enumeration of joint RNA–RNA interaction structures

**Setting.** Two RNA strands $R$ and $S$ are drawn as horizontal backbones; a *pre-structure* consists of interior arcs within $R$ or within $S$ (secondary structures, noncrossing) and exterior arcs $R_kS_{k'}$ (interaction base pairs), noncrossing among themselves. An interior arc is an ancestor of an exterior arc it encloses; two interior arcs on different strands are dependent if they share a descendant, and a *zigzag* is a pair of dependent interior arcs neither of whose descendant sets contains the other. A **joint structure** $J(R,S,I)$ is a zigzag-free pre-structure. It is *$\sigma$-canonical* if all stacks (helices) have length at least $\sigma$, with arc-length at least $2$. Let $\mathbf T_\sigma(z)$ be the generating function of $\sigma$-canonical secondary structures,

$$\mathbf T_\sigma(z)=\frac{1}{u_\sigma(z)z^2-z+1}\,\mathbf F\!\left(\Big(\frac{\sqrt{u_\sigma(z)}\,z}{u_\sigma(z)z^2-z+1}\Big)^2\right),\qquad u_\sigma(z)=\frac{z^{2\sigma-2}}{z^{2\sigma}-z^2+1},\quad \mathbf F(z)=\frac{1-\sqrt{1-4z}}{2z}.$$

**Shapes.** Every joint structure decomposes uniquely into tight structures and maximal secondary segments, and collapsing stacks gives its *shape*. The trivariate generating function of shapes satisfies

$$(u+v+uv)(z+1)\,\mathbf G^2-\big((u+v+uv)(z+2)+1\big)\mathbf G+(1+u)(1+v)(1+z)=0,$$

and $\mathbf U(z)=\mathbf G(z,z,z)=\dfrac{1+3z+z^2-\sqrt{1-2z-9z^2-10z^3-3z^4}}{2z(z+2)}$, with dominant singularity $\rho\approx0.22144$, the smallest positive root of $1-2z-9z^2-10z^3-3z^4$.

**Theorem.** For $\sigma\ge1$ the generating function of $\sigma$-canonical joint structures by total length satisfies

$$\mathbf J_\sigma(z)=\mathbf T_\sigma(z)^2\,\mathbf U\big(\zeta(z)\big),\qquad \zeta(z)=\frac{z^{2\sigma}\mathbf T_\sigma(z)^2}{1-z^2-z^{2\sigma}(\mathbf T_\sigma(z)^2-1)},$$

it is algebraic (it solves an explicit quadratic equation), and for $1\le\sigma\le9$

$$J_\sigma(s)\sim c_\sigma\,s^{-3/2}\,\gamma_\sigma^{-s},$$

where $\gamma_\sigma$ is the smallest positive solution of $\zeta(z)=\rho$; numerically $\gamma_1^{-1}\approx3.48766$, $\gamma_2^{-1}\approx2.24338$, $\gamma_3^{-1}\approx1.86724$, and $c_1\approx1.6527921$, $c_2\approx4.3011932$.

## Expansion

Inflating each arc of a shape into a stack of length at least $\sigma$ and each gap into an arbitrary $\sigma$-canonical secondary structure is a substitution in the symbolic method, which turns $\mathbf G$ into $\mathbf J_\sigma$. The composition $\mathbf U(\zeta(z))$ is *supercritical*: $\zeta$ reaches the square-root singularity $\rho$ of $\mathbf U$ before $\mathbf T_\sigma$ becomes singular, so the dominant singularity of $\mathbf J_\sigma$ is the root of $\zeta(z)=\rho$ and it inherits the square-root type, which by singularity analysis (transfer theorems) gives the $s^{-3/2}$ subexponential factor.

## Sources

- Thomas J. X. Li, Christian M. Reidys, "Combinatorics of RNA-RNA interaction", arXiv:1006.2924 (2010), Proposition 2, Theorems 3–6 and Corollary 1, <https://doi.org/10.48550/arXiv.1006.2924>.
