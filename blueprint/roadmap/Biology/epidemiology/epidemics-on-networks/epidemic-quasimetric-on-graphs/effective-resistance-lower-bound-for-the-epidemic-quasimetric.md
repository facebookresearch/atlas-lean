# Effective-resistance lower bound for the epidemic quasimetric

Let $G = (V,E)$ be a finite connected graph with graph distance $d_G$. For $x \in V$ and $r \ge 0$ let $\Omega(x,r)$ be the subgraph induced by the ball $\{v : d_G(x,v) \le r\}$ and $|\Omega(x,r)|$ its number of edges. The **epidemic quasimetric** is

$$

\varepsilon(x,y) = |\Omega(x,d_G(x,y))| + |\Omega(y,d_G(x,y))|,

$$

the number of contacts exposed if an epidemic started at $x$ spreads until it reaches $y$, or vice versa. It is symmetric and positive for $x \ne y$, but the triangle inequality can fail by an arbitrarily large factor.

Give each edge unit resistance. The **effective resistance** $R_{\mathrm{eff}}(a,b)$ is the potential difference needed to send a unit current from $a$ to $b$; the effective conductance is $C_{\mathrm{eff}} = 1/R_{\mathrm{eff}}$. The **modulus** $\mathrm{Mod}(a,b)$ of the family of paths from $a$ to $b$ is $\inf \sum_{e \in E}\rho(e)^2$ over densities $\rho : E \to [0,\infty)$ giving every $a$–$b$ path $\rho$-length at least $1$, and the **capacity** is $\inf \sum_{\{u,v\} \in E}(U(u)-U(v))^2$ over functions with $U(a) = 0$, $U(b) = 1$.

**Theorem.**

1. $C_{\mathrm{eff}}(a,b) = \mathrm{cap}(a,b) = \mathrm{Mod}(a,b)$, and effective resistance is a metric on $V$.
2. For all $a \ne b$,

$$

d_G(a,b)^2\,\mathrm{Mod}(a,b) \le \varepsilon(a,b), \qquad\text{hence}\qquad \varepsilon(a,b) \ge \frac{d_G(a,b)^2}{R_{\mathrm{eff}}(a,b)} .

$$

The discrepancy $\delta(a,b) = R_{\mathrm{eff}}(a,b)\,\varepsilon(a,b)/d_G(a,b)^2 \ge 1$ stays between $2$ and $4$ on paths, grows linearly in the number of vertices on stars and complete graphs, and can grow quadratically for a complete graph with a pendant vertex (Examples 7.1 and 7.2).

## Expansion

Item 1 combines Thomson's principle (the unit current flow minimizes energy among unit flows), the identification of the capacitary function with the electrical potential, and the duality between path densities and potentials. For item 2, let $d = d_G(a,b)$ and take $\rho = 1/d$ on every edge of $\Omega(a,d) \cup \Omega(b,d)$ and $0$ elsewhere: every $a$–$b$ path has at least $d$ edges, all inside these balls until it reaches $b$, so $\rho$ is admissible, and its energy is at most $\varepsilon(a,b)/d^2$. The modulus is the infimum of energies, which gives the bound.

## Sources

- Josh Ericson, Pietro Poggi-Corradini, Hainan Zhang, "Effective resistance on graphs and the Epidemic quasimetric", arXiv (2012); Involve (2014). Section 3 (definition), Section 5 (Theorem 5.4, Proposition 5.7), Section 6 (Theorem 6.3, Proposition 6.4, Corollary 6.5), Section 7. <https://doi.org/10.48550/arXiv.1210.1460>. Published version: Involve, a Journal of Mathematics 7(1) (2014), 97–124, <https://doi.org/10.2140/involve.2014.7.97>; locators above refer to the arXiv version.
