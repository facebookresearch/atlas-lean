# Global convergence of the multi-resource chemostat system

Let $n$ consumer phenotypes $x_1,\dots,x_n$ (distinct points of a compact trait space $\mathcal X$) share $r$ resources in a chemostat. With consumer densities $u_i \ge 0$, resource concentrations $R_k \ge 0$, death rates $d(x) > 0$, consumption efficiencies $\eta_k(x) \ge 0$ and resource inflow concentrations $g_k > 0$, the **chemostat system** $\mathrm{CH}(n; x_1,\dots,x_n)$ is

$$\dot u_i = u_i\Big(-d(x_i) + \sum_{k=1}^r \eta_k(x_i) R_k\Big), \qquad \dot R_k = g_k - R_k\Big(1 + \sum_{j=1}^n \eta_k(x_j) u_j\Big).$$

Assume:

- (A3) $\sum_k \eta_k(x) g_k > d(x)$ for every $x \in \mathcal X$ (each type is supercritical at full resources);
- (A4) for every $n$ and distinct $x_1,\dots,x_n$, the system $d(x_i) = \sum_k \eta_k(x_i) g_k / (1 + \sum_j \eta_k(x_j) u_j)$, $1 \le i \le n$, has at most one solution $u \in \mathbb R_+^n$.

(A4) holds, for instance, if for all distinct $x_1,\dots,x_{r+1}$ the $r+1$ vectors $(\eta_k(x_i))_{i \le r+1}$, $k \le r$, and $(d(x_i))_{i\le r+1}$ are linearly independent, and for all distinct $x_1,\dots,x_r$ the vectors $(\eta_k(x_i))_{i \le r}$ are linearly independent. Conversely, under (A4) at most $r$ types can have a positive equilibrium.

**Theorem.** Under (A3) and (A4), for every $n \ge 1$ and distinct $x_1,\dots,x_n$ there is $(\bar u, \bar R) \in \mathbb R_+^{n+r}$ such that every solution with $u_i(0) > 0$ for all $i$ converges to $(\bar u, \bar R)$. Moreover $(\bar u, \bar R)$ is the unique equilibrium satisfying, for every $i$ with $\bar u_i = 0$, the saturation condition

$$-d(x_i) + \sum_{k=1}^r \eta_k(x_i) \bar R_k \le 0.$$

At every equilibrium $\bar R_k = g_k / (1 + \sum_j \eta_k(x_j)\bar u_j)$.

## Expansion

Replacing the resources by their quasi-equilibria gives the reduced system $\dot u_i = u_i(-d(x_i) + \sum_k \eta_k(x_i) g_k / (1 + \sum_j \eta_k(x_j) u_j))$, which has the strict Lyapunov function

$$F(u) = \sum_i d(x_i) u_i - \sum_k g_k \log\Big(1 + \sum_j \eta_k(x_j) u_j\Big),$$

with $\tfrac{d}{dt}F(u(t)) = -\sum_i u_i(\cdots)^2 \le 0$. $F$ is convex and coercive on $\mathbb R_+^n$, and (A4) forces strict convexity on the face of its support at any critical point, so $F$ has a unique local minimizer, which is the saturated equilibrium. The full system is handled by extending $F$ with a resource term, as for the classical single-resource chemostat functional, and LaSalle's principle gives global convergence.

## Sources

- Nicolas Champagnat, Pierre-Emmanuel Jabin, Sylvie Méléard, "Adaptation in a stochastic multi-resources chemostat model", arXiv (2013). Section 2.4 (system CH), Section 3.1 (assumptions (A3)–(A4), Proposition 3.1, Theorem 3.2), Section 3.2 (Lyapunov functional, Step 1). <https://doi.org/10.48550/arXiv.1302.0552>. Published version: Journal de Mathématiques Pures et Appliquées 101(6) (2014), 755–788, <https://doi.org/10.1016/j.matpur.2013.10.003>; locators above refer to the arXiv version.
