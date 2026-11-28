# Invasion fitness and coexistence in the multi-resource chemostat

In the [multi-resource chemostat system](global-convergence-of-the-multi-resource-chemostat-system.md) $\mathrm{CH}(n;x_1,\dots,x_n)$ under assumptions (A3)–(A4), with $d$ and $\eta_k$ of class $C^2$ and positive on $\mathcal X$ (the source's (2.6)), let $(\bar u(\mathbf x), \bar R(\mathbf x))$ be its globally attracting saturated equilibrium, $\mathbf x = (x_1,\dots,x_n)$. The traits **coexist** if $\bar u_i(\mathbf x) > 0$ for all $i$; write $\mathcal D_n \subset \mathcal X^n$ for the coexistence domain ($\mathcal D_1 = \mathcal X$). The **invasion fitness** of a mutant trait $y$ in the resident community $\mathbf x$ is its per-capita growth rate at the resident resource levels,

$$f(y; x_1,\dots,x_n) = -d(y) + \sum_{k=1}^r \eta_k(y)\,\bar R_k(\mathbf x).$$

**Proposition (dimorphic coexistence).** For $x_1 \neq x_2$, the traits coexist if and only if $f(x_1;x_2) > 0$ and $f(x_2;x_1) > 0$. The coexistence densities then solve

$$d(x_i) = \sum_{k=1}^r \frac{\eta_k(x_i)\,g_k}{1 + \eta_k(x_1)\bar u_1 + \eta_k(x_2)\bar u_2}, \qquad i = 1,2.$$

**Proposition (adding a mutant).** The map $\bar u$ is $C^2$ and bounded on $\mathcal D_n$, and $\mathcal D_n$ is open. If $\mathbf x \in \mathcal D_n$ and $y$ is such that replacing $x_i$ by $y$ still gives a coexisting $n$-tuple (true for $y$ close to $x_i$), then $(\mathbf x, y) \in \mathcal D_{n+1}$ if and only if

$$f(y;\mathbf x) > 0 \quad\text{and}\quad f(x_i; x_1,\dots,x_{i-1},y,x_{i+1},\dots,x_n) > 0.$$

So, as in Lotka–Volterra adaptive dynamics, coexistence after a small mutation is decided by mutual invasibility, here computed through the resource equilibria rather than a competition kernel.

## Depends on

- [Global convergence of the multi-resource chemostat system](global-convergence-of-the-multi-resource-chemostat-system.md)
- [Mutual invasibility](../../../../classification-of-adaptive-dynamics-singular-str/mutual-invasibility.md)

## Expansion

The saturated equilibrium of $\mathrm{CH}(n+1;\mathbf x,y)$ equals $(\bar u(\mathbf x),0)$ exactly when the mutant cannot grow, $f(y;\mathbf x) \le 0$; when $f(y;\mathbf x) > 0$ that boundary point is unstable with eigenvalue $f(y;\mathbf x)$, so the mutant invades and the system moves to a new saturated equilibrium. Uniqueness of the saturated equilibrium (assumption (A4)) leaves only two candidates near $(\mathbf x, y)$: coexistence of all $n+1$ types, or replacement of $x_i$ by $y$; the second is ruled out exactly when $x_i$ can reinvade the community in which $y$ replaced it. Smoothness of $\bar u$ on $\mathcal D_n$ follows from the implicit function theorem applied to the equilibrium equations.

## Sources

- Nicolas Champagnat, Pierre-Emmanuel Jabin, Sylvie Méléard, "Adaptation in a stochastic multi-resources chemostat model", arXiv (2013). Section 3.3 (Definition 3.3, Proposition 3.5, Lemma 3.6, Proposition 3.7). <https://doi.org/10.48550/arXiv.1302.0552>. Published version: Journal de Mathématiques Pures et Appliquées 101(6) (2014), 755–788, <https://doi.org/10.1016/j.matpur.2013.10.003>; locators above refer to the arXiv version.
