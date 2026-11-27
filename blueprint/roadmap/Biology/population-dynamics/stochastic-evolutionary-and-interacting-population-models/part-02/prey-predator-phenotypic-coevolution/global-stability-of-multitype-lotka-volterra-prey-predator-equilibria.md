# Global stability of multitype Lotka–Volterra prey–predator equilibria

**Individual-based model.** A community has $d$ prey types with traits $x_1,\dots,x_d$ and $m$ predator types with traits $y_1,\dots,y_m$, and $\mathbf Z^K = K^{-1}(N^K_1,\dots,N^K_d,H^K_1,\dots,H^K_m)$ is the rescaled vector of their numbers. A prey of trait $x$ gives birth at rate $b(x)$ and dies at rate $d(x) + \sum_i c(x,x_i)N^K_i/K + \sum_l B(x,y_l)H^K_l/K$ (intrinsic death, competition, predation); a predator of trait $y$ gives birth at rate $r\sum_iB(x_i,y)N^K_i/K$ (conversion efficiency $r < 1$) and dies at rate $D(y)$.

**Large-population limit.** If $\mathbf Z^K(0)\to\mathbf z(0)$ in probability, then on every $[0,T]$, $\mathbf Z^K$ converges in law to the solution $(n,h)$ of the system $\mathrm{LVP}(\mathbf x,\mathbf y)$:

$$\dot n_i = n_i\Big(b_i - d_i - \sum_{j}c_{ij}n_j - \sum_l B_{il}h_l\Big), \qquad \dot h_l = h_l\Big(r\sum_i B_{il}n_i - D_l\Big),$$

with $b_i = b(x_i)$, $c_{ij} = c(x_i,x_j)$, $B_{il} = B(x_i,y_l)$, $D_l = D(y_l)$.

**Theorem.** Assume $C + C^{T}$ is positive definite for the prey competition matrix $C = (c_{ij})$ and that every subsystem of LVP is non-degenerate.

1. (Global stability.) If $\mathbf z^\ast = (n^\ast,h^\ast)\ge0$ is an equilibrium such that every absent type has negative invasion fitness,

$$b_i - d_i - \sum_j c_{ij}n^\ast_j - \sum_l B_{il}h^\ast_l < 0 \ \ (n^\ast_i = 0), \qquad r\sum_i B_{il}n^\ast_i - D_l < 0 \ \ (h^\ast_l = 0),$$

then $\mathbf z^\ast$ is globally asymptotically stable for positive initial conditions, and it is the unique such equilibrium.
2. (Existence via linear complementarity.) For every $M\in\mathbb R^{d\times d}$, $q\in\mathbb R^d$, $D\in\mathbb R^m_+$ and $B\in\mathbb R_+^{d\times m}$ such that every row of $B$ has a positive entry (every prey type is eaten by some predator), the linear complementarity problem with matrix $\begin{pmatrix}M & B\\ -B^{T} & 0\end{pmatrix}$ and vector $(q, D)$ has a solution. Consequently, if the predation kernel is positive, $B(x,y)>0$ for all traits, and the zero sets of the invasion fitness functions in trait space are Lebesgue-null, then for almost every $(\mathbf x,\mathbf y)$ the system $\mathrm{LVP}(\mathbf x,\mathbf y)$ has a unique globally asymptotically stable equilibrium, and it satisfies the strict conditions of item 1.
3. (Stochastic consequence.) Starting near this equilibrium, the stochastic process $\mathbf Z^K$ stays in any small neighborhood of it for a time at least $e^{V K}$ with probability tending to $1$, and sub-populations absent at equilibrium go extinct within time $O(\log K)$.

Every asymptotically stable equilibrium contains at least as many prey types as predator types (competitive exclusion), so predator diversity is bounded by prey diversity.

## Depends on

- [Lotka–Volterra predator–prey model](../../../lotka-volterra-predator-prey-model/README.md)

## Expansion

The Lyapunov function $V(\mathbf z) = \sum_i (n_i - n^\ast_i\log n_i) + r^{-1}\sum_l (h_l - h^\ast_l\log h_l)$ (Goh's function, adapted) has derivative $-(n - n^\ast)^{T}C(n - n^\ast)$ plus negative terms from absent types: the prey–predator interaction terms cancel because the interaction matrix is $\begin{pmatrix}C & B\\ -rB^{T} & 0\end{pmatrix}$, skew in the off-diagonal blocks. Positive definiteness of $C + C^{T}$ and LaSalle's principle give global convergence. Equilibria with sign conditions on invasion fitnesses are exactly solutions of a linear complementarity problem, whose solvability for this block structure gives existence. The quantitative Lyapunov estimate combined with large deviations for the birth–death process gives the exponential exit time.

## Sources

- Manon Costa, Céline Hauzy, Nicolas Loeuille, Sylvie Méléard, "Stochastic eco-evolutionary model of a prey-predator community", arXiv (2014). Section 2 (model, Proposition 2.2), Section 3 (Proposition 3.1, Theorems 3.3–3.4), Section 4 (Theorem 4.2, Proposition 4.4). <https://doi.org/10.48550/arXiv.1407.3069>. Published version: Journal of Mathematical Biology 72(3) (2016), 573–622, <https://doi.org/10.1007/s00285-015-0895-y>; locators above refer to the arXiv version.
