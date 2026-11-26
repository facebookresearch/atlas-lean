# Steady state and global well-posedness of the Lander–Nie–Wan morphogen–receptor model

**Model.** Let $\Omega \subset \mathbb{R}^n$ be a bounded domain with $C^{1,1}$ boundary split into two disjoint parts, $\partial\Omega = \Gamma_D \sqcup \Gamma_N$, and let $p > n \ge 1$. Free morphogen $l(t,x)$ diffuses in the tissue, binds receptors whose total (free plus bound) concentration is normalized to $1$, unbinds, and is degraded only in the bound state $s(t,x)$. After nondimensionalization the Lander–Nie–Wan model reads

$$
\begin{aligned}
\partial_t l - D\Delta l &= \delta s - l(1-s), && (t,x) \in (0,\infty)\times\Omega,\\
\partial_t s &= -(\delta+\epsilon)s + l(1-s), && (t,x) \in (0,\infty)\times\Omega,\\
-D\,\nabla_n l &= -\nu \ \text{ on } \Gamma_N, \qquad l = 0 \ \text{ on } \Gamma_D,
\end{aligned}
$$

with diffusion $D > 0$, unbinding rate $\delta > 0$, degradation rate $\epsilon > 0$ and a time-independent source flux $0 \le \nu \in W^{1-1/p}_p(\Gamma_N)$ entering through $\Gamma_N$. Initial data satisfy $l_0, s_0 \in W^1_p(\Omega)$, $0 \le l_0$, $0 \le s_0 < 1$, and $l_0 = s_0 = 0$ on $\Gamma_D$.

**Theorem (steady state).** The system has a unique nonnegative steady state $(l_\infty, s_\infty)$, where $0 \le l_\infty \in W^2_p(\Omega)$ is the unique solution of the semilinear elliptic problem

$$
-D\Delta l_\infty = -\frac{\epsilon\, l_\infty}{\delta + \epsilon + l_\infty} \ \text{ in } \Omega, \qquad -D\nabla_n l_\infty = -\nu \ \text{ on } \Gamma_N, \qquad l_\infty = 0 \ \text{ on } \Gamma_D,
$$

and $s_\infty = l_\infty/(\epsilon + \delta + l_\infty)$.

**Theorem (global existence).** There is a unique global solution with $l - l_\infty \in C([0,\infty); W^1_p) \cap C^1((0,\infty); W^1_p) \cap C((0,\infty); W^3_p)$ and $s \in C^1([0,\infty); W^1_p)$, and it respects the biological bounds

$$
0 \le l(t,x), \qquad 0 \le s(t,x) < 1 \qquad \text{for all } (t,x) \in [0,\infty)\times\Omega.
$$

## Expansion

At equilibrium the $s$-equation is algebraic, $s = l/(\delta+\epsilon+l)$, and substituting it into the $l$-equation leaves a scalar elliptic problem with the bounded Michaelis–Menten-type sink $f(l)\,l$, $f(x) = \epsilon/(\delta+\epsilon+x)$. Existence follows from Schauder's fixed point theorem applied to the map $u \mapsto w$ solving the linear problem $-D\Delta w + f(u)w = 0$ with the same boundary data: since $0 \le f \le \epsilon/(\delta+\epsilon)$, elliptic estimates give $\|w\|_{W^2_p} \le C\|\nu\|_{W^{1-1/p}_p(\Gamma_N)}$, so the map has bounded, precompact range in $L^p$, and testing with $w_-$ shows $w \ge 0$. For the evolution, write $z = (l - l_\infty, s)$; the diffusion operator generates an analytic semigroup on $W^1_p$ with homogeneous mixed boundary conditions, and the reaction terms are locally Lipschitz, so a unique maximal mild solution exists and satisfies a Duhamel formula, with blow-up of the $W^1_p$ norm the only obstruction to globality. Invariance of $\{l \ge 0,\ 0 \le s < 1\}$ follows from the sign structure of the reaction terms, and a priori bounds from the semigroup estimates and a singular Gronwall inequality exclude finite-time blow-up. Since $p > n$, the solution is Hölder continuous.

## Sources

- M. Małogrosz, *Well-posedness and asymptotic behavior of a multidimensional model of morphogen transport*, arXiv:1112.5833 (2011), Section 2 (model), Section 3, assumptions A1–A4 and Theorems 1–2. <https://doi.org/10.48550/arXiv.1112.5833>
- A. D. Lander, Q. Nie and F. Y. M. Wan, *Do morphogen gradients arise by diffusion?*, Developmental Cell 2 (2002) 785–796 (origin of the model).
