# Square-splitting convolution as a bivariate Dirichlet convolution

Let $\star$ be the
square-splitting convolution. For all complex arithmetic functions $f$ and $g$, every squarefree
natural number $u$ and every natural number $v \ge 1$,

$$(f \star g)(u v^2) = \sum_{u_1 \mid u} \sum_{v_1 \mid v} f(u_1 v_1^2)\, g((u/u_1)(v/v_1)^2).$$

Moreover, for every function $F : \mathbb{N} \times \mathbb{N} \to \mathbb{C}$ there is exactly
one complex arithmetic function $f$ with $f(u v^2) = F(u, v)$ for every squarefree $u$ and every
$v \ge 1$.

Thus $f \mapsto \big((u, v) \mapsto f(u v^2)\big)$ is a bijection from complex arithmetic functions
onto functions on $\{(u, v) : u \text{ squarefree},\ v \ge 1\}$, and it turns $\star$ into the
bivariate Dirichlet convolution
$(\Phi \odot \Psi)(u, v) = \sum_{u_1 \mid u} \sum_{v_1 \mid v} \Phi(u_1, v_1)\, \Psi(u/u_1, v/v_1)$.

## Sources

- Champak Talukdar and Helen K. Saikia, *A Square-Splitting A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 2 (`integers-2026-A56-thm-2`).
