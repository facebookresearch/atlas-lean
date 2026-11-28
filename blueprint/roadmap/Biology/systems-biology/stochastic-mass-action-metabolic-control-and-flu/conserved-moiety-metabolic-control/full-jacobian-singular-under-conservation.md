# Conservation laws make the full Jacobian singular

If a metabolic network has a nonzero conservation relation, its full Jacobian $N\varepsilon'$ is singular at every state, so the full-state regular steady-state condition can never hold.

Let $M,R$ be finite, $N\in\mathbb{R}^{M\times R}$ a stoichiometric matrix with $\operatorname{rank}N<|M|$ (equivalently, some nonzero $\ell\in\mathbb{R}^M$ has $\ell^{\mathsf T}N=0$), and let $f_i\colon\mathbb{R}^M\to\mathbb{R}$ be rate laws with [fluxes](../flux.md) $v_i(e,s)=e_if_i(s)$. Then for every $e\in\mathbb{R}^R$ and every $s$ at which all $f_i$ are differentiable, the square matrix

$$N\varepsilon'(e,s),\qquad \varepsilon'_{im}(e,s)=e_i\frac{\partial f_i}{\partial s_m}(s),$$

is singular: its image lies in $\operatorname{im}N$ and $\ell^{\mathsf T}N\varepsilon'(e,s)=0$ for every conservation relation $\ell$. Consequently no map $\sigma\colon\mathbb{R}^R\to\mathbb{R}^M$ is a [regular steady state](../is-regular-steady-state.md) at any $e_0$ for $N$ and $f$, because the injectivity of $\delta\mapsto N\varepsilon'(e_0,\sigma(e_0))\delta$ required there fails.

Example: for the species $S_1,S_2,C_1,C_2$ and reactions $S_1+C_1\to S_2+C_2$, $S_2\to S_1$, $C_2\to C_1$ with mass-action rates, $\operatorname{rank}N=2$, the pools $S_1+S_2$ and $C_1+C_2$ are conserved, and the $4\times4$ full Jacobian is singular at every state, while at the steady state with all concentrations, rate constants and enzyme levels equal to $1$ the [reduced Jacobian](conserved-pool-reduced-jacobian.md) is $\begin{pmatrix}-2&-1\\-1&-2\end{pmatrix}$, with determinant $3$.

## Depends on

- [Reaction fluxes proportional to enzyme levels](../flux.md)
- [Regular steady state of a metabolic network](../is-regular-steady-state.md)

## Proof depends on

- [Regular steady state of a metabolic network](../is-regular-steady-state.md)

## Expansion

$N\varepsilon'$ maps $\mathbb{R}^M$ into $\operatorname{im}N$, a proper subspace when $\operatorname{rank}N<|M|$; a linear endomorphism of a finite-dimensional space that is not surjective is not injective. Hence the regularity clause of the full-state definition is never satisfied, and the full-state summation and connectivity theorems, which assume it, say nothing about networks with conserved pools. The reduced Jacobian of the example is computed with $B$ spanned by the reaction vectors of $S_2\to S_1$ and $C_2\to C_1$; the conserved-pool replacement of the regularity clause is the [regular steady state with fixed conserved pools](conserved-pool-regular-steady-state.md).

## Sources

- K. Smallbone, E. Simeonidis, N. Swainston and P. Mendes, Towards a genome-scale kinetic model of cellular metabolism, *BMC Systems Biology* 4 (2010), article 6, [doi:10.1186/1752-0509-4-6](https://doi.org/10.1186/1752-0509-4-6): Methods, “Control analysis”, Equation (6) and the following paragraph (in general $\operatorname{rank}(N\varepsilon')<m$ and the system displays moiety conservations).
