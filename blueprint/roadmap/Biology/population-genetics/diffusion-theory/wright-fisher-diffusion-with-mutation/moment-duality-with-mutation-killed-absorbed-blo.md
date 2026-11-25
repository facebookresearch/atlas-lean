# Moment duality for the Wright-Fisher diffusion with two-way mutation

Let $\theta_1,\theta_2\ge0$, and let $X$ solve the
[selection-mutation martingale problem](two-way-mutation-and-selection-wright-fisher-mar.md)
with $\alpha=0$ and $X_0=x\in[0,1]$ almost surely. For an integer $n\ge0$,
let $N$ be the finite-state continuous-time chain on
$\{0,\ldots,n\}\cup\{\dagger\}$, started at $n$, with rates from $k\ge1$

$$k\to k-1:\quad a_k=\tfrac12 k(k-1+\theta_1),\qquad
 k\to\dagger:\quad b_k=\tfrac12 k\theta_2,$$

and absorbing $0$ and $\dagger$. Define
$h_x(k)=x^k$ for $k\ge0$, including $h_x(0)=1$ even when $x=0$, and
$h_x(\dagger)=0$. Then for every $t\ge0$,

$$\mathbb E[X_t^n]=\mathbb E_n[h_x(N_t)].$$

For $n\ge1$ the generator identity is

$$L_{0,\theta}(x^n)=a_n(x^{n-1}-x^n)-b_nx^n.$$

For $n=0$ use $L1=0$ separately; no negative exponent at $x=0$ is used.
For $n=1$, this is $(\theta_1-(\theta_1+\theta_2)x)/2$.
Writing $\theta=\theta_1+\theta_2$, the first moment is consequently

$$\mathbb E X_t=
 \begin{cases}
 \theta_1/\theta+(x-\theta_1/\theta)e^{-\theta t/2},&\theta>0,\\
 x,&\theta=0.
 \end{cases}$$

When both mutation rates vanish, the nonempty states evolve as Kingman's
block count. The state zero remains the separate empty-sample convention.

## Depends on

- [Martingale problem with selection and mutation](two-way-mutation-and-selection-wright-fisher-mar.md)

## Proof depends on

- [Generator with two-way mutation](mutation-generator.md)

## Expansion

For each fixed $n$, all functions and generator images used here are bounded
on $[0,1]$. Taking expectations in the martingale property and applying
Fubini gives the triangular integral equations for $m_k(t)=\mathbb E X_t^k$,
$0\le k\le n$. Path continuity and dominated convergence give continuous
moments; hence

$$m'_k=a_km_{k-1}-(a_k+b_k)m_k,\quad k\ge1,\qquad
 m_0=1,\quad m_k(0)=x^k.$$

The backward equations of the finite chain give the same system for
$\mathbb E_kh_x(N_t)$, with cemetery value zero. Uniqueness of this finite
linear ODE proves the identity. There is no explosion issue for the finite
chain and no required coupling or independence between $X$ and $N$.

## Sources

- S. Tavaré, "Line-of-descent and genealogical processes, and their applications in population genetics models", Theoretical Population Biology 26 (1984), 119–164, <https://doi.org/10.1016/0040-5809(84)90027-3>, Section 4, (4.7); Section 7.5, (7.20)–(7.21), for mutation towards the counted allele, and (7.24)–(7.25), for mutation away. The simultaneous two-way killed dual follows from the generator and finite-system argument above, not a claimed verbatim two-way statement in the source.
