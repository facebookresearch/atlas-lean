# Trotter–Kato approximation theorem

Let $L$ be a real Banach space, let $(T_n(t))_{t\ge0}$, $n\ge1$, and $(T(t))_{t\ge0}$ be [strongly continuous contraction semigroups](strongly-continuous-contraction-semigroups.md) on $L$ with generators $A_n$ and $A$, and let $D$ be a core for $A$. Then the following are equivalent:

1. for every $f\in L$ and every $t_0\ge0$, $\sup_{0\le t\le t_0}\lVert T_n(t)f-T(t)f\rVert\to0$;
2. for every $f\in D$ there are $f_n\in\mathcal D(A_n)$ with $f_n\to f$ and $A_nf_n\to Af$.

## Depends on

- [Strongly continuous contraction semigroups, generators and cores](strongly-continuous-contraction-semigroups.md)

## Expansion

A proof page must show that condition 2 is equivalent to strong convergence of the resolvents, $(\lambda-A_n)^{-1}g\to(\lambda-A)^{-1}g$ for every $g\in L$ and some, equivalently every, $\lambda>0$, using the core property and the bounds $\lVert(\lambda-A_n)^{-1}\rVert\le1/\lambda$ (taking $f_n=(\lambda-A_n)^{-1}(\lambda-A)f$ in one direction); derive condition 1 from resolvent convergence, for instance by comparing each semigroup with the semigroups of its Yosida approximations, uniformly in $n$; and derive resolvent convergence from condition 1 by the Laplace transform formula $(\lambda-A_n)^{-1}g=\int_0^\infty e^{-\lambda t}T_n(t)g\,dt$ and dominated convergence. It should record the discrete-time variant for contractions $T_N$ and rates $a_N\to\infty$, in which $T_N^{\lfloor a_Nt\rfloor}$ replaces $T_n(t)$ and $a_N(T_N-I)$ replaces $A_n$.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, <https://doi.org/10.1002/9780470316658>, Chapter 1, Section 6.
- A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*, Springer, 1983, Chapter 3.
