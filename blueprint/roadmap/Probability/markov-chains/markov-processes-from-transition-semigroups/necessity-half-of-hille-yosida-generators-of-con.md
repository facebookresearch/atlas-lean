# Necessity half of Hille-Yosida: generators of contraction semigroups are dissipative

Let $X$ be a real Banach space and $(S(t))_{t\ge0}$ a strongly continuous semigroup of contractions on $X$ ($S(0)=I$, $S(s+t)=S(s)S(t)$, $\|S(t)\|\le1$, and $t\mapsto S(t)x$ continuous for every $x$), with generator $Ax=\lim_{t\to0^+}t^{-1}(S(t)x-x)$ on the domain $D(A)$ where the limit exists. Then:

- $A$ is closed and $D(A)$ is dense in $X$;
- for every $\lambda>0$, $\lambda-A:D(A)\to X$ is a bijection, with $\|(\lambda-A)^{-1}\|\le1/\lambda$;
- $(\lambda-A)^{-1}x=\int_0^\infty e^{-\lambda t}S(t)x\,dt$ for every $x\in X$, the integral converging as an improper Riemann integral in $X$.

The resolvent bound is equivalent to dissipativity of $A$: $\|(\lambda-A)x\|\ge\lambda\|x\|$ for $x\in D(A)$ and $\lambda>0$. In finite dimensions, with $S(t)=e^{tA}$ and $\|e^{tA}\|\le1$, the resolvent formula is the Laplace transform of $t\mapsto e^{tA}$.

## Depends on

- [Strongly continuous contraction semigroups, generators and cores](../../../Analysis/operator-theory/strongly-continuous-contraction-semigroups.md)

## Proof depends on

- [Integral identities for a strongly continuous semigroup and its generator](../../../Analysis/operator-theory/integral-identities-for-semigroup-generators.md)

## Expansion

A proof page must establish: density of $D(A)$ through the averages $t^{-1}\int_0^tS(s)x\,ds\in D(A)$; closedness from $S(t)x-x=\int_0^tS(s)Ax\,ds$ for $x\in D(A)$; that the Laplace integral $R_\lambda x$ lies in $D(A)$ with $(\lambda-A)R_\lambda x=x$, and $R_\lambda(\lambda-A)x=x$ for $x\in D(A)$; the bound $\|R_\lambda\|\le\int_0^\infty e^{-\lambda t}\,dt=1/\lambda$; and the finite-dimensional case.

## Sources

- A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*, Applied Mathematical Sciences 44, Springer (1983), <https://link.springer.com/book/10.1007/978-1-4612-5561-1>, Chapter 1, Hille–Yosida theorem (necessity direction).
- K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Graduate Texts in Mathematics 194, Springer (2000), <https://link.springer.com/book/10.1007/b97696>, Chapter II (generators and resolvents).
