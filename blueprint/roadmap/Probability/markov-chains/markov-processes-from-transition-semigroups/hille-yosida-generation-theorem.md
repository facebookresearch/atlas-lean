# Hille–Yosida generation theorem

Let $X$ be a real Banach space and $A:D(A)\to X$ a linear operator. If $A$ is closed, $D(A)$ is dense, and every $\lambda>0$ belongs to the resolvent set of $A$ with

$$\|(\lambda-A)^{-1}\|\le\frac1\lambda,$$

then $A$ is the generator of a strongly continuous semigroup of contractions on $X$; this semigroup is unique and is the strong limit $S(t)x=\lim_{\lambda\to\infty}e^{tA_\lambda}x$ of the semigroups of the Yosida approximations $A_\lambda=\lambda A(\lambda-A)^{-1}=\lambda^2(\lambda-A)^{-1}-\lambda I$. Under the hypothesis, $\|(\lambda-A)^{-n}\|\le\lambda^{-n}$ for all $n\ge1$ by submultiplicativity of the operator norm. Together with the [necessity half](necessity-half-of-hille-yosida-generators-of-con.md), this gives the contraction Hille–Yosida theorem: a linear operator generates a strongly continuous contraction semigroup if and only if it is closed and densely defined and satisfies the resolvent bound for every $\lambda>0$. The positive-maximum-principle (Feller) variant is a separate statement.

## Depends on

- [Necessity half of Hille-Yosida: generators of contraction semigroups are dissipative](necessity-half-of-hille-yosida-generators-of-con.md)
- [Strongly continuous contraction semigroups, generators and cores](../../../Analysis/operator-theory/strongly-continuous-contraction-semigroups.md)

## Expansion

A proof page must establish: $\lambda(\lambda-A)^{-1}x\to x$ as $\lambda\to\infty$, first for $x\in D(A)$ and then by density; $A_\lambda x\to Ax$ for $x\in D(A)$; $\|e^{tA_\lambda}\|\le1$ from $\|e^{tA_\lambda}\|\le e^{-\lambda t}e^{\lambda t\|\lambda(\lambda-A)^{-1}\|}$; the Cauchy estimate $\|e^{tA_\lambda}x-e^{tA_\mu}x\|\le t\|A_\lambda x-A_\mu x\|$ for $x\in D(A)$, using that the Yosida approximations commute; strong continuity and contractivity of the limit; identification of its generator with $A$ through the resolvent; and uniqueness of the semigroup with a given generator.

## Sources

- A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*, Applied Mathematical Sciences 44, Springer (1983), <https://link.springer.com/book/10.1007/978-1-4612-5561-1>, Chapter 1, Hille–Yosida theorem.
- K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Graduate Texts in Mathematics 194, Springer (2000), <https://link.springer.com/book/10.1007/b97696>, Chapter II (generation theorems).
