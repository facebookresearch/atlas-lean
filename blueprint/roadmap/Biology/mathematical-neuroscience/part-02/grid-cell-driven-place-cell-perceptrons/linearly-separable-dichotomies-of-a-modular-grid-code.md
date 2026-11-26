# Linearly separable dichotomies of a modular grid code

**Setting.** Let $M$ grid modules have integer periods $\lambda=(\lambda_1,\dots,\lambda_M)$ and let $N=\sum_m\lambda_m$. A grid-like pattern is a vector $c\in\{0,1\}^{\lambda_1}\times\dots\times\{0,1\}^{\lambda_M}$ with exactly one active cell in each module; the set $C_\lambda$ of all such patterns has $\Lambda=\prod_m\lambda_m$ elements. A place cell is a perceptron $(w,\theta)$ that is active on $c$ iff $w^{\mathsf T}c>\theta$; a set of active patterns (a place-field arrangement, or dichotomy of $C_\lambda$) is realizable iff it is linearly separable.

**Geometry of the code.**

1. $\operatorname{span}C_\lambda=\{y=(y_1,\dots,y_M):\ \sum_i y_{1,i}=\dots=\sum_i y_{M,i}\}$, so $\dim\operatorname{span}C_\lambda=\sum_m\lambda_m-M+1$.
2. Because $\mathbf 1^{\mathsf T}c=M$ for every $c\in C_\lambda$, every realizable dichotomy is realized by a perceptron with non-negative weights, and also by one with zero threshold.
3. The convex hull of $C_\lambda$ is the product of simplices $\Delta_{\lambda_1}\times\dots\times\Delta_{\lambda_M}$, a polytope of dimension $\sum_m\lambda_m-M$ whose vertices are exactly the patterns. For $M\ge2$ the patterns are not in general position, so Cover's count $2\sum_{k=0}^{N-1}\binom{P-1}{k}$ for $P$ points in general position does not apply.

**Counting theorem ($M=2$).** For two modules the number of linearly separable dichotomies of $C_{(\lambda_1,\lambda_2)}$ is

$$N_{\lambda_1,\lambda_2}=\sum_{k=0}^{\min(\lambda_1,\lambda_2)}(k!)^2\,S(\lambda_1+1,k+1)\,S(\lambda_2+1,k+1),$$

where $S(n,k)$ are Stirling numbers of the second kind; this is a poly-Bernoulli number. On the diagonal $N_{\lambda,\lambda}$ grows like a constant multiple of $(2\lambda)!/(2\log 2)^{2\lambda}$, a vanishing fraction of all $2^{\lambda^2}$ dichotomies. For any $M$, the number of two-field arrangements is $\tfrac12\sum_{m=1}^M\lambda_m(\lambda_m-1)\prod_{n\ne m}\lambda_n$.

## Expansion

With non-negative weights and cells ordered by weight within each module, the inactive set of a perceptron is a down-closed lattice set, i.e. an $M$-dimensional Young diagram in $\{1,\dots,\lambda_1\}\times\dots\times\{1,\dots,\lambda_M\}$. Each realizable diagram accounts for a multinomial number of dichotomies obtained by permuting cells within modules, and for $M=2$ every Young diagram is realizable, so summing over diagrams by their numbers of distinct row and column lengths gives the Stirling-number formula. For $M\ge3$ all realizable arrangements are still Young diagrams, but not every diagram is realizable.

## Sources

- M. Y. Yim, L. A. Sadun, I. R. Fiete, T. Taillefumier, "Place-cell capacity and volatility with grid-like inputs", eLife 10 (2021) e62702, Appendix: Propositions 1, 2, 3, 4, 6 and 8, Equations (10), (17), (36), (47) and (62), <https://doi.org/10.7554/eLife.62702>, PMCID PMC8294848.
