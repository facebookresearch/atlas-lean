# Variance of the first unsatisfiable random k-SAT prefix

Fix $k\ge3$. For $n\ge k$, sample an infinite independent stream of proper uniform clauses as in the [random k-SAT model](proper-clause-stream-and-survival.md). Let $H_n$ be the first prefix length with no satisfying assignment, using $0$ as its real-valued representation if that length is infinite. Write $T_{n,B}=\min(H_n,\lfloor Bn\rfloor)$ on finite-failure outcomes, and $T_{n,B}=\lfloor Bn\rfloor$ if no prefix fails. Set $\ell_k(n)=\log(en)$ for $k=3$, and $\ell_k(n)=1$ otherwise; put $U_k=\log2/[-\log(1-2^{-k})]$.

There is a constant $C\ge0$ with $\operatorname{Var}(H_n)\le Cn\ell_k(n)$ for every $n\ge k$. For each $B>0$ there is a possibly different $C\ge0$ with the same upper bound for $\operatorname{Var}(T_{n,B})$. One $c>0$, depending only on $k$, satisfies $cn\le\operatorname{Var}(H_n)$ for all sufficiently large $n\ge k$, and for every $B>U_k$ the same $c$ satisfies $cn\le\operatorname{Var}(T_{n,B})$ for all sufficiently large $n\ge k$ (the size cutoff may depend on $B$).

**Conventions.** Use the product clause-stream law, the first-failure time on extended naturals, and the order of clipping and conversion to reals described above. The real variance is the real projection of the extended nonnegative variance; infinity projects to zero.

## Depends on

- [Proper-clause streams, survival and first failure](proper-clause-stream-and-survival.md)

## Expansion

Separate a lifetime or clause-replacement second-moment estimate for the upper variance bound from a lower-variance mechanism that still works after clipping all prefixes at each fixed $B>U_k$. Relate the two stopping times using the first-moment tail at the stated $U_k$, and prove finite second moments. Recover the common lower constant and the possible $B$-dependence of the onset; do not assert an extra logarithm is necessary at $k=3$.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SATVariance.lean#L54-L65)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/235.md)
- [Accompanying manuscript: Variance of the Random $k$-SAT Hitting Time](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Variance-of-the-Random-k-SAT-Hitting-Time-September-27-2026/article.pdf)
- [Background: Friedgut, *Sharp thresholds of graph properties, and the k-sat problem*, Journal of the American Mathematical Society 12 (1999), 1017–1054](https://doi.org/10.1090/S0894-0347-99-00305-7)
