---
article_id: af_8e480a4ecd966ad51ab2c98d
declaration: theorem
origin: cited
lean: index_calculus_relation
---

# Algorithm 10.1 (Index calculus)

Given $\beta \in \langle\alpha\rangle = (\mathbb{Z}/p\mathbb{Z})^{\times}$, compute $\log_{\alpha} \beta$ as follows:
1. Pick a smoothness bound $B$, compute the factor base $P_B \coloneqq \{p_1, \ldots, p_b\}$ with $b \coloneqq \pi(B)$, and let $N \coloneqq p-1$.
2. Generate $b+1$ random relations $R_i = (e_{i,1}, e_{i,2}, \ldots, e_{i,b}, 1, e_i)$ by picking $e \in [1, N]$ at random and attempting to factor $\alpha^e \beta^{-1} \in [1, N]$ over the factor base $P_B$. Each successful factorization yields a relation $R_i$ with $e_i = e$ and $\alpha^{e_i}\beta^{-1} = \prod p_j^{e_{i,j}}$.
3. Attempt to solve the system defined by the relations $R_1, \ldots, R_{b+1}$ for $x_{b+1} \in \mathbb{Z}/N\mathbb{Z}$ using linear algebra (row reduce the corresponding matrix).
4. If $x_{b+1} = \log_{\alpha} \beta$ is uniquely determined, return this value, otherwise go to step 2.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.783 Elliptic Curves (Spring 2021), Section 10.1](../../../../../sources/v1/EllipticCurves.md)
