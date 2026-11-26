# The plookup grand-product identity for sorted concatenations

Let $\mathbf{t}\in\mathbb{F}^{d}$ and $\mathbf{f}\in\mathbb{F}^{n}$, and let $\mathbf{s}\in\mathbb{F}^{n+d}$ be the concatenation of $\mathbf{f}$ and $\mathbf{t}$ sorted by the order in which values appear in $\mathbf{t}$. Then $\{f_i\}\subseteq\{t_j\}$ and $\mathbf{s}$ is such a sorted concatenation iff, as polynomials in $\beta,\gamma$,

$$
(1+\beta)^{n}\prod_{i=1}^{n}(\gamma+f_i)\prod_{i=1}^{d-1}\bigl(\gamma(1+\beta)+t_i+\beta t_{i+1}\bigr)=\prod_{i=1}^{n+d-1}\bigl(\gamma(1+\beta)+s_i+\beta s_{i+1}\bigr).
$$

Checking it at random $(\beta,\gamma)$ by a grand-product argument has soundness error at most $(n+d)/|\mathbb{F}|$.

## Proof sketch

The right side's factors encode the multiset of consecutive pairs $(s_i,s_{i+1})$. When $\mathbf{s}$ is sorted by $\mathbf{t}$, each adjacent pair is either a repeated value $(v,v)$, contributing $(1+\beta)(\gamma+v)$, or a consecutive table pair $(t_j,t_{j+1})$; the repeated pairs correspond exactly to the entries of $\mathbf{f}$. Conversely, polynomial equality forces the multiset of difference pairs to match, which forces each $f_i$ to occur in $\mathbf{t}$. Schwartz–Zippel bounds the random-evaluation error.

## Depends on

- [Lookup relations with multiplicities](lookup-relation.md)
- [Grand-product permutation argument with random linear combinations](../plonkish-polynomial-iops/plonk-permutation-argument.md)

## Proof depends on

- [Grand-product permutation argument with random linear combinations](../plonkish-polynomial-iops/plonk-permutation-argument.md)

## Sources

- Ariel Gabizon, Zachary J. Williamson, "plookup: A Simplified Polynomial Protocol for Lookup Tables", IACR ePrint 2020/315 (2020).
