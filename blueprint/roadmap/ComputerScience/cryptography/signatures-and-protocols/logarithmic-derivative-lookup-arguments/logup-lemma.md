# Logarithmic-derivative characterization of set inclusion

Let $\mathbb{F}$ have characteristic $p>\max(n,T)$, let $t_1,\dots,t_T$ be pairwise distinct, and $f_1,\dots,f_n\in\mathbb{F}$. Then $\{f_i\}\subseteq\{t_j\}$ iff there exist $m_1,\dots,m_T\in\mathbb{F}$ with

$$
\sum_{i=1}^{n}\frac{1}{X-f_i}=\sum_{j=1}^{T}\frac{m_j}{X-t_j}
$$

as rational functions in $\mathbb{F}(X)$; in that case $m_j$ is the multiplicity of $t_j$ among the $f_i$.

## Proof sketch

If the inclusion holds, group the left side by value. Conversely, the left side has a pole at each distinct $f_i$ with residue equal to its multiplicity, which is a positive integer less than $p$ and hence nonzero in $\mathbb{F}$; the right side has poles only at the $t_j$. Uniqueness of partial fraction decompositions forces every $f_i$ to be some $t_j$ with $m_j$ its multiplicity.

## Depends on

- [Lookup relations with multiplicities](lookup-relation.md)

## Sources

- Ulrich Haböck, "Multivariate Lookups Based on Logarithmic Derivatives", IACR ePrint 2022/1530 (2022).
