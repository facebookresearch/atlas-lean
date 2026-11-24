# Henderson's rules for the inverse numerator relationship matrix

Order a pedigree with parents before offspring, let $A$ be its numerator relationship matrix, and write each breeding value as $u_i = \frac12 u_s + \frac12 u_d + m_i$, the parent average plus an independent Mendelian sampling term, so that $u = P u + m$ with $P$ holding the entries $\frac12$ at (offspring, known parent) positions. Then $u = L m$ with $L = (I - P)^{-1}$ unit lower triangular, $\operatorname{var}(m) = D \sigma_u^2$ with $D$ diagonal, and $A = L D L^\top$, where
$$d_i = \tfrac12 - \tfrac14 (F_s + F_d) \ \text{(both parents known)}, \qquad d_i = \tfrac34 - \tfrac14 F_s \ \text{(only parent $s$ known)}, \qquad d_i = 1 \ \text{(neither known)},$$
with $F$ the inbreeding coefficients of the parents. Hence $A^{-1} = (L^{-1})^\top D^{-1} L^{-1}$ with $L^{-1} = I - P$, and $A^{-1}$ is assembled by adding, for each individual $i$, $d_i^{-1}$ times $1$ at $(i, i)$, $-\frac12$ at the (individual, known parent) positions and $\frac14$ at the positions indexed by pairs of known parents. Without inbreeding these are Henderson's rules: add $2$, $-1$, $\frac12$ when both parents are known, $\frac43$, $-\frac23$, $\frac13$ when one is known, and $1$ when neither is.

## Depends on

- [Malécot's recursion computes gene-dropping kinship](../../../Biology/quantitative-genetics/pedigree-kinship-and-inbreeding/gene-drop-kinship-eq-kinship.md)

## Expansion

1. The model: pedigree order, the relationship matrix $A$ with $A_{ii} = 1 + F_i$ and $A_{sd} = 2F_i$ for the parents $s$, $d$ of $i$.
2. The Mendelian-sampling decomposition and the variances $d_i$ in the three cases.
3. The factorization $A = L D L^\top$, the identity $L^{-1} = I - P$, and the assembly rules for $A^{-1}$.
4. The use of $A^{-1}$ in [Henderson's mixed-model equations](../../../Biology/statistical-genetics/bolt-lmm-mixed-model-association/is-mmesolution-iff.md).

## Sources

- P. von Rohr, Inverse numerator relationship matrix, course slides, Livestock Breeding and Genomics, 2021.
- Original result: C. R. Henderson, A simple method for computing the inverse of a numerator relationship matrix used in prediction of breeding values, Biometrics 32 (1976), 69–83. <https://doi.org/10.2307/2529339> The decomposition and the assembly rules follow von Rohr's slides.
