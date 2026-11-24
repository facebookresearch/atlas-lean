# f-statistics of a sample taken on an ancestral lineage

In a [drift model](drift-model.md) with [binary loadings](has-binary-loadings.md) and drift lengths $\ell$, let a sample $S$ have [lineage](lineage.md) $L_S \subseteq L_X$, as for an
ancient sample taken at an internal node on the lineage of $X$. Then, for all populations $Y$ and $Z$,

$$f_2(S, X) = \sum_{e \in L_X \setminus L_S} \ell_e, \qquad f_3(S; X, Y) = \sum_{e \in (L_X \cap L_Y) \setminus L_S} \ell_e,$$

$$f_4(X, S; Y, Z) = \sum_{e \in L_X \setminus L_S} \bigl(\mathbf 1[e \in L_Y] - \mathbf 1[e \in L_Z]\bigr)\, \ell_e .$$

These follow from [$f_2$ as a symmetric-difference length](f2-eq-sum-symm-diff.md) and the expressions of [$f_3$](f3-eq-f2.md) and [$f_4$](f4-eq-f2.md) through $f_2$: an edge of $L_S$ lies in
$L_X$ and contributes to none of the sums. On a tree, $f_2(S, X)$ is the drift from $S$ down to $X$, $f_3(S; X, Y)$ the drift from $S$ to the
path joining $X$ and $Y$, and $f_4(X, S; Y, Z)$ counts the edges below $S$ on the lineage of $X$, with sign $+$ for those on the lineage of $Y$ but not of $Z$,
$-$ for those on the lineage of $Z$ but not of $Y$, and $0$ for the rest. In particular $f_4(X, S; Y, Z) = 0$ when every edge of
$L_X \setminus L_S$ lies on both or neither of the lineages of $Y$ and $Z$, and $f_2(S, S') = 0$ for two samples with the same lineage. The sample has no drift of its own after it was taken.

## Depends on

- [Admixture-graph drift model](drift-model.md)
- [Lineage of a population in the drift model](lineage.md)

## Proof depends on

- [f2 as a symmetric-difference drift length under binary loadings](f2-eq-sum-symm-diff.md)
- [f3 in terms of f2](f3-eq-f2.md)
- [f4 in terms of f2](f4-eq-f2.md)

## Sources

- N. Patterson, P. Moorjani, Y. Luo, S. Mallick, N. Rohland, Y. Zhan, T. Genschoreck, T. Webster and D. Reich, "Ancient admixture in human history", Genetics 192 (2012), 1065–1093, <https://doi.org/10.1534/genetics.112.145037>. The identities are derived above.
