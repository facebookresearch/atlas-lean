# Uniformity of the subtyping algorithm

If [the Amadio–Cardelli algorithm](the-amadio-cardelli-subtyping-algorithm.md) succeeds on $\alpha \le \beta$, then it succeeds on $\alpha|_k \le \beta|_k$ for every $k$, where $|_k$ is the
cut at level $k$ of the [tree ordering](tree-ordering-on-recursive-types.md). The successful execution tree for the cut types is obtained by replacing each assumption leaf by a renamed
copy of the whole tree, as often as needed. Together with the μ-free case this gives soundness of the algorithm: success implies $\alpha \le_T \beta$.

## Depends on

- [The Amadio–Cardelli subtyping algorithm](the-amadio-cardelli-subtyping-algorithm.md)
- [The tree ordering on recursive types](tree-ordering-on-recursive-types.md)

## Proof depends on

- [The subtyping algorithm on μ-free types](subtyping-algorithm-on-non-recursive-types.md)

## Sources

- R. M. Amadio and L. Cardelli, "Subtyping recursive types", *ACM Transactions on Programming Languages and Systems* 15(4):575–631, 1993, <http://lucacardelli.name/Papers/SRT.pdf>: Section 4.3, Lemma 4.3.4 (uniformity of $\le_A$) and Proposition 4.3.5 (soundness of $\le_A$).
