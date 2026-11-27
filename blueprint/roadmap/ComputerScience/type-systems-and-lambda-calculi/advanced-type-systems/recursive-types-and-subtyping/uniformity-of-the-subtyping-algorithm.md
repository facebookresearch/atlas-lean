# Uniformity of the subtyping algorithm

If [the Amadio–Cardelli algorithm](the-amadio-cardelli-subtyping-algorithm.md) succeeds on $\alpha \le \beta$, then it succeeds on $\alpha|_k \le \beta|_k$ for every $k$, where $|_k$ is the
cut at level $k$ of the [tree ordering](tree-ordering-on-recursive-types.md). The successful execution tree for the cut types is extracted from the given one in two steps. First, the use of the assumption rule is
delayed: a leaf closed by an assumption $t \le s$ is replaced by a renamed copy of the earlier subderivation that introduced $t \le s$, with the equation environment
expanded by renamed copies of the equations it uses, until every branch reaches depth $k$. Second, the tree is truncated at depth $k$: the cut replaces a node
at depth $k$ by $\bot$ at a positive path and by $\top$ at a negative path, and since the goals at negative paths compare the two sides in reversed order, each goal at
depth $k$ closes by the $\bot$ axiom or by the $\top$ axiom. When the tree has no assumption leaf, only the truncation is needed: for $a \to a \le a \to a$ with a free
variable $a$, both cuts at depth $0$ are $\bot$ and the $\bot$ axiom closes the goal. The source's proof sketch shows the copying on an example in which the repeated
comparison is the root. Together with the μ-free case this gives soundness of the algorithm: success implies $\alpha \le_T \beta$.

## Depends on

- [The Amadio–Cardelli subtyping algorithm](the-amadio-cardelli-subtyping-algorithm.md)
- [The tree ordering on recursive types](tree-ordering-on-recursive-types.md)

## Proof depends on

- [The subtyping algorithm on μ-free types](subtyping-algorithm-on-non-recursive-types.md)

## Sources

- R. M. Amadio and L. Cardelli, "Subtyping recursive types", *ACM Transactions on Programming Languages and Systems* 15(4):575–631, 1993, <http://lucacardelli.name/Papers/SRT.pdf>: Section 4.3, Lemma 4.3.4 (uniformity of $\le_A$) and Proposition 4.3.5 (soundness of $\le_A$).
