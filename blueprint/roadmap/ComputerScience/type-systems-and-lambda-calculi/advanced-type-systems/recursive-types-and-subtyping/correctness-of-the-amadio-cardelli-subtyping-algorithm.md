# Correctness of the Amadio–Cardelli subtyping algorithm

For all recursive types $\alpha$ and $\beta$, [the Amadio–Cardelli algorithm](the-amadio-cardelli-subtyping-algorithm.md) succeeds on $\alpha \le \beta$, written $\alpha \le_A \beta$, if and only if
$\alpha \le_T \beta$ in the [tree ordering](tree-ordering-on-recursive-types.md). Since execution trees are finite, the tree ordering, and equality of tree expansions, are decidable.

## Depends on

- [The Amadio–Cardelli subtyping algorithm](the-amadio-cardelli-subtyping-algorithm.md)
- [The tree ordering on recursive types](tree-ordering-on-recursive-types.md)

## Proof depends on

- [Uniformity of the subtyping algorithm](uniformity-of-the-subtyping-algorithm.md)
- [Faithfulness of the subtyping algorithm to paths](faithfulness-of-the-subtyping-algorithm-to-paths.md)

## Sources

- R. M. Amadio and L. Cardelli, "Subtyping recursive types", *ACM Transactions on Programming Languages and Systems* 15(4):575–631, 1993, <http://lucacardelli.name/Papers/SRT.pdf>: Section 4.3, Proposition 4.3.5 (soundness of $\le_A$) and Proposition 4.3.7 (completeness of $\le_A$).
