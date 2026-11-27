# Faithfulness of the subtyping algorithm to paths

In an execution tree of [the Amadio–Cardelli algorithm](the-amadio-cardelli-subtyping-algorithm.md) with root $\Sigma, \varepsilon \supset \alpha \le \beta$, every node $\Sigma', \varepsilon \supset \alpha' \le \beta'$
determines a path $\pi$, read off from the arrow steps between the root and the node. At every node, either $\alpha'$ and $\beta'$ are both bound type variables or neither is, and
the first labels of the solutions of $\alpha'$ and $\beta'$ in $\varepsilon$ are, in this order, $T\alpha(\pi)$ and $T\beta(\pi)$ if $\pi$ is positive (it selects the domain of an
arrow an even number of times) and $T\beta(\pi)$ and $T\alpha(\pi)$ if $\pi$ is negative, since the arrow rule compares domains in reversed order. So a failing leaf
exhibits a path at which the trees are not related in the order the tree ordering requires there, which gives completeness of the algorithm: $\alpha \le_T \beta$
implies success. The source's statement of Lemma 4.3.6(2) gives the root order at every path; Section 3.4 defines the positive and negative paths that its
use in Proposition 4.3.7 needs.

## Depends on

- [The Amadio–Cardelli subtyping algorithm](the-amadio-cardelli-subtyping-algorithm.md)
- [Canonical forms and regular systems of equations](canonical-forms-and-regular-systems-of-equations.md)

## Sources

- R. M. Amadio and L. Cardelli, "Subtyping recursive types", *ACM Transactions on Programming Languages and Systems* 15(4):575–631, 1993, <http://lucacardelli.name/Papers/SRT.pdf>: Section 3.4 (positive and negative paths), Section 4.3, Lemma 4.3.6 (faithfulness of $\le_A$ w.r.t. paths) and Proposition 4.3.7 (completeness of $\le_A$).
