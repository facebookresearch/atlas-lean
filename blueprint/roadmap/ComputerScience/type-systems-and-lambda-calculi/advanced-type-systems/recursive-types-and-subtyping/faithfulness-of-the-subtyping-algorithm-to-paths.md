# Faithfulness of the subtyping algorithm to paths

In an execution tree of [the Amadio–Cardelli algorithm](the-amadio-cardelli-subtyping-algorithm.md) with root $\Sigma, \varepsilon \supset \alpha \le \beta$, every node $\Sigma', \varepsilon \supset \alpha' \le \beta'$
determines a path $\pi$, read off from the arrow steps between the root and the node. At every node, either $\alpha'$ and $\beta'$ are both bound type variables or neither is, and
the first labels of the solutions of $\alpha'$ and $\beta'$ in $\varepsilon$ are $T\alpha(\pi)$ and $T\beta(\pi)$. So a failing leaf exhibits a path at which the trees are not related, which
gives completeness of the algorithm: $\alpha \le_T \beta$ implies success.

## Depends on

- [The Amadio–Cardelli subtyping algorithm](the-amadio-cardelli-subtyping-algorithm.md)
- [Canonical forms and regular systems of equations](canonical-forms-and-regular-systems-of-equations.md)

## Sources

- R. M. Amadio and L. Cardelli, "Subtyping recursive types", *ACM Transactions on Programming Languages and Systems* 15(4):575–631, 1993, <http://lucacardelli.name/Papers/SRT.pdf>: Section 4.3, Lemma 4.3.6 (faithfulness of $\le_A$ w.r.t. paths) and Proposition 4.3.7 (completeness of $\le_A$).
