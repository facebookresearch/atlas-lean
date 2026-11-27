# Augmenting walks remove two defects

Let $f$ be a valid labeling of an edge CSP whose constraints are even delta-matroids. The **forest search** grows a directed forest whose roots are the defects of $f$, alternating between variables and timestamped copies of constraints: it repeatedly picks a variable $v$ of the forest and an incident constraint $C$ such that no copy of $C$ is the parent or a child of $v$, adds a new copy of $C$ as a child of $v$, and examines every variable $w \neq v$ in the scope of $C$ with $f(C) \oplus v \oplus w \in C$: a $w$ not yet in the forest becomes a child of the new copy; a $w$ whose parent is a copy of the same constraint $C$ is skipped; and any other $w$ already in the forest (a root, or a variable whose parent is a copy of a different constraint) is a meeting of two branches, at which the search stops (Kazda, Kolmogorov and Rolínek, Algorithm 1, step 4).

- If they come from distinct roots, the concatenated **augmenting walk** $p$ (from one defect to another, with all intermediate variables consistent) is valid to flip: $f \oplus p$ is a valid labeling with exactly two fewer defects.
- If they come from the same root, they determine a **blossom**: a closed walk through the lowest common ancestor of the two branches. If that ancestor is a variable it is a defect and serves as the base; if it is a copy of a constraint, the labeling is first flipped along the forest path to the child $r$ of that ancestor on the branch of $v$, which keeps it valid, keeps the number of defects, and makes $r$ the defective base.

## Proof sketch

The forest stays an *$f$-DAG*: every incidence is used at most once, every variable has at most one incoming arc, timestamps order the nodes, every pair of arcs at a constraint copy entering at $u$ and continuing at $v$ is a feasible flip ($f(C) \oplus u \oplus v \in C$), and there are no shortcuts from an earlier copy of a constraint to a later one. Using the even delta-matroid exchange property at each constraint, flipping along such a DAG keeps every intermediate labeling valid, which gives both the augmentation and the blossom property.

## Depends on

- [Edge CSPs, occurrence labelings and defects](edge-csps-and-defects.md)
- [Delta-matroids and even delta-matroids](../../../../TheoryOfComputation/np-completeness/boolean-constraint-satisfaction/planar-boolean-csp/delta-matroids-and-even-delta-matroids.md)

## Sources

- A. Kazda, V. Kolmogorov and M. Rolínek, "Even Delta-Matroids and the Complexity of Planar Boolean CSPs", ACM Transactions on Algorithms 15(2), Article 22, 2019, Section 5.2, Lemma 25, Lemma 34, Corollary 36 and Proposition 38.
