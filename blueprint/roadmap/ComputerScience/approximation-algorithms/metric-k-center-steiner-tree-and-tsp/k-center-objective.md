# The k-center objective

Given a finite set $V$ with a distance $d : V \times V \to \mathbb{R}_{\ge 0}$ and $k \ge 1$, the **radius** of a center set $S \subseteq V$ is $r(S) = \max_{v \in V} \min_{c \in S} d(v, c)$, and the **$k$-center problem** asks for $S$ with $|S| \le k$ minimizing $r(S)$; $r^*_k$ denotes the optimum. The distance is **metric** if it is symmetric, vanishes on the diagonal and satisfies the triangle inequality.

## Depends on

- [k-center instances](../../../TheoryOfComputation/np-completeness/set-systems-and-location/nonmetric-k-center/kcenter-instance.md)

## Sources

- D. P. Williamson and D. B. Shmoys, "The Design of Approximation Algorithms", Cambridge University Press, 2011.
- T. F. Gonzalez, "Clustering to Minimize the Maximum Intercluster Distance", Theoretical Computer Science 38, 1985.
