# Dual Helly number of a concept class

Let $H \subseteq \{0,1\}^X$ be a concept class. For a labelled sample $S$ let $H_S = \{h \in H : h \text{ is consistent with } S\}$. The **dual Helly number** of $H$ is the smallest $k$ such that for every finite realizable-by-each-$k$-subsample labelled sample $S$ — that is, every $k$ labelled examples of $S$ are consistent with some concept of $H$ — the whole sample $S$ is consistent with some concept of $H$; if no such $k$ exists the dual Helly number is infinite. Equivalently, every minimal non-realizable labelled sample has at most $k$ elements. For halfspaces in $\mathbb{R}^n$ the dual Helly number is $n+2$ by Helly's theorem.

## Sources

- O. Bousquet, S. Hanneke, S. Moran, N. Zhivotovskiy, "Proper Learning, Helly Number, and an Optimal SVM Bound", COLT (2020), arXiv:2005.11818.
