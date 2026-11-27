# Dual Helly number of a concept class

Let $H \subseteq \{0,1\}^X$ be a concept class. For a labelled sample $S$ let $H_S = \{h \in H : h \text{ is consistent with } S\}$. The **dual Helly number** of $H$ is the smallest $k$ such that every set $S \subseteq X \times \{0,1\}$ of labelled examples, finite or infinite, with $H_S = \emptyset$ contains a subset $W \subseteq S$ with $|W| \le k$ and $H_W = \emptyset$; if no such $k$ exists the dual Helly number is infinite. Restricted to finite $S$, the same quantity is the largest size of a minimal non-realizable finite labelled sample (the hollow star number); the two agree whenever every $S$ with $H_S = \emptyset$ has a finite subset $W$ with $H_W = \emptyset$. For halfspaces in $\mathbb{R}^n$ the dual Helly number is $n+2$ by Helly's theorem.

## Sources

- O. Bousquet, S. Hanneke, S. Moran, N. Zhivotovskiy, "Proper Learning, Helly Number, and an Optimal SVM Bound", COLT (2020), arXiv:2005.11818.
