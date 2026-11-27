# Dual Helly number of a concept class

Let $H \subseteq \{0,1\}^X$ be a concept class. For a labelled sample $S$ let $H_S = \{h \in H : h \text{ is consistent with } S\}$. The **dual Helly number** $k_w$ of $H$ is the smallest $k$ such that every set $S \subseteq X \times \{0,1\}$ of labelled examples, finite or infinite, with $H_S = \emptyset$ contains a subset $W \subseteq S$ with $|W| \le k$ and $H_W = \emptyset$; if no such $k$ exists the dual Helly number is infinite. The **hollow star number** $k_o$ is the largest $k$ such that some labelled sequence $((x_1, y_1), \dots, (x_k, y_k))$ is not realizable by $H$ while each sequence obtained by flipping exactly one label is realizable ($\infty$ if there is no largest such $k$). Call $H$ **closed** if every $S$ with $H_S = \emptyset$ has a finite subset $W$ with $H_W = \emptyset$. Then $k_o \le k_w$, and $k_o = k_w$ whenever $k_w < \infty$ or $H$ is closed; the inequality can be strict for classes that are not closed (for the singletons on $\mathbb{N}$, $k_o = 2$ while $k_w = \infty$). For halfspaces in $\mathbb{R}^n$ the hollow star number is $n + 2$.

## Sources

- O. Bousquet, S. Hanneke, S. Moran, N. Zhivotovskiy, "Proper Learning, Helly Number, and an Optimal SVM Bound", COLT (2020), arXiv:2005.11818, Definitions 2 and 3, Lemma 5 and Examples 1 and 3.
