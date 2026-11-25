# Faithfulness

Let $b$ be a Bayesian network on nodes $\{0, \dots, n-1\}$ whose variables take values in a finite set, and let $P$ be a real weight on joint assignments. $P$ is faithful to the graph of $b$ if, for all pairwise disjoint sets of nodes $X$, $Y$, $Z$, $X$ is conditionally independent of $Y$ given $Z$ under $P$ exactly when $X$ and $Y$ are d-separated by $Z$ in $b$ (MIT 6.S091, Lecture 5, Definition 5.1; Kalisch and Bühlmann 2007, Section 2.1).
