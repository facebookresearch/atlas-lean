# Pinch count changes only at the corners of a new cell

Let $S \subseteq \mathbb{Z}^2$ be a finite set of unit cells and $c \notin S$ a cell, and let $\pi_T(v) \in \{0, 1\}$ indicate that $v$ is a pinch point of $T$ and $P(T) = \sum_{v} \pi_T(v)$, the sum over the corners of cells of $T$, the number of pinch points. Then

$$P(S \cup \{c\}) = P(S) + \sum_{v \text{ corner of } c} \big(\pi_{S \cup \{c\}}(v) - \pi_S(v)\big).$$
