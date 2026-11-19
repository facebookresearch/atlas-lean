# Weighted degree

Let $V$ be a set, $E$ a finite set, and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$, with weights $w : E \to \mathbb{R}$. The weighted degree of $a \in V$ is

$$d(a) = \sum_{e \in E} w_e \big([e^- = a] + [e^+ = a]\big),$$

so a loop at $a$ counts twice. Loops contribute nothing to the Laplacian.
