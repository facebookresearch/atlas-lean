# Ancestral sampling from a chain

Let $c$ be a chain of conditional distributions $p_k(\cdot \mid y_0, \dots, y_{k-1})$ with values in a finite type $\alpha$. Ancestral (forward) sampling of the first $n$ variables is the probability mass function $S_n$ on $\alpha^n$ defined by recursion on $n$:

- $S_0$ is the point mass at the empty assignment;
- $S_{n+1}$ draws $y \sim S_n$, then $a \sim p_n(\cdot \mid y)$, and returns $(y_0, \dots, y_{n-1}, a)$.
