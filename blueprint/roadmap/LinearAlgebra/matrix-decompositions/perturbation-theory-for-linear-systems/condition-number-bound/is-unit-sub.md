# Small perturbations of an invertible element stay invertible

In a complete normed ring (for instance square matrices with an operator norm, or bounded operators on a Banach space), if $A$ is invertible and $\|E\|\,\|A^{-1}\| < 1$, then $A - E$ is invertible (J. W. Demmel, Math 221 Lecture 3 notes, UC Berkeley, 2024: "A-E invertible if norm(E) < 1/norm(inv(A))"). Indeed $A - E = A(1 - A^{-1}E)$, and the Neumann series $(1 - A^{-1}E)^{-1} = \sum_k (A^{-1}E)^k$ converges because $\|A^{-1}E\| \le \|A^{-1}\|\,\|E\| < 1$.
