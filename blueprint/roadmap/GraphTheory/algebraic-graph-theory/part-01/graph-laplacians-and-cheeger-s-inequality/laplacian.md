# Weighted Laplacian of a multigraph

Let $V$ be a set, $E$ a finite set, and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a multigraph; loops $e^- = e^+$ are allowed), with weights $w : E \to \mathbb{R}$. The weighted Laplacian is the $V \times V$ matrix

$$L_w = B\, \mathrm{diag}(w)\, B^{\mathsf T} = \sum_{e \in E} w_e\, (\delta_{e^-} - \delta_{e^+})(\delta_{e^-} - \delta_{e^+})^{\mathsf T},$$

where $B$ is the oriented incidence matrix, $B_{x e} = [x = e^-] - [x = e^+]$ (D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, equation (3.3)). Loops contribute nothing.
