# Circular split weights by non-negative least squares

**Circular split systems.** Let $X$ be a set of $n$ taxa. A split $A|B$ is a bipartition of $X$ into non-empty parts; its split pseudometric is $\delta_{A|B}(i,j) = 1$ if $A|B$ separates $i$ and $j$ and $0$ otherwise. A split system $\mathcal S$ is **circular** if there is an ordering $\theta = (x_1, \dots, x_n)$ such that, for every split, the part not containing $x_1$ is a contiguous interval of $\theta$. For a fixed $\theta$ the compatible splits are the $\binom n2$ interval splits

$$S_{pq} = \{x_p, \dots, x_q\} \mid X \setminus \{x_p, \dots, x_q\}, \qquad 1 < p \le q \le n,$$

and non-negative weights $\lambda$ define the circular metric $\hat d = \sum_{S \in \mathcal S} \lambda_S\, \delta_S$, the network analogue of an additive tree metric. A circular weighted split system can be drawn as a planar split network with the taxa on its outer boundary in the order $\theta$.

**Estimation problem.** Given observed distances $d$ and an ordering $\theta$, NeighborNet chooses

$$\hat\lambda = \arg\min_{\lambda \ge 0} \sum_{i<j} \big(d_{ij} - \hat d_{ij}\big)^2 = \arg\min_{\lambda \ge 0} \|A\lambda - d\|_2^2,$$

where $A$ is the $\binom n2 \times \binom n2$ 0/1 matrix with $A_{(ij), S} = \delta_S(i,j)$.

**Fast linear algebra.** Although $A$ is dense, the products $A\lambda$, $A^{\mathsf T} y$ and $A^{-1} y$ can each be evaluated in $O(n^2)$ time, linear in the number of entries, by recursions over the interval structure. The inverse is the **combinatorial Crofton formula**: if $d$ is exactly circular for $\theta$, the weight of the interval split $\{x_p,\dots,x_q\}$ is

$$\lambda_{pq} = \tfrac12\big(d(x_{p-1}, x_q) + d(x_p, x_{q+1}) - d(x_{p-1}, x_{q+1}) - d(x_p, x_q)\big),$$

with indices taken cyclically. Consequently, if $A^{-1}d \ge 0$ then $\lambda = A^{-1}d$ is the NNLS optimum and is obtained in $O(n^2)$ time; otherwise iterative NNLS methods (active set, projected gradient, conjugate gradient variants) start from $\max(A^{-1}d, 0)$ and stop when the projected gradient

$$g_S = \begin{cases}\nabla f(\lambda)_S & \lambda_S > 0,\\ \min(\nabla f(\lambda)_S, 0) & \lambda_S = 0\end{cases}$$

satisfies $\|g\|_2 < \delta$, since $g = 0$ characterizes the NNLS optimum.

## Expansion

An interval split separates $x_i$ from $x_j$ exactly when the interval contains one but not the other, so the four-term combination in the Crofton formula cancels every split except the one with endpoints exactly $p$ and $q$. The matrix is badly conditioned (numerical estimates of $\kappa_2(A)$ for $n \le 50$ grow rapidly with $n$), so convergence thresholds must scale with $\|A^{\mathsf T}d\|_2$ rather than being fixed. The first stage of NeighborNet builds $\theta$ agglomeratively, linking clusters into a growing cycle with a neighbor-joining-style selection criterion instead of into a tree, and the third stage draws the planar network from the weighted splits.

## Sources

- D. Bryant, D. H. Huson, "NeighborNet: improved algorithms and implementation", Frontiers in Bioinformatics 3:1178600 (2023), Sections 2–4 (circularity, the NNLS formulation, Eqs 3–13 for fast products and the Crofton inversion, and the projected-gradient stopping rule), <https://doi.org/10.3389/fbinf.2023.1178600>, PMCID PMC10548196.
