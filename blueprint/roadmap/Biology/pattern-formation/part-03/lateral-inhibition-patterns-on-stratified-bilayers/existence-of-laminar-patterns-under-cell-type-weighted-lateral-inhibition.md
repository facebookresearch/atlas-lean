# Existence of laminar patterns under cell-type-weighted lateral inhibition

**Model.** Cells are the vertices of an undirected connected graph $\mathcal G$ arranged as a bilayer of two cell types (luminal $L$ and basal $B$) with periodic boundaries, $N \in 2\mathbb N$ cells. Contact weights are $w_{ij} = w_1 > 0$ for touching cells of the same type, $w_{ij} = w_2 > 0$ for touching cells of different types, and $0$ otherwise. Every cell has $n_1$ same-type and $n_2$ other-type neighbours, so $N_w = n_1 w_1 + n_2 w_2$ and the cell-type ratio $R_\tau = n_1/n_2$ are the same for all cells. Each cell runs a single-input single-output (SISO) lateral-inhibition system

$$\dot{\mathbf x}_i = \mathbf f(\mathbf x_i, u_i), \qquad y_i = h(\mathbf x_i), \qquad u_i = \frac{1}{N_w} \sum_j w_{ij}\, y_j,$$

with $\mathbf f, h$ continuously differentiable (for Notch–Delta, $y_i$ is Delta and the input is the weighted average of neighbouring Delta). The static input–output characteristic $T = h \circ S$, where $S(u)$ is the steady state for constant input $u$, is assumed positive, bounded and decreasing, and $u^*$ is the homogeneous steady-state input, $u^* = T(u^*)$.

**Theorem (existence of laminar patterns).** Suppose the layers $P_L$ and $P_B$ are equitable partitions of $\mathcal G$ whose reduced graphs are bipartite. If $n_1 w_1 < n_2 w_2$ and

$$w_1 < \frac{|T'(u^*)| - 1}{|T'(u^*)| + 1} \cdot \frac{w_2}{R_\tau},$$

then there exist heterogeneous steady states in which all luminal cells share one state and all basal cells share another (a laminar pattern). In particular $|T'(u^*)| > 1$ is necessary for the bound to admit any $w_1 > 0$.

## Expansion

Equitability lets the $N \times N$ scaled adjacency matrix collapse to the $2 \times 2$ quotient matrix

$$\frac{1}{N_w} \overline{\mathbf W} = \frac{1}{N_w} \begin{pmatrix} n_1 w_1 & n_2 w_2 \\ n_2 w_2 & n_1 w_1 \end{pmatrix},$$

with eigenvalues $\lambda_1 = 1$ and $\lambda_2 = (n_1 w_1 - n_2 w_2)/N_w$. Under $n_1 w_1 < n_2 w_2$ the smallest eigenvalue is $\lambda_2 < 0$. The Rufino Ferreira–Arcak criterion for equitable bipartite partitions states that heterogeneous partition steady states exist when $|T'(u^*)|\, \lambda_{\min} < -1$; substituting $\lambda_2$ and dividing by $n_2$ gives the displayed bound. Larger same-type connectivity $R_\tau$ shrinks the admissible $w_1$, so laminar patterning demands stronger polarization of Delta signalling toward the other layer.

## Sources

- J. W. Moore, T. C. Dale, T. E. Woolley, "Algebraic framework for determining laminar pattern bifurcations by lateral-inhibition in 2D and 3D bilayer geometries", arXiv:2104.12142 (2021), sections "Theory" (lateral-inhibition model, graph partitioning and network stability) and "Theoretical results" (existence theorem for bilayer laminar patterns). <https://doi.org/10.48550/arXiv.2104.12142>
- Published version: J. W. Moore, T. C. Dale, T. E. Woolley, "Polarity-driven laminar pattern formation by lateral-inhibition in 2D and 3D bilayer geometries", IMA Journal of Applied Mathematics (2022), <https://doi.org/10.1093/imamat/hxac011>.
