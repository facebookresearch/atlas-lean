# Algebraic-connectivity criterion for stable partitions of predator–prey metapopulation networks

Consider $n$ habitat patches forming an undirected weighted graph $G$ with Laplacian $L$ ($L_{ii} = d_i = \sum_{j \sim i} w_{ij}$, $L_{ij} = -w_{ij}$). Prey $x_i$ and predators $y_i$ disperse along the edges at rates given by the edge weights:

$$
\dot x_i = f_i(x_i, y_i) + \sum_{j \ne i} w_{ij}(x_j - x_i), \qquad \dot y_i = g_i(x_i, y_i) + \sum_{j \ne i} w_{ij}(y_j - y_i).
$$

Assume each isolated patch is unstable at its coexistence equilibrium, with local Jacobian $J_i$ having complex eigenvalues of positive real part ($\det J_i \ge 0$, $(\operatorname{tr} J_i)^2 \le 4\det J_i$, $\operatorname{tr} J_i \ge 0$). Let $0 = \lambda_1 \le \lambda_2 \le \dots \le \lambda_n$ be the Laplacian spectrum and

$$
\tau = \tfrac12 \max_i \operatorname{tr} J_i .
$$

Decomposing the linearization along the eigenvectors of $L$ shows that the coexistence state of the network is stable when $\lambda_2(L) \ge \tau$: the dispersal-induced damping $\lambda_j$ outweighs the local growth rate $\tfrac12\operatorname{tr} J_i$ in every nonuniform mode.

**Theorem (partition tests).** Let $C$ be a component obtained by cutting edges of $G$.

1. If $\tau$ exceeds an upper bound for $\lambda_2(L(C))$, then $C$ is unstable.
2. If $\tau$ is below a lower bound for $\lambda_2(L(C))$, then $C$ is stable.
3. (Necessary condition) If a stable subgraph $G'$ is obtained by removing edges, then its mean weighted degree satisfies $\langle k \rangle \ge \frac{n-1}{n}\tau$.
4. (Sufficient condition for one edge) If $\mathbf{v} = \varepsilon_i - \varepsilon_j$ is an eigenvector of $L(G)$ with eigenvalue $\lambda \ne 0$, then deleting the edge $ij$ (with $w_{ij} \ne \lambda$) leaves a stable graph provided $w_{ij} \le (\lambda - \tau)/2$. The analogous statement holds for removing $r$ edges whose difference vectors are eigenvectors, as a rank-$r$ Laplacian perturbation.

## Expansion

Writing $X = \sum_j \xi_1^j \Phi_j$, $Y = \sum_j \xi_2^j \Phi_j$ in the Laplacian eigenbasis decouples the modes. In mode $j$ the growth rates $\sigma_j$ solve $\sigma^2 - \sigma(\operatorname{tr} J_i - 2\lambda_j) + (\lambda_j^2 - \lambda_j\operatorname{tr} J_i + \det J_i) = 0$, so stability needs $\lambda_j \ge \tfrac12\operatorname{tr} J_i$ for every $j > 1$. Item 3 follows from $\sum_i d_i = \operatorname{tr} L = \sum_j \lambda_j \ge (n-1)\tau$. Item 4 uses the fact that removing edge $ij$ subtracts $w_{ij}\mathbf{v}\mathbf{v}^\top$ from $L$, which, when $\mathbf{v}$ is an eigenvector, lowers exactly one eigenvalue by $2w_{ij}$. Standard lower and upper bounds for the Fiedler value (via minimum degree, edge cuts, diameter) make the test computable without knowing the growth parameters beyond $\tau$.

## Sources

- Dinesh Kumar, Jatin Gupta, Soumyendu Raha, "Ecologically Sustainable Partitioning of a Metapopulations Network", arXiv (2018). Section 2 (linearized stability conditions), Theorems 1-5. <https://doi.org/10.48550/arXiv.1801.03673>
