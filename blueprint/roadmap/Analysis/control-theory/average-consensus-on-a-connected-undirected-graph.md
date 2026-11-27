# Average consensus on a connected undirected graph

Let $G$ be a finite loopless undirected multigraph on the vertices $1, \dots, n$, $n \ge 2$, with positive edge weights, and let $L$ be its weighted Laplacian, so that $x^\top L x = \sum_{\{i, j\}} w_{ij}(x_i - x_j)^2$ summed over the edges. Consider the network of integrators $\dot x_i = \sum_{j} w_{ij}(x_j - x_i)$, that is $\dot x = -Lx$, and let $\bar x = \frac1n \mathbf{1}^\top x(0)$ be the initial average.

1. **Conservation.** $\mathbf{1}^\top x(t) = \mathbf{1}^\top x(0)$ for all $t$.
2. **Average consensus.** If $G$ is connected, then $x(t) \to \bar x\,\mathbf{1}$ as $t \to \infty$ for every initial state, that is, $e^{-tL} \to \frac1n \mathbf{1}\mathbf{1}^\top$.
3. **Rate.** The disagreement $\delta(t) = x(t) - \bar x\,\mathbf{1}$ satisfies $\|\delta(t)\| \le e^{-\lambda_2 t}\|\delta(0)\|$, where $\lambda_2$ is the second-smallest eigenvalue of $L$ (the algebraic connectivity), which is positive exactly when $G$ is connected.
4. **Necessity of connectivity.** If $G$ is not connected, the averages over each connected component are separately conserved, so states with different component averages do not reach a common value.

**Proof.** $\mathbf{1}^\top L = 0$ because $L$ is symmetric and $L\mathbf{1} = 0$, which gives part 1 and shows that $\mathbf{1}^\top\delta(t) = 0$. Since $\dot\delta = -L\delta$, $\frac{d}{dt}\|\delta\|^2 = -2\delta^\top L\delta \le -2\lambda_2\|\delta\|^2$, because $\delta \perp \mathbf{1}$ and $\lambda_2$ is the minimum of the Rayleigh quotient of $L$ on the vectors orthogonal to the constants. Grönwall's inequality gives part 3, and part 2 follows when $\lambda_2 > 0$. For part 4, the Laplacian is block diagonal over the components, and part 1 applied to each block shows that each component average is conserved.

## Proof depends on

- [Constants are in the kernel of the Laplacian](../../GraphTheory/algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/laplacian-mul-vec-one.md): $L\mathbf{1} = 0$
- [$\lambda_2$ bounds the Rayleigh quotient on vectors orthogonal to the constants](../../GraphTheory/algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/algebraic-connectivity-mul-le.md): $\delta^\top L\delta \ge \lambda_2\|\delta\|^2$ for $\delta \perp \mathbf{1}$
- [$\lambda_2 > 0$ exactly for connected multigraphs](../../GraphTheory/algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/algebraic-connectivity-pos-iff.md): positivity of the rate

## Sources

- R. Olfati-Saber and R. M. Murray, "Consensus problems in networks of agents with switching topology and time-delays", *IEEE Transactions on Automatic Control* 49(9), 2004 (preprint, <https://www.cds.caltech.edu/~murray/preprints/om04-tac.pdf>), Theorem 1 and Remark 4 (the Laplacian of a connected undirected graph has rank $n - 1$, and its quadratic form is the disagreement $\frac12\sum(x_j - x_i)^2$, p. 7), equation (14) ($\lambda_2$ as the minimal Rayleigh quotient on $\mathbf{1}^\perp$), Theorem 4 (protocol (A1), $\dot x = -Lx$, solves average consensus on strongly connected balanced digraphs, which include undirected graphs, p. 11), and Theorem 8 (the disagreement decays as $\|\delta(t)\| \le \|\delta(0)\|e^{-\kappa t}$ with $\kappa = \lambda_2$ of the mirror graph, p. 14). The component argument for part 4 is on the page.
