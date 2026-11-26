# Community epidemic thresholds are bounded below by the global threshold

**Model.** On a connected undirected network $G = (V,E)$ with adjacency matrix $A$, the discrete-time SIS model of Chakrabarti et al. updates the infection probability $p_i(t)$ of node $i$ by

$$p_i(t+1) = 1 - \big[(1-p_i(t)) + \delta p_i(t)\big]\prod_{j=1}^n\big(1 - \beta A_{ij}p_j(t)\big).$$

Here $\beta$ is the per-edge transmission probability per step and $\delta$ the recovery probability. The epidemic threshold is $\tau = 1/\lambda_1(A)$, where $\lambda_1$ is the spectral radius: if $\beta/\delta < \tau$, all $p_i(t)\to 0$ exponentially fast.

Partition $V$ into $K$ disjoint connected communities $C_1,\dots,C_K$ with induced adjacency matrices $A_g$. Define the **local thresholds** $\tau_g = 1/\lambda_1(A_g)$, and call the ordered tuple $\mathcal{T}_A = (\tau_1,\dots,\tau_K)$ the **epidemic threshold set** of $G$, indexed so that $\tau_1\le\cdots\le\tau_K$.

**Theorem.** For every community, $\tau_g \ge \tau$. Hence

$$\tau \le \tau_1 \le \tau_2 \le \cdots \le \tau_K .$$

**Corollaries.**

1. If the effective spreading rate is below the global threshold, $\beta/\delta < \tau$, then it is below every local threshold, so the epidemic cannot break out within any community taken in isolation.
2. If an epidemic can break out within some community in isolation, $\beta/\delta > \tau_g$ for some $g$, then $\beta/\delta > \tau$ and it breaks out on the whole network.

The most fragile community, the one with the smallest $\tau_g$, gives the tightest community-level warning, and $\tau_1 - \tau \ge 0$ measures how much inter-community edges lower the threshold.

## Expansion

After permuting $V$ so that $C_g$ comes first, $A = \begin{pmatrix} A_g & R\\ R^\top & A_{\bar g}\end{pmatrix}$. Let $u_g$ be a unit Perron eigenvector of $A_g$ and $\tilde u_g = (u_g, 0)$. By the Rayleigh quotient for the symmetric matrix $A$, $\lambda_1(A) \ge \tilde u_g^\top A\tilde u_g = u_g^\top A_g u_g = \lambda_1(A_g)$. So the spectral radius of a principal submatrix never exceeds that of the whole nonnegative matrix, and taking reciprocals gives $\tau_g \ge \tau$. For a connected $G$ and a proper community the inequality is in fact strict, since $A$ is irreducible and Perron–Frobenius theory makes the spectral radius of a proper principal submatrix strictly smaller.

## Depends on

- [Spectral radius and die-out of SIS epidemics on graphs](../epidemics-on-networks/spectral-radius-and-die-out-of-sis-epidemics.md)

## Sources

- H. P. Dung and N. H. Phuc, "An Epidemic Threshold Set for Networks", arXiv:2607.14048 (2026), Definitions 1–3, Theorem 1 and Corollaries 1–2, <https://doi.org/10.48550/arXiv.2607.14048>.
- D. Chakrabarti, Y. Wang, C. Wang, J. Leskovec and C. Faloutsos, "Epidemic thresholds in real networks", ACM Trans. Inf. Syst. Secur. (2008).
