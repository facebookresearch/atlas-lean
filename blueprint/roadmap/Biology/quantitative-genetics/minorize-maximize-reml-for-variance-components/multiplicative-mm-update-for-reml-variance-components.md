# Multiplicative MM update for REML variance components

**Model.** Let $y \in \mathbb{R}^n$ satisfy $y \sim \mathcal{N}(X\beta, \Sigma_\gamma)$ with $X \in \mathbb{R}^{n \times p}$ of full column rank, $\gamma = (\sigma_1^2, \dots, \sigma_K^2) \in (0, \infty)^K$, and

$$\Sigma_\gamma = \sum_{k=1}^{K} \sigma_k^2 V_k,$$

where $V_1, \dots, V_K$ are known positive semidefinite $n \times n$ matrices whose combination is positive definite (for example a genomic relationship matrix, an environment design matrix, and $V_K = I_n$ for the residual). With

$$P_\gamma = \Sigma_\gamma^{-1} - \Sigma_\gamma^{-1} X (X^\top \Sigma_\gamma^{-1} X)^{-1} X^\top \Sigma_\gamma^{-1},$$

the restricted log-likelihood is, up to a constant,

$$L_R(\gamma) = -\tfrac12 \Bigl[ \log|\Sigma_\gamma| + \log|X^\top \Sigma_\gamma^{-1} X| + y^\top P_\gamma y \Bigr].$$

**MM principle.** If $g^{(t+1)}(\gamma) \ge -L_R(\gamma)$ for all $\gamma$ with equality at the current iterate $\gamma^{(t)}$, then $\gamma^{(t+1)} = \arg\min g^{(t+1)}$ satisfies $L_R(\gamma^{(t+1)}) \ge L_R(\gamma^{(t)})$.

**Proposition (surrogate).** The function

$$g^{(t+1)}(\gamma) = \tfrac12 \sum_{k=1}^{K} \Bigl[ \sigma_k^2\, \mathrm{tr}\bigl(P_{\gamma^{(t)}} V_k\bigr) + \frac{\sigma_k^{4\,(t)}}{\sigma_k^2}\, y^\top P_{\gamma^{(t)}} V_k P_{\gamma^{(t)}} y \Bigr] + c^{(t)},$$

with $c^{(t)}$ independent of $\gamma$, majorizes $-L_R$ and touches it at $\gamma^{(t)}$.

**Update.** The surrogate separates across components; setting $\partial g / \partial \sigma_k^2 = 0$ gives

$$\sigma_k^{2\,(t+1)} = \sigma_k^{2\,(t)} \sqrt{\frac{y^\top P_{\gamma^{(t)}} V_k P_{\gamma^{(t)}} y}{\mathrm{tr}\bigl(P_{\gamma^{(t)}} V_k\bigr)}}, \qquad k = 1, \dots, K .$$

Positive starting values stay positive, $L_R$ is non-decreasing along the iterates, and a fixed point with all $\sigma_k^2 > 0$ satisfies the REML score equations $y^\top P V_k P y = \mathrm{tr}(P V_k)$.

## Depends on

- [Restricted log-likelihood of an error contrast](../../../Probability/linear-models-multivariate/ordinary-least-squares/restricted-residual-maximum-likelihood-error-con/reml-log-lik.md)

## Expansion

The surrogate combines two inequalities. The log-determinant part $\log|\Sigma_\gamma| + \log|X^\top \Sigma_\gamma^{-1} X|$ equals $\log|M \Sigma_\gamma M^\top|$ plus a constant for any full-rank $M$ with $M X = 0$, and is concave in $\gamma$, so it lies below its tangent plane at $\gamma^{(t)}$, whose slope in $\sigma_k^2$ is $\mathrm{tr}(P_{\gamma^{(t)}} V_k)$. The quadratic part $y^\top P_\gamma y$ is bounded by a convexity argument applied to the matrix weights $\sigma_k^2 V_k$, giving the term $\sigma_k^{4\,(t)} y^\top P V_k P y / \sigma_k^2$, with equality at $\gamma^{(t)}$. Each step costs one $n \times n$ inversion; when $\sum_k n_k + p \ll n$ (few random-effect levels), the traces and quadratic forms can be computed from the Henderson mixed-model equations instead, and for $K = 2$ a simultaneous diagonalization of $V_1, V_2$ reduces each update to a scalar quadratic. A squared-extrapolation (SQUAREM) step on successive iterates accelerates convergence while keeping the monotonicity check.

## Sources

- F. Laporte, A. Charcosset, T. Mary-Huard, "Efficient ReML inference in variance component mixed models using a Min-Max algorithm", PLoS Computational Biology 18 (2022) e1009659, Methods, Equations (1)–(14), Propositions 1 and 2, section "Min-Max algorithm for ReML", <https://doi.org/10.1371/journal.pcbi.1009659> (PMC8824334).
- H. Zhou, L. Hu, J. Zhou, K. Lange, "MM algorithms for variance components models", Journal of Computational and Graphical Statistics 28 (2019) 350–361, <https://doi.org/10.1080/10618600.2018.1529601>.
