# Stochastic shielding error as a sum of edge importances

Let $X \in \mathbb{R}^n$ be the Ornstein–Uhlenbeck approximation of a population process on a directed graph with $n$ nodes and $m$ edges,

$$dX = LX\,dt + \sum_{k=1}^m B_k\,dW, \qquad B_k = \sigma_k \zeta_k e_k^{\top},$$

where $L = (A - D)^{\top}$ is the graph Laplacian built from the transition rates, $\zeta_k = e_{j(k)} - e_{i(k)}$ is the stoichiometry vector of edge $k$, $\sigma_k$ is its noise intensity (for a population, $\sigma_k^2 = \alpha_k \bar N_{i(k)}$, the mean flux), and the $W_k$ are independent Brownian motions. Fix a measurement vector $M \in \mathbb{R}^n$, for example $M \in \{0,1\}^n$ marking the conducting states of an ion channel, and the observable $Y = M^{\top}X$.

The **stochastic shielding approximation** keeps the mean dynamics but drops the noise of a subset $E' \subset E$ of edges: $d\tilde X = L\tilde X\,dt + \sum_{k \notin E'} B_k\,dW$, driven by the same Brownian motions, with $\tilde Y = M^{\top}\tilde X$.

**Theorem.** Suppose the graph is irreducible and $L$ is symmetric with orthonormal eigenpairs $(\lambda_i, v_i)$, $\lambda_1 = 0 > \lambda_2 \geq \dots \geq \lambda_n$. Then the stationary mean squared error is additive over the neglected edges,

$$R[E'] := \lim_{t \to \infty} \operatorname{Var}\bigl(\tilde Y(t) - Y(t)\bigr) = \sum_{k \in E'} R_k,$$

$$R_k = \sigma_k^2 \sum_{i=2}^n \sum_{j=2}^n \frac{-1}{\lambda_i + \lambda_j}\,(M^{\top}v_i)(v_i^{\top}\zeta_k)(\zeta_k^{\top}v_j)(v_j^{\top}M) \;\geq\; 0 .$$

Hence, among all reductions that suppress the noise of exactly $m - K'$ edges, the most accurate one (minimal $R[E']$) drops the edges with the smallest **edge importance** $R_k$. For the classical Hodgkin–Huxley potassium (5-state) and sodium (8-state) channel graphs under voltage clamp, this ranking reproduces the original stochastic shielding rule (keep the noise on edges between conducting and nonconducting states, drop it on edges between states of equal conductance) over all physiologically relevant voltages.

## Depends on

- [Edge decomposition of the stationary covariance of a first-order transition network](edge-decomposition-of-the-stationary-covariance-of-a-first-order-transition-network.md)

## Expansion

The deficiency $U = \tilde X - X$ solves $dU = LU\,dt - \sum_{k \in E'} B_k\,dW$, a linear SDE driven only by the neglected noises. Its stationary covariance is $\int_0^\infty e^{tL}\bigl(\sum_{k \in E'} \sigma_k^2 \zeta_k\zeta_k^{\top}\bigr)e^{tL}\,dt$, which is a sum over edges because the $W_k$ are independent. Expanding $e^{tL} = \sum_i e^{\lambda_i t}v_iv_i^{\top}$ and integrating $\int_0^\infty e^{(\lambda_i + \lambda_j)t}dt = -1/(\lambda_i + \lambda_j)$ gives $R_k$; the zero mode drops out because $v_1 \propto \mathbf{1}$ is orthogonal to every $\zeta_k$. Each $R_k = M^{\top}C_kM$ is the variance of a stationary Gaussian process and therefore nonnegative. Additivity reduces choosing the best edge subset, a priori one of $2^m$ options, to sorting $m$ numbers. A term vanishes only when $M$ or $\zeta_k$ is orthogonal to the corresponding eigenvector.

## Sources

- D. R. Schmidt, P. J. Thomas, "Measuring edge importance: a quantitative analysis of the stochastic shielding approximation for random processes on graphs", *Journal of Mathematical Neuroscience* 4 (2014) 6. Section 2.2 (Eqs. 3–8), Lemma 1 (Eqs. 9–10) with proof in Appendix C.2, and Section 4 (Hodgkin–Huxley potassium and sodium channels). <https://doi.org/10.1186/2190-8567-4-6>. PMCID: PMC4234999.
