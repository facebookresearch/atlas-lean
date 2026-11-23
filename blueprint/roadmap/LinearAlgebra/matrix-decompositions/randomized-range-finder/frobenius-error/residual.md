# Range-finder residual

For a real $m \times n$ matrix $A$ and a test matrix $\Omega \in \mathbb{R}^{n \times \ell}$, let $P_Y$ be the orthogonal projection of $\mathbb{R}^m$ onto the range of the sample matrix $Y = A\Omega$. The range-finder residual of $A$ for the test matrix $\Omega$ is the operator $(I - P_Y)A : \mathbb{R}^n \to \mathbb{R}^m$, whose norm is the error of the approximation $A \approx P_Y A = Q Q^* A$ with $Q$ an orthonormal basis of $\operatorname{range}(Y)$.

## Sources

- N. Halko, P.-G. Martinsson and J. A. Tropp, Finding structure with randomness: probabilistic algorithms for constructing approximate matrix decompositions, SIAM Rev. 53 (2011), 217–288, arXiv:0909.4061, §1.5, §4.1 and §9.1.
