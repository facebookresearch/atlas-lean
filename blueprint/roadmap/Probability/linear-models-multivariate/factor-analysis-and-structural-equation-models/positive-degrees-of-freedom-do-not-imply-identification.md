# Positive degrees of freedom do not imply identification of a factor model

Consider the confirmatory two-factor model for $p = 5$ indicators with standardized uncorrelated factors ($\Phi = I$), in which factor $1$ loads only on items $1$–$3$ and factor $2$ only on items $4$–$5$, and $\Sigma = \Lambda\Phi\Lambda^{\mathsf T} + \Psi$ with diagonal $\Psi$. It has $10$ free parameters (five loadings and five uniquenesses) and $15$ distinct covariance entries, so its degrees of freedom are $5 > 0$, yet its parameters are not identified. The loadings $\Lambda_A$ with rows $(1, 0), (1, 0), (1, 0), (0, 1), (0, 1)$ and uniquenesses $\Psi_A = \operatorname{diag}(1, 1, 1, 4, 1)$, and the loadings $\Lambda_B$ with rows $(1, 0), (1, 0), (1, 0), (0, 2), (0, \tfrac12)$ and uniquenesses $\Psi_B = \operatorname{diag}(1, 1, 1, 1, \tfrac74)$, all uniquenesses positive, give the same covariance matrix, block diagonal with blocks $J_3 + I_3$ and $\begin{pmatrix} 5 & 1 \\ 1 & 2 \end{pmatrix}$, while their loadings on factor $2$ differ in magnitude.

Proof. In both cases the first block is $\mathbf 1\mathbf 1^{\mathsf T} + I_3 = J_3 + I_3$ and the off-diagonal blocks vanish. For the second block, $\Lambda_A$ gives $\begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix} + \operatorname{diag}(4, 1)$ and $\Lambda_B$ gives $\begin{pmatrix} 4 & 1 \\ 1 & \tfrac14 \end{pmatrix} + \operatorname{diag}(1, \tfrac74)$, both equal to $\begin{pmatrix} 5 & 1 \\ 1 & 2 \end{pmatrix}$.

## Background

- [Identification of a one-factor model from three indicators](identification-of-the-one-factor-model.md): identification of the one-factor model with nonzero loadings.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
