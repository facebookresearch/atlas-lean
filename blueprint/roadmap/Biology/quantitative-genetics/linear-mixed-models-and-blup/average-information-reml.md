# Average-information REML

Let $y \sim N(X b, V)$ with $X$ an $n \times p$ fixed-effect design of full column rank and $V = \sum_{i=1}^{r} \sigma_i V_i$ positive definite, where the $V_i$ are known symmetric matrices and $\sigma = (\sigma_1, \dots, \sigma_r)$ are variance parameters. Put

$$P = V^{-1} - V^{-1} X (X^\top V^{-1} X)^{-1} X^\top V^{-1}.$$

The restricted (REML) log-likelihood $\ell_R(\sigma) = -\tfrac12\bigl(\log\det V + \log\det(X^\top V^{-1} X) + y^\top P y\bigr) + \text{const}$ has score and information

$$\frac{\partial \ell_R}{\partial \sigma_i} = -\tfrac12\bigl(\operatorname{tr}(P V_i) - y^\top P V_i P y\bigr),$$

$$\mathcal I^{O}_{ij} = -\frac{\partial^2 \ell_R}{\partial \sigma_i \partial \sigma_j} = -\tfrac12 \operatorname{tr}(P V_i P V_j) + y^\top P V_i P V_j P y, \qquad \mathcal I^{E}_{ij} = E\,\mathcal I^{O}_{ij} = \tfrac12 \operatorname{tr}(P V_i P V_j).$$

The **average information** matrix is their mean,

$$\mathcal I^{A}_{ij} = \tfrac12\bigl(\mathcal I^{O}_{ij} + \mathcal I^{E}_{ij}\bigr) = \tfrac12\, y^\top P V_i P V_j P y.$$

The matrix $\mathcal I^{A}$ is a Gram matrix: with $u_i = V_i P y$ it equals $\tfrac12 (u_i^\top P u_j)$, so it is positive semidefinite and needs no traces of $n \times n$ products. At an iterate $\sigma^{(t)}$ where $\mathcal I^{A}$ is nonsingular, AI-REML takes the step $\sigma^{(t+1)} = \sigma^{(t)} + (\mathcal I^{A})^{-1} \nabla \ell_R(\sigma^{(t)})$. Positive semidefiniteness does not give invertibility: with $V_1 = V_2 = I$ and $\sigma_1 + \sigma_2 > 0$, $V$ is positive definite but $u_1 = u_2$, so $\mathcal I^{A}$ has identical rows and is singular.

## Depends on

- [BLUP is the conditional expectation](cond-exp-mixed-model.md)

## Proof depends on

None beyond matrix calculus for $\log\det$ and inverses, $PX = 0$, $PVP = P$ and the expectation of a quadratic form, as the Expansion describes.

## Expansion

Use $\partial V / \partial \sigma_i = V_i$, $\partial P / \partial \sigma_i = -P V_i P$ and $\partial \log\det(\cdot)$ identities to get the score; differentiating again gives $\mathcal I^O$, with no second derivatives of $V$ because $V$ is linear in $\sigma$. Since $PX = 0$, $P V P = P$ and $E[y y^\top] = V + Xbb^\top X^\top$, one gets $E[y^\top P V_i P V_j P y] = \operatorname{tr}(P V_i P V_j P V) = \operatorname{tr}(P V_i P V_j)$, which yields $\mathcal I^E$; the trace terms cancel in the average.

## Sources

- A. R. Gilmour, R. Thompson and B. R. Cullis, "Average information REML: an efficient algorithm for variance parameter estimation in linear mixed models", *Biometrics* 51 (1995), 1440–1450, <https://doi.org/10.2307/2533274>.
