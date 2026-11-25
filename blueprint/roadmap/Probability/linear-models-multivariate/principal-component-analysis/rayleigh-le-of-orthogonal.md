# Hotelling's characterization of the principal axes

Let $S$ be a real symmetric $p \times p$ matrix with eigenvalues $\lambda_0 \ge \lambda_1 \ge \dots \ge \lambda_{p-1}$ in decreasing order and a corresponding [ordered orthonormal eigenbasis](ordered-eigenbasis.md) $v_0, \dots, v_{p-1}$ of $\mathbb{R}^p$. Let $k \in \{0, \dots, p-1\}$ and $w \ne 0$ orthogonal to $v_0, \dots, v_{k-1}$. Then the Rayleigh quotient $R_S(w) = w^\top S w / w^\top w$ satisfies

$$R_S(w) \le \lambda_k,$$

with equality at $w = v_k$ ([Rayleigh quotient of an eigenvector](rayleigh-ordered-eigenbasis.md)).

## Sources

- H. Hotelling, *Analysis of a complex of statistical variables into principal components*, J. Educ. Psychol. 24 (1933), 417–441.
