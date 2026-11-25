# Mixed-model equations and the generalized least squares estimator

Let $X \in \mathbb{R}^{n\times p}$ and $Z \in \mathbb{R}^{n\times q}$, let $G \in \mathbb{R}^{q\times q}$ and $R \in \mathbb{R}^{n\times n}$ be positive definite, and let $V = ZGZ^\top + R$ with $X^\top V^{-1}X$ invertible. Then for $y \in \mathbb{R}^n$, a pair $(b, u)$ solves Henderson's mixed-model equations if and only if $b = (X^\top V^{-1}X)^{-1}X^\top V^{-1}y$ is the generalized least squares estimate and $u = GZ^\top V^{-1}(y - Xb)$.
