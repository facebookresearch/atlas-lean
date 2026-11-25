# Closed-form solution of the qpGraph normal equations

Let $\iota$ and $E$ be finite sets, $Q$ a real $\iota \times \iota$ matrix and $B$ a real $\iota \times E$ matrix such that $G = B^\top Q^{-1} B$ is invertible. Then for every $f \in \mathbb{R}^\iota$, the vector $\hat\ell = G^{-1} B^\top Q^{-1} f$ solves the normal equations $G \hat\ell = B^\top Q^{-1} f$.

For positive definite $Q$, $\hat\ell$ is the generalized least-squares estimate of the edge lengths ([it maximizes the score S1](score-s1-le-of-normal-eq.md)).
