# Solutions of the normal equations maximize the score S1

Let $\iota$ and $E$ be finite sets, $Q$ a positive definite real $\iota \times \iota$ matrix, $B$ a real $\iota \times E$ matrix and $f \in \mathbb{R}^\iota$. Let $\hat\ell \in \mathbb{R}^E$ solve the normal equations $B^\top Q^{-1} B \hat\ell = B^\top Q^{-1} f$. Then for every $\ell \in \mathbb{R}^E$,

$$S_1(B\ell) \le S_1(B\hat\ell),$$

where $S_1$ is the [score](score-s1.md) with covariance $Q$ and estimated statistics $f$.
