# Up-down and down-up random walks on a weighted complex

Let $X$ be a pure weighted complex of dimension $d$ and $0 \le k < d$. For functions on faces define the **up operator** $U_k : \mathbb{R}^{X(k)} \to \mathbb{R}^{X(k+1)}$ and the **down operator** $D_{k+1} : \mathbb{R}^{X(k+1)} \to \mathbb{R}^{X(k)}$ by

$$
(U_k f)(\sigma) = \frac{1}{k+2} \sum_{\tau \subset \sigma,\ |\tau| = k+1} f(\tau), \qquad (D_{k+1} g)(\tau) = \mathbb{E}_{\sigma \sim \Pi_{k+1},\ \sigma \supset \tau}\, g(\sigma).
$$

The **down-up walk** on $X(k)$ is $N_k^{\vee} = U_{k-1} D_k$ (drop a uniformly random vertex, then add one according to $\Pi_k$), and the **up-down walk** is $N_k^{\wedge} = D_{k+1} U_k$ (add a vertex according to $\Pi_{k+1}$, then drop a uniformly random vertex). Both are self-adjoint with respect to $\Pi_k$ and have the constant function as top eigenvector with eigenvalue $1$.

## Depends on

- [Pure weighted simplicial complexes and their face distributions](pure-weighted-complex.md)

## Sources

- T. Kaufman, D. Mass, "High dimensional random walks and colorful expansion", ITCS (2017), arXiv:1604.02947.
- T. Kaufman, I. Oppenheim, "High order random walks: beyond spectral gap", APPROX-RANDOM (2018); Combinatorica 40 (2020), arXiv:1707.02799.
- V. L. Alev, L. C. Lau, "Improved analysis of higher order random walks and applications", STOC (2020), arXiv:2001.02827.
