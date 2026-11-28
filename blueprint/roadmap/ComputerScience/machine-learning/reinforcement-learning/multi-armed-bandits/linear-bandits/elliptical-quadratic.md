# Quadratic form of an action in the inverse Gram matrix

For a matrix
$V_0 \in \mathbb{R}^{d \times d}$ and vectors $a_0, a_1, \ldots \in \mathbb{R}^d$, numbered from
$0$, let $V_k = V_0 + \sum_{j < k} a_j a_j^{\mathsf T}$ be the Gram matrix of the actions before
$a_k$. The quadratic form of round $k$ is

$$a_k^{\mathsf T} V_k^{-1} a_k,$$

where $V_k^{-1}$ is the inverse of $V_k$, taken to be $0$ when $V_k$ is singular. When $V_k$ is
positive definite, it is the squared norm $\lVert a_k \rVert_{V_k^{-1}}^2$.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Lemma 19.4, the quadratic forms $\lVert a_t \rVert_{V_{t-1}^{-1}}^2$, with $t = k + 1$. <https://tor-lattimore.com/downloads/book/book.pdf>
