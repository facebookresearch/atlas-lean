# First two moments of the Yule tree height and of a random pair's coalescence time

**Setting.** Grow a pure-birth (Yule) tree with speciation rate $1$ from a single lineage and stop it just before the $(n+1)$-st speciation, so that it has $n$ tips. Its height is $U^{(n)} = T_1 + \cdots + T_n$ with independent $T_i \sim \operatorname{Exp}(i)$ (the waiting time while $i$ lineages are present). Let $\tau^{(n)}$ be the time back from the present to the most recent common ancestor of two tips sampled uniformly without replacement, $\mathcal{Y}_n$ the tree, and $H_{n,i} = \sum_{k=1}^n k^{-i}$.

**Theorem (first two moments).**
$$\mathbb{E}U^{(n)} = H_{n,1}, \qquad \mathbb{E}\big[(U^{(n)})^2\big] = H_{n,1}^2 + H_{n,2},$$
$$\mathbb{E}\tau^{(n)} = \frac{n+1}{n-1}H_{n,1} - \frac{2n}{n-1}, \qquad \mathbb{E}\big[(\tau^{(n)})^2\big] = \frac{n+1}{n-1}\Big((H_{n,1} - 2)^2 + H_{n,2}\Big) - \frac{4}{n-1},$$
and for the shared path length $U^{(n)} - \tau^{(n)}$ of the pair,
$$\mathbb{E}\big[U^{(n)} - \tau^{(n)}\big] = \frac{2(n - H_{n,1})}{n-1}, \qquad \mathbb{E}\big[(U^{(n)} - \tau^{(n)})^2\big] = \frac{4n+2}{n-1}H_{n,2} - \frac{2H_{n,1}^2}{n-1} - \frac{4H_{n,1}}{n-1},$$
$$\mathbb{E}\big[U^{(n)}(U^{(n)} - \tau^{(n)})\big] = \mathbb{E}\big[U^{(n)}\big(U^{(n)} - \mathbb{E}[\tau^{(n)}\mid\mathcal{Y}_n]\big)\big] = \frac{2n}{n-1}\Big(H_{n,1} + H_{n,2} - 1 - \frac{H_{n,1}^2}{n}\Big).$$
Hence the shared path length has mean $\to 2$ and variance $\to 4(\pi^2/6 - 1)$, while $U^{(n)}$ has mean $\sim \log n$, variance $\to \pi^2/6$, and $U^{(n)} - \log n$ converges to a Gumbel law.

**Theorem (tree-conditional coalescence time).** As $n \to \infty$,
$$\mathbb{E}\Big[\big(U^{(n)} - \mathbb{E}[\tau^{(n)}\mid\mathcal{Y}_n]\big)^2\Big] = \tfrac43 H_{n,2} + 3 - \tfrac{8}{n}H_{n,1} + \Theta(n^{-1}) \to \frac{2\pi^2}{9} + 3,$$
$$\mathbb{E}\Big[\big(\tau^{(n)} - \mathbb{E}[\tau^{(n)}\mid\mathcal{Y}_n]\big)^2\Big] = \tfrac83 H_{n,2} - 3 - \frac{2H_{n,1}^2}{n-1} + \Theta(n^{-1}\ln n) \to \frac{4\pi^2}{9} - 3 .$$
Since the total cophenetic index of the tree with branch lengths equals $\binom n2\big(U^{(n)} - \mathbb{E}[\tau^{(n)}\mid\mathcal{Y}_n]\big)$, these give its first two moments.

## Depends on

## Expansion

The height is a sum of independent exponentials, giving the $U^{(n)}$ moments. The pair of sampled tips coalesces at the speciation event that occurs when $k$ lineages become $k+1$ with probability $\pi_{n,k} = \frac{2(n+1)}{(n-1)(k+1)(k+2)}$, so $U^{(n)} - \tau^{(n)} = T_1 + \cdots + T_K$ for an independent random index $K$; summing moments of partial sums against $\pi_{n,k}$ gives the formulas. Higher moments follow a partition expansion $\sum_{\mathbf{k}} c_{\mathbf{k}}\prod_i H_{n,i}^{k_i}$ over the integer partitions of $m$. The tree-conditional quantities require the joint law of coalescence nodes for two independent pairs on the same tree.

## Sources

- K. Bartoszek, B. Brahmantio and W. H. C. Kiang, "First two moments and cross-moments of some coalescent times of the pure birth tree", arXiv:2502.18159 (2025), Section 3 and Theorems 4.1, 4.2, <https://doi.org/10.48550/arXiv.2502.18159>.
