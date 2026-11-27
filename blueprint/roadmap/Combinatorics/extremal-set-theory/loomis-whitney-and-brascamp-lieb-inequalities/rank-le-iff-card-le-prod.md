# Discrete Hölder–Brascamp–Lieb inequality

Let $\varphi_j : \mathbb{Z}^d \to \mathbb{Z}^{d_j}$ ($j = 1, \dots, m$) be group homomorphisms and $s \in [0, 1]^m$. Then

$$\operatorname{rank} H \le \sum_{j=1}^m s_j \operatorname{rank} \varphi_j(H) \quad \text{for all subgroups } H \le \mathbb{Z}^d$$

if and only if

$$|E| \le \prod_{j=1}^m |\varphi_j(E)|^{s_j} \quad \text{for all nonempty finite sets } E \subseteq \mathbb{Z}^d$$

(M. Christ, J. Demmel, N. Knight, T. Scanlon and K. Yelick, *Communication lower bounds and optimal algorithms for programs that reference arrays, Part 1*, arXiv:1308.0068, 2013, Theorem 3.2). The rank of a subgroup of $\mathbb{Z}^k$ is its rank as a free $\mathbb{Z}$-module. Although the first condition ranges over infinitely many subgroups, each rank lies in $\{0, \dots, d\}$, so it amounts to finitely many linear constraints on $s$.

For the three coordinate projections $\mathbb{Z}^3 \to \mathbb{Z}^2$ and $s = (1/2, 1/2, 1/2)$ the rank condition holds and the conclusion is the [discrete Loomis–Whitney inequality](card-le-sqrt-mul-mul.md). In Christ et al. the least $s_{\mathrm{HBL}} = \sum_j s_j$ satisfying the rank condition gives, for a loop nest whose array subscripts are the maps $\varphi_j$ of the loop indices, the communication lower bound $\Omega(|Z| / M^{s_{\mathrm{HBL}} - 1})$ words for $|Z|$ iterations and a fast memory of $M$ words (their Theorem 4.1); for classical matrix multiplication $s_{\mathrm{HBL}} = 3/2$ recovers $\Omega(n^3/\sqrt{M})$.



## Background

- [Discrete Loomis–Whitney inequality (three dimensions)](card-sq-le-card-mul-card-mul-card.md): the special case of the three coordinate projections.
