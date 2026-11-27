# Major and minor subtree-size sums as the building blocks of the Sackin and Colless indices

**Setting.** Let $\mathcal{BT}^*_n$ be the set of rooted binary tree shapes with $n$ leaves and $\mathring V(T)$ the inner vertices of $T$. For $v \in \mathring V(T)$ let $n_{v_a} \ge n_{v_b}$ be the leaf numbers of the two maximal pending subtrees below $v$. Define

$$N_a(T) = \sum_{v \in \mathring V(T)} n_{v_a}, \qquad N_b(T) = \sum_{v \in \mathring V(T)} n_{v_b}.$$

Then the Sackin and Colless indices decompose as

$$S(T) = \sum_{v} n_v = N_a(T) + N_b(T), \qquad C(T) = \sum_v (n_{v_a} - n_{v_b}) = N_a(T) - N_b(T),$$

and $\Delta_{CS} = C - S = -2N_b$, $\Delta_{SC} = S - C = 2N_b$. An *imbalance index* is a shape statistic uniquely maximized by the caterpillar $T^{cat}_n$ and, when $n = 2^k$, uniquely minimized by the fully balanced tree $T^{fb}_k$; a *balance index* has the reverse extremal behavior.

**Theorem.**
1. $N_a$ and $\Delta_{CS}$ are imbalance indices; $N_b$ and $\Delta_{SC}$ are balance indices on $\mathcal{BT}^*_n$.
2. $N_b(T) \ge n - 1$ with equality exactly for the caterpillar; $N_a(T^{cat}_n) = n(n-1)/2$ is the unique maximum of $N_a$; for $n = 2^k$, $N_a(T^{fb}_k) = N_b(T^{fb}_k) = 2^{k-1}k$.
3. With $\breve s(x) = \min_{z\in\mathbb{Z}}|x - z|$ and $k_n = \lceil \log_2 n\rceil$,

$$\Delta_{CS}(T) \;\ge\; \sum_{j=1}^{k_n - 1} 2^j\,\breve s(2^{-j} n) + 2^{k_n} - n(k_n + 1),$$

tight and attained by every Colless-minimal tree; the minimal values $d_n$ satisfy $d_0 = d_1 = 0$, $d_{2n} = 2d_n - 2n$ and $d_{2n+1} = d_{n+1} + d_n - 2n$.
4. Call $(n_a, n_b)$ with $n_a \ge n_b$, $n_a + n_b = n$ a *Colless partition* of $n$ if joining a Colless-minimal tree on $n_a$ leaves and one on $n_b$ leaves at a new root gives a Colless-minimal tree on $n$ leaves, and call $(2^{k_n-1},\, n - 2^{k_n-1})$, $k_n = \lceil\log_2 n\rceil$, the *echelon partition* of $n$. The *echelon tree* $T^{be}_n$ is defined recursively: $T^{be}_1$ is a single vertex, and for $n > 1$ its two maximal pending subtrees are the fully balanced tree $T^{fb}_{k_n-1}$ on $2^{k_n-1}$ leaves and $T^{be}_{n-2^{k_n-1}}$, so its root split is the echelon partition. Then $T$ minimizes $\Delta_{CS}$ (equivalently maximizes $N_b$) iff at every inner vertex $v$ the pair $(n_{v_a}, n_{v_b})$ is a Colless partition or the echelon partition of $n_v$; in particular the echelon tree is always such a minimizer.
5. $T$ minimizes $N_a$ iff $T$ minimizes the Colless index.
6. $N_a$, $N_b$, $\Delta_{CS}$, $\Delta_{SC}$ are local, binary recursive tree shape statistics computable in $O(n)$ time.

## Expansion

At the root, $\Delta_{CS}(T) = \Delta_{CS}(T_a) + \Delta_{CS}(T_b) - 2n_b$, so optimal trees have optimal root subtrees, and the minimum obeys a recursion over root splits; checking that the balanced split $(\lceil n/2\rceil, \lfloor n/2\rfloor)$ is optimal yields the recursion for $d_n$ and the closed form, which equals $C - S$ of the maximally balanced tree. Since $N_a = (S + C)/2$ and $N_b = (S - C)/2$, both classical indices are sums of a balance-rewarding and an imbalance-rewarding part; the minimal Colless trees are exactly the $N_a$ minimizers, while $N_b$ maximizers form a strictly larger family including the echelon tree.

## Sources

- L. Knüver and M. Fischer, "Revealing the building blocks of tree balance: fundamental units of the Sackin and Colless Indices", *Annals of Combinatorics* (2026), Theorems 1–4, Propositions 1–3, 5, 6, 9 and Corollary 2, <https://doi.org/10.1007/s00026-026-00860-8> (preprint arXiv:2509.04995).
