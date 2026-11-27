# Combs maximize Colless-like indices

**Setting.** Let $K_n$ be the rooted comb (caterpillar) with $n$ leaves, and use the [Colless-like indices](soundness-of-colless-like-indices.md) $C_{D,f}$ on the set $\mathcal T^*_n$ of rooted trees without out-degree-1 nodes with $n$ leaves.

**Lemma (classical Colless index).** For every bifurcating tree $T$ with $n$ leaves, $T \ne K_n$ implies $C(T) < C(K_n) = \binom{n-1}{2}$.

**Theorem.** Let $f : \mathbb N \to \mathbb R_{\ge 0}$ satisfy $0 < f(k) < f(k-1) + f(2)$ for every $k \ge 3$. Then for every $n \ge 2$ the indices $C_{\mathrm{MDM},f}$, $C_{\mathrm{sd},f}$ and $C_{\mathrm{var},f}$ reach their maximum on $\mathcal T^*_n$ exactly at the comb $K_n$, with

$$C_{\mathrm{MDM},f}(K_n) = \frac{f(0)+f(2)}{4}(n-1)(n-2), \qquad C_{\mathrm{sd},f}(K_n) = \frac{f(0)+f(2)}{2\sqrt2}(n-1)(n-2),$$

$$C_{\mathrm{var},f}(K_n) = \frac{(f(0)+f(2))^2}{12}(n-1)(n-2)(2n-3).$$

The function $f(n) = \ln(n+e)$ satisfies the hypothesis, so the sound indices $C_{D,\ln(n+e)}$ have the comb as unique most unbalanced tree and can be normalized by these maxima. For the fast-growing $f(n) = e^n$ the hypothesis fails and the maximizer is instead (for $n \ne 4$, with MDM or sd) the tree whose root has one leaf child and one star child with $n-1$ leaves.

## Depends on

- [Soundness of Colless-like indices](soundness-of-colless-like-indices.md)

## Expansion

Lemma: take an internal node $x$ of smallest depth with no leaf child, with subtrees $T_1 \star T_2$ and $T_3 \star T_4$ below it ($t_1 \le t_2$, $t_1 + t_2 \le t_3 + t_4$ leaves); pruning $T_2$ and regrafting it on the other arc from $x$ strictly increases $C$. Iterating reaches the comb. The theorem's condition says that merging a node of degree $k$ into a binary node and a node of degree $k-1$ increases the $f$-size, so resolving multifurcations into a comb can only increase the dissimilarities; the long case analysis is done separately for each $D$.

## Sources

- A. Mir, L. Rotger and F. Rosselló, "Sound Colless-like balance indices for multifurcating trees", *PLoS ONE* 13(9) (2018) e0203401, Lemma 1 (with Fig 6), Theorem 18 (proofs in S1 File) and Theorem 19. <https://doi.org/10.1371/journal.pone.0203401> (PMC6155497)
