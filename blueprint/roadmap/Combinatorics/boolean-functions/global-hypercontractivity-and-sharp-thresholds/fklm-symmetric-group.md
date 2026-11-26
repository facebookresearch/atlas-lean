# Hypercontractivity for global functions on the symmetric group

Let $S_n$ carry the uniform measure, and call $f : S_n \to \mathbb{R}$ **$(d, \varepsilon)$-global** if for every set of $d$ pairs $(i_1, j_1), \dots, (i_d, j_d)$ the restriction of $f$ to $\{\pi : \pi(i_t) = j_t\ \forall t\}$ has $L^2$-norm at most $\varepsilon$. Then there are absolute constants $C, c > 0$ such that for every $d \le c\, n$ and every $(d, \varepsilon)$-global $f$ of degree at most $d$,

$$
\|f\|_4^4 \le C^{d}\, \varepsilon^2\, \|f\|_2^2.
$$

Consequently, global subsets of $S_n$ of density $\alpha$ have level-$d$ Fourier weight $O_d(\alpha^2 \log^d(1/\alpha))$, giving strong bounds for $t$-intersecting families of permutations and for product-free sets.

## Proof sketch

Couple the uniform permutation with a product space of independent random variables through a sequence of random transpositions and prove the estimate first for functions of low degree in the coupled product space; globalness of $f$ transfers to bounds on the generalized influences in the product space, where the KLLM-type hypercontractive inequality applies.

## Depends on

- [Keevash–Lifshitz–Long–Minzer: hypercontractivity for global functions](kllm-global-hypercontractivity.md)

## Proof depends on

- [Keevash–Lifshitz–Long–Minzer: hypercontractivity for global functions](kllm-global-hypercontractivity.md)

## Sources

- Y. Filmus, G. Kindler, N. Lifshitz, D. Minzer, "Hypercontractivity on the symmetric group", Forum of Mathematics, Pi 12 (2024), arXiv:2009.05503.
