# Hypercontractivity for global functions on the symmetric group

Let $S_n$ carry the uniform measure. A set $T$ of pairs $(i, j) \in [n]^2$ is *consistent* if no two of its pairs share a first or a second coordinate, and $f_{\to T}$ denotes the restriction of $f : S_n \to \mathbb{R}$ to $\{\pi : \pi(i) = j \text{ for all } (i,j) \in T\}$ with its uniform measure. Call $f$ **$(d, \varepsilon)$-global** if $\|f_{\to T}\|_2 \le \varepsilon$ for every consistent $T$ with $|T| \le d$. There is an absolute constant $K > 0$ such that for every even $q \in \mathbb{N}$ and every $n > q^{K d^2}$, every $(2d, \varepsilon)$-global $f$ of degree at most $d$ satisfies

$$
\|f\|_q \le q^{O(d^3)}\, \varepsilon^{(q-2)/q}\, \|f\|_2^{2/q}.
$$

Moreover (level-$d$ inequality), there is an absolute constant $C > 0$ such that for every $(2d, \varepsilon)$-global $f : S_n \to \mathbb{Z}$ with $n > 2^{C d^3} \log(1/\varepsilon)^{C d}$,

$$
\|f^{\le d}\|_2^2 \le 2^{C d^4}\, \varepsilon^4 \log^{C d}(1/\varepsilon),
$$

which bounds the density of global product-free subsets of the alternating group $A_n$.

## Proof sketch

Couple the uniform permutation with a product space of independent random variables through a sequence of random transpositions and prove the estimate first for functions of low degree in the coupled product space; globalness of $f$ transfers to bounds on the generalized influences in the product space, where the KLLM-type hypercontractive inequality applies.

## Proof depends on

- [Keevash–Lifshitz–Long–Minzer: hypercontractivity for global functions](kllm-global-hypercontractivity.md)

## Sources

- Y. Filmus, G. Kindler, N. Lifshitz, D. Minzer, "Hypercontractivity on the symmetric group", Forum of Mathematics, Pi 12 (2024), arXiv:2009.05503.
