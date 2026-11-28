# Maximum and average quartet distance separate under partial information

Let $M_{T(S)}$ be the maximum quartet distance between two completions of a partially labelled phylogenetic tree $T(S)$ and $X_{T(S)}$ the quartet distance between two independent uniform completions, as in [the expected quartet distance of random completions](expected-quartet-distance-of-random-completions-of-a-partially-labelled-tree.md).

**Background (Bandelt–Dress conjecture).** With no pinned taxa, the maximum quartet distance between two labelled trees of order $n$ is conjectured to be $(\frac23 + o(1))\binom n4$, i.e. asymptotically equal to the average $\frac23\binom n4$; it is known that the maximum is below $\frac{14}{15}\binom n4$ for $n\ge6$, below $(0.69+o(1))\binom n4$ in general, and equals $(\frac23 + o(1))\binom n4$ when both trees are caterpillars.

**Theorem.** Let $0<\alpha<1$, let $T$ be a tree of order $n$ and $T(S)$ a partial labelling with $|S| = \alpha n$. Suppose there is an internal edge $e = uv$ whose removal leaves components $T_u$, $T_v$ with $\mathcal{L}(T_u) = S$, and such that $T_v$ (after suppressing the degree-2 vertex) is a caterpillar whose join edge is one of its four endpoint edges. Then

$$M_{T(S)} - \mathbb{E}[X_{T(S)}] = \Theta(n^4).$$

So the "maximum equals average" phenomenon conjectured in the no-information setting fails under partial information: such configurations exist for every $\alpha\in(0,1)$ (attach any labelled tree on $\alpha n$ leaves to an endpoint edge of an unlabelled caterpillar on $(1-\alpha)n$ leaves). This does not contradict the Bandelt–Dress conjecture itself, which concerns $\alpha = 0$.

## Depends on

- [Expected quartet distance of random completions of a partially labelled tree](expected-quartet-distance-of-random-completions-of-a-partially-labelled-tree.md)

## Proof sketch

In this configuration $S$ is one side of a split, so the expectation is the minimum possible, $\bigl(\frac23(1-\alpha)^4+\frac83\alpha(1-\alpha)^3\bigr)\binom n4(1+o(1))$. For the maximum, order the caterpillar leaves $\ell_1,\dots,\ell_{n-k}$ by distance from the split. One completion places the free taxa in this order, the other in the reversed order. Quartets with $0$, $2$, $3$ or $4$ pinned taxa are displayed identically by both, but every quartet $[ax|yz]$ with one pinned taxon $a$ flips, because which free taxon is closest to the split is reversed. Hence $M_{T(S)}\ge \alpha n\binom{(1-\alpha)n}{3} = 4\alpha(1-\alpha)^3\binom n4(1+o(1))$, which exceeds the expectation by order $n^4$ when $\alpha>1/3$. For $\alpha\le1/3$ a mixed completion works: the free taxa on the two end blocks of the caterpillar are swapped and reversed, while those in the middle block are permuted at random, and the block size is tuned to beat the random baseline.

## Sources

- Sagi Snir, Osnat Weissberg and Raphael Yuster, "On the quartet distance given partial information", *Journal of Graph Theory* 100 (2022), 252–269, <https://doi.org/10.1002/jgt.22776>. Preprint version: arXiv:2111.13101 (2021), Conjecture 1.1 (Bandelt–Dress) and Theorem 2.4; proof in Section 5, <https://doi.org/10.48550/arXiv.2111.13101>.
