# Asymmetric palette sparsification: greedy coloring from random lists of average size O(log^2 n)

Let $(G, S)$ be a D1LC instance on $n$ vertices in which every list $S(v)$ has exactly $\deg(v) + 1$ colors, let $\pi : V \to \{1, \dots, n\}$ be a uniformly random bijection, and set $\ell(v) = \min\big(\deg(v) + 1, \lceil 40\, n \ln n / \pi(v) \rceil\big)$ (the distribution of $\ell$ depends only on $V$ and the degrees). If every vertex $v$ independently samples a uniformly random subset $L(v) \subseteq S(v)$ of size $\ell(v)$, then with high probability over $\pi$ and the samples, the greedy algorithm that processes the vertices in decreasing order of $\pi(v)$ and gives each vertex any color of $L(v)$ not used by its already colored neighbors finds a proper list coloring of $G$ from the lists $L(v)$.

For $(\Delta + 1)$-coloring the same holds with $\ell(v) = \min\big(\Delta + 1, \lceil 40\, n \ln n/\pi(v)\rceil\big)$ and lists $L(v)$ sampled from $\{1, \dots, \Delta + 1\}$, by first sampling $\deg(v) + 1$ colors of $\{1, \dots, \Delta + 1\}$ as $S(v)$ and sampling inside it. Since $\sum_v \ell(v) = O(n\log^2 n)$ deterministically, this yields semi-streaming, sublinear-time and massively parallel $(\Delta + 1)$-coloring algorithms of the same quality as the symmetric theorem up to polylogarithmic factors, with greedy post-processing.

## Proof sketch

When $v$ is processed, only its already processed neighbors, those with larger $\pi$, can block colors, so at least $\deg^{<}_\pi(v) + 1$ colors of $S(v)$ are still available. If $\ell(v) = \deg(v) + 1$ then $L(v) = S(v)$ and greedy succeeds at $v$. Otherwise $\pi(v) > 40 n\ln n/(\deg(v) + 1)$, the back-degree lemma gives at least $\deg(v)\pi(v)/(2n)$ available colors out of $\deg(v) + 1$, and since $L(v)$ is independent of the colors chosen earlier, all $\ell(v)$ samples miss the available set with probability at most $(1 - \pi(v)/(4n))^{40 n \ln n/\pi(v)} \le n^{-10}$. A union bound over the vertices finishes.

## Depends on

- [The (deg + 1)-list-coloring problem (D1LC)](degree-plus-one-list-coloring.md)

## Proof depends on

- [List sizes inversely proportional to a random rank have average O(log^2 n)](asymmetric-list-sizes-from-random-ranks.md)
- [Concentration of the number of later-processed neighbors under a random order](random-order-back-degree-concentration.md)
- [$k$-degenerate graphs are $(k + 1)$-colorable](../../../../GraphTheory/graph-coloring/part-01/degeneracy-and-greedy-coloring/colorable.md)

## Sources

- Sepehr Assadi, Helia Yazdanyar, "Simple Sublinear Algorithms for (Delta+1) Vertex Coloring via Asymmetric Palette Sparsification", SOSA (2025); TheoretiCS 5 (2026), Article 3, arXiv:2502.17629.
