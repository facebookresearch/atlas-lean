# Bourgain's O(log n) embedding of finite metrics into l_1 and l_2, tight for expanders

1. (Bourgain.) Every $n$-point metric space $(X, d)$ embeds into $\ell_2$, and hence into $\ell_1$, with distortion $O(\log n)$. A random Fréchet embedding achieves this in dimension $O(\log^2 n)$ with high probability, computable in randomized polynomial time.
2. (Linial–London–Rabinovich.) For every fixed $k \ge 3$ and every family of $k$-regular expander graphs with edge expansion bounded below by a constant, the shortest-path metrics of the $n$-vertex members satisfy $c_{\ell_1} = \Omega(\log n)$ and hence $c_{\ell_2} = \Omega(\log n)$.

So $\max_{|X| = n} c_{\ell_1}(X) = \Theta(\log n)$ and $\max_{|X| = n} c_{\ell_2}(X) = \Theta(\log n)$.

## Proof sketch

For part 1, for $j = 1, \dots, \lceil\log_2 n\rceil$ and $O(\log n)$ repetitions, pick random sets $A$ containing each point independently with probability $2^{-j}$ and use coordinates $x \mapsto d(x, A)$, each $1$-Lipschitz. For a pair $x, y$ and radii $r_t$ at which balls around $x$ or $y$ contain $2^t$ points, the set $A$ of the matching scale hits one ball and misses the other with constant probability, so the coordinate gap is at least $r_{t+1} - r_t$; summing over scales telescopes to $\Omega(d(x, y))$ on average, while the upper bound loses only the number $O(\log n)$ of scales. For part 2, let $f$ be a non-contracting embedding into $\ell_1$ with distortion $D$ and write its metric as $\sum_S \lambda_S \delta_S$, a nonnegative combination of cut metrics. Edge expansion $h$ gives $|E(S, V \setminus S)| \ge (h/n)|S||V \setminus S|$ for every cut, so the sum of the image lengths of the edges is at least $h/n$ times the sum over all pairs, which is at least $h/n$ times $\sum_{x, y} d(x, y) = \Omega(n^2\log n)$, because in a graph of bounded degree most pairs are at distance $\Omega(\log n)$. The edges have length $1$, so their image lengths sum to at most $Dkn/2$, and $D = \Omega(\log n)$.

## Depends on

- [Distortion of a metric embedding and the Euclidean dimension-reduction function](bi-lipschitz-distortion-of-metric-embeddings.md)

## Proof depends on

- [Hoeffding's inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- Jean Bourgain, "On Lipschitz embedding of finite metric spaces in Hilbert space", Israel J. Math. 52 (1985).
- Nathan Linial, Eran London, Yuri Rabinovich, "The geometry of graphs and some of its algorithmic applications", Combinatorica 15 (1995).
