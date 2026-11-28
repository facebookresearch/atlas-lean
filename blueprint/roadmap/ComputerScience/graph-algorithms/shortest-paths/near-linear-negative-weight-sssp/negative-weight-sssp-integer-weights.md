# Negative-weight single-source shortest paths with integer weights bounded below by -W

Let $G=(V,E,w)$ be a directed graph with $n=|V|$ vertices, $m=|E|\ge n$ edges and integer weights $w:E\to\mathbb{Z}$, and let $W\ge 2$ be an integer with $w(e)\ge -W$ for every $e\in E$. For $u,v\in V$ let $\mathrm{dist}_G(u,v)$ be the infimum of $w(P)$ over all directed $u$-$v$ walks $P$, with $\mathrm{dist}_G(u,v)=+\infty$ if $v$ is not reachable from $u$ and $\mathrm{dist}_G(u,v)=-\infty$ if some $u$-$v$ walk meets a cycle of negative total weight.

The *negative-weight single-source shortest paths problem* (negative-weight SSSP) asks: given $G$ and a source $s\in V$, output either

1. a shortest-path tree $T$ rooted at $s$ that spans all vertices reachable from $s$, so that the tree path to each such $v$ has weight $\mathrm{dist}_G(s,v)$, or
2. a directed cycle $C$ of $G$ with $w(C)<0$.

Algorithms are analysed on the word RAM with words of $\Theta(\log(nM))$ bits, where $M\ge 2$ bounds $|w(e)|$ for every $e\in E$ (the lower bound $W$ does not bound positive weights), so that every input weight and every sum of at most $n$ weights fits in $O(1)$ words. Both outputs are certificates checkable in $O(m)$ time. The classical baselines are the Bellman-Ford algorithm, running in $O(mn)$ time, and the scaling algorithms of Gabow, of Gabow and Tarjan, and of Goldberg, which led to running time $O(m\sqrt{n}\log W)$ for weights with $w(e) \ge -W$, $W \ge 2$ (Bernstein, Nanongkai and Wulff-Nilsen, Section 1, who cite the Gabow-Tarjan bound as $\tilde{O}(m\sqrt{n}\log W)$).

## Depends on

- [Bellman–Ford algorithm](../bellman-ford-algorithm/bellman-ford.md)
- [Existence of a reachable negative cycle](../bellman-ford-algorithm/has-reachable-negative-cycle.md)
- [Negative cycles](../floyd-warshall-algorithm/is-negative-cycle.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- Aaron Bernstein, Danupon Nanongkai, Christian Wulff-Nilsen, "Negative-Weight Single-Source Shortest Paths in Near-linear Time", FOCS (2022), arXiv:2203.03456, abstract and Section 1 (Bellman-Ford and the scaling algorithms of Gabow, Gabow-Tarjan and Goldberg).
- Richard Bellman, "On a Routing Problem", Quarterly of Applied Mathematics 16(1) (1958).
- Harold N. Gabow, "Scaling Algorithms for Network Problems", Journal of Computer and System Sciences 31(2) (1985).
- Harold N. Gabow, Robert E. Tarjan, "Faster Scaling Algorithms for Network Problems", SIAM Journal on Computing 18(5) (1989).
- Andrew V. Goldberg, "Scaling Algorithms for the Shortest Paths Problem", SIAM Journal on Computing 24(3) (1995).
