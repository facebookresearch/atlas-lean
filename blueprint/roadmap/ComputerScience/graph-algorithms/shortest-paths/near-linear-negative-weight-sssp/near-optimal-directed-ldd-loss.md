# Directed low-diameter decompositions with loss O(log n log log n)

Let $G$ be a directed graph with $n$ vertices, $m$ edges and positive integer edge lengths (polynomially bounded for the algorithms), and let $D\ge 1$. Integrality is part of the hypothesis: the source reduces to unit lengths by subdividing each edge $e$ into $\ell(e)$ unit edges, and without it the small uniform support of item 2 fails (on a directed $n$-cycle with every edge of length $2/n$ and $D=1$, every valid cut set contains an edge, so in a uniform list of $O(\log n)$ cut sets some edge is cut with probability $\Omega(1/\log n)$, far above $O(\log n\log\log n)\,w(e)/D$). A directed LDD of $G$ with loss $L$ is a probability distribution over edge sets $S$ such that every strongly connected component of $G\setminus S$ has weak diameter at most $D$ and $\Pr[e\in S]\le L\,w(e)/D$ for every edge $e$. Then:

1. there exists a directed LDD with loss $O(\log n\log\log n)$, which is within an $O(\log\log n)$ factor of the known lower bound $\Omega(\log n)$ on the loss;
2. a deterministic algorithm computes in time $\tilde O(m\,\mathrm{poly}(D))$ the support of such an LDD: an explicit list of $O(D\log n)$ edge sets, each with the weak-diameter property, whose uniform distribution has loss $O(\log n\log\log n)$; and a randomized algorithm samples one edge set from an LDD with loss $O(\log n\log\log n)$ in expected time $\tilde O(m)$, its analysis adding $1/\mathrm{poly}(n)$ to each cutting probability for rare invalid answers of a subroutine;
3. an LDD with loss $O(\log n\log\log n)$ can be sampled in expected time $O((m+n\log\log n)\log n\log\log n)$, succeeding with high probability.

## Proof sketch

The construction exploits a connection between directed LDDs and directed expander decompositions: inside a cluster that admits no sparse balanced directed cut, sets with small out- or in-balls can be peeled off at low cost, while clusters that are well connected in both directions have small weak diameter. Replacing expanders by lopsided expanders, whose diameter is $O(\psi^{-1}\log\log \mathrm{vol}(V)+\log\mathrm{vol}(V))$, and charging cut edges by multiplicative weight updates gives the loss bound. The algorithm in item 3 follows the ball-carving template: carve an out- or in-ball, cut its boundary edges, and recurse on the ball and on the rest, with radii chosen so that the per-level and recursion-depth losses merge into one $O(\log n\log\log n)$ factor.

## Depends on

- [Weak and strong directed low-diameter decompositions with overhead rho](directed-low-diameter-decomposition.md)

## Sources

- Karl Bringmann, Nick Fischer, Bernhard Haeupler, Rustam Latypov, "Near-Optimal Directed Low-Diameter Decompositions", ICALP (2025), arXiv:2502.05687, Definition 1.1, Section 2 and Theorems 2.1, 2.7 and 2.8.
- Jason Li, Connor Mowry, Satish Rao, "Faster Negative-Weight Shortest Paths and Directed Low-Diameter Decompositions", SODA (2026), arXiv:2510.22721.
