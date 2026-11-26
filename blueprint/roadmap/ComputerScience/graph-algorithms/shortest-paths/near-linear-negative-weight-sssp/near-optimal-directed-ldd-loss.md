# Directed low-diameter decompositions with loss O(log n log log n)

For directed graphs with $n$ vertices, $m$ edges and nonnegative weights, and every $D>0$:

1. there exists a weak directed LDD that deletes each edge $e$ with probability $O\big(\frac{w(e)}{D}\log n\log\log n\big)$, which is within an $O(\log\log n)$ factor of the known lower bound $\Omega(\log n)$ on the overhead;
2. such an LDD can be computed deterministically in time $\tilde O(m\,\mathrm{poly}(D))$ and by a randomized algorithm in near-linear time $\tilde O(m)$;
3. an LDD with loss $O(\log n\log\log n)$ can be computed in expected time $O((m+n\log\log n)\log n\log\log n)$.

## Proof sketch

The construction exploits a connection between directed LDDs and directed expander decompositions: inside a cluster that admits no sparse balanced directed cut, sets with small out- or in-balls can be peeled off at low cost, while clusters that are well connected in both directions have small weak diameter. Charging cut edges against the volume of the smaller side across $O(\log n)$ scales, with a $\log\log n$ refinement of the radius distribution, gives the loss bound. The faster algorithm in item 3 replaces the expensive ball-size estimates by a cheaper sampling-based classification and shares work across scales.

## Depends on

- [Weak and strong directed low-diameter decompositions with overhead rho](directed-low-diameter-decomposition.md)
- [A weak directed low-diameter decomposition with overhead O(log^2 n) in near-linear time](bnw-weak-directed-ldd.md)

## Proof depends on

- [Weak and strong directed low-diameter decompositions with overhead rho](directed-low-diameter-decomposition.md)
- [A weak directed low-diameter decomposition with overhead O(log^2 n) in near-linear time](bnw-weak-directed-ldd.md)

## Sources

- Karl Bringmann, Nick Fischer, Bernhard Haeupler, Rustam Latypov, "Near-Optimal Directed Low-Diameter Decompositions", ICALP (2025), arXiv:2502.05687.
- Jason Li, Connor Mowry, Satish Rao, "Faster Negative-Weight Shortest Paths and Directed Low-Diameter Decompositions", SODA (2026), arXiv:2510.22721.
