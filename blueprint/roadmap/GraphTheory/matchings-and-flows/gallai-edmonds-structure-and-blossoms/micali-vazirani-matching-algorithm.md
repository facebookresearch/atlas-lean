# Micali-Vazirani maximum matching in O(m sqrt n) time with Vazirani's correctness proof

There is a deterministic algorithm that, given a finite simple graph $G$ with $n$ vertices and $m \ge n/2$ edges in adjacency-list form, computes a maximum matching in $O(m \sqrt{n})$ time on a unit-cost RAM. Each phase computes the even and odd levels and tenacities of all vertices by a breadth-first search organized by increasing minlevel, processes bridges in order of increasing tenacity by double depth-first search from the two endpoints of each bridge, and outputs a maximal family of vertex-disjoint shortest augmenting paths in $O(m)$ time; by the phase bound there are $O(\sqrt{n})$ phases. The algorithm was published in 1980 without a correctness proof; Vazirani's 1994 proof attempt had gaps, and the complete proof (preprint 2020, journal version in Mathematics of Operations Research 2024) rests on graph-theoretic properties of minimum-length alternating paths and of blossoms defined through tenacity.

## Proof sketch

Inner vertices receive their maxlevel only through blossoms: when a bridge of tenacity $t$ is processed, double depth-first search either finds two vertex-disjoint alternating paths to distinct missed vertices, giving an augmenting path of length $t$, or identifies a new blossom (the vertices of tenacity $t$ reachable from the bridge) together with its base, and assigns $\mathrm{maxlevel}(v) = t - \mathrm{minlevel}(v)$ to its vertices. Vazirani's proof establishes that minimum-length alternating paths through nested blossoms behave like paths in a layered graph (the base structure and the tenacity invariants), so each edge is examined $O(1)$ times per phase and found paths can be erased without destroying the remaining shortest paths. Combined with the phase bound, the total time is $O(m \sqrt{n})$.

## Depends on

- [Even and odd levels, tenacity and bridges for minimum-length alternating paths](levels-tenacity-and-bridges.md)
- [Augmenting path](../berge-s-lemma/is-augmenting-walk.md)

## Proof depends on

- [Phase bound for shortest-augmenting-path matching algorithms in general graphs](phase-bound-shortest-augmenting-paths.md)

## Sources

- S. Micali, V. V. Vazirani, "An O(sqrt(|V|) |E|) algorithm for finding maximum matching in general graphs", FOCS (1980).
- V. V. Vazirani, "A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length", Mathematics of Operations Research 49 (2024) 2009-2047, doi:10.1287/moor.2020.0388.
- V. V. Vazirani, "A Proof of the MV Matching Algorithm", arXiv preprint (2020), arXiv:2012.03582.
- V. V. Vazirani, "A Simplification of the MV Matching Algorithm and its Proof", arXiv preprint (2012, revised 2013), arXiv:1210.4594.
