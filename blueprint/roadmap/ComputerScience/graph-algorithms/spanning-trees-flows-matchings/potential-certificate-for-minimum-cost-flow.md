# Reduced-cost optimality certificate for minimum-cost flow

Let $f$ be a feasible flow with $l \le f \le u$ and prescribed supplies in a finite directed network with real arc costs $c$, and let its residual network have forward arcs with capacity $u - f$ and cost $c$, and reverse arcs with capacity $f - l$ and cost $-c$, keeping only arcs of positive capacity. If vertex potentials $\pi$ make every residual reduced cost $c_{vw} + \pi_v - \pi_w$ nonnegative, then $f$ is a minimum-cost flow. Conversely, if the residual network has no directed cycle of negative cost, such potentials exist: take $\pi_v$ to be the least cost of a walk to $v$ from an added source joined to every vertex by an arc of cost $0$.

Proof. For any feasible $g$, the potential terms cancel by flow conservation with equal supplies, so $c^{\mathsf T}g - c^{\mathsf T}f = \sum_{vw}(c_{vw} + \pi_v - \pi_w)(g_{vw} - f_{vw})$. A positive term $g_{vw} - f_{vw}$ needs $f_{vw} < u_{vw}$, a forward residual arc with nonnegative reduced cost; a negative one needs $f_{vw} > l_{vw}$, a reverse residual arc, whose nonnegative reduced cost is $-(c_{vw} + \pi_v - \pi_w)$; so every term is nonnegative. For the converse, without negative cycles every walk from the added source can be shortened to a path of no larger cost, so least walk costs exist (finitely many paths), and extending a cheapest walk to $v$ by a residual arc $vw$ gives $\pi_w \le \pi_v + c_{vw}$. The equivalence of optimality with the absence of negative residual cycles is a separate statement.

## Background

- [Bellman-Ford succeeds exactly when no negative cycle is reachable](../shortest-paths/bellman-ford-algorithm/bellman-ford-returns-distances-iff.md): computing such distances for integer costs.

## Sources

- A. Schrijver, *A Course in Combinatorial Optimization*, lecture notes, CWI and University of Amsterdam, 2017, <https://homepages.cwi.nl/~lex/files/dict.pdf>, §4.6, Proposition 4 (no negative circuit in the auxiliary graph), and §1.3, Theorems 1.9–1.10
