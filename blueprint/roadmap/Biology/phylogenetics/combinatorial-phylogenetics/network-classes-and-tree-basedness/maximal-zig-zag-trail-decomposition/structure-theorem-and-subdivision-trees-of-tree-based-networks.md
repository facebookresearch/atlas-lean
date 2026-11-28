# Maximal zig-zag trail decomposition and the subdivision trees of a tree-based network

**Setting.** Let $N$ be a rooted binary phylogenetic network on $X$ with arc set $A(N)$. $N$ is **tree-based** if it has a **subdivision tree**: a spanning tree of $N$ that is a subdivision of a rooted binary phylogenetic $X$-tree (all vertices of $N$ covered, leaf set $X$). A **zig-zag trail** is a connected subgraph $Z$ with $|A(Z)| \ge 1$ whose arcs admit an ordering $(a_1,\dots,a_m)$ in which consecutive arcs share a head or share a tail; write it as $v_0 > v_1 < v_2 > \cdots$, where $u > v$ denotes an arc $(u,v)$. A maximal zig-zag trail is of exactly one of four types:

- **crown**: $m \ge 4$ even and closed, $v_0 < v_1 > v_2 < \cdots < v_{m-1} > v_m = v_0$;
- **N-fence**: $m$ odd, $v_0 > v_1 < \cdots < v_{m-1} > v_m$;
- **M-fence**: $m$ even, $v_0 < v_1 > \cdots < v_{m-1} > v_m$ (both endpoints are heads);
- **W-fence**: $m$ even, $v_0 > v_1 < \cdots > v_{m-1} < v_m$ (both endpoints are tails).

**Theorem (structure theorem).** Every rooted binary phylogenetic network $N$ has a unique decomposition $\mathcal{Z} = \{Z_1,\dots,Z_\ell\}$ of its arc set into maximal zig-zag trails, and it can be computed in $O(|A(N)|)$ time.

**Theorem (subdivision trees).** Encode a subset of $A(Z_i) = (a_1,\dots,a_{m_i})$, listed in trail order, as a $0$–$1$ word of length $m_i$, and let

$$\mathcal{S}(Z_i) = \begin{cases} \{\langle (10)^{m_i/2}\rangle, \langle (01)^{m_i/2}\rangle\} & Z_i \text{ a crown}, \\ \{\langle 1(01)^{(m_i-1)/2}\rangle\} & Z_i \text{ an N-fence}, \\ \{\langle 1(01)^p(10)^q1\rangle : p,q \in \mathbb{Z}_{\ge 0},\ p+q = (m_i-2)/2\} & Z_i \text{ an M-fence}. \end{cases}$$

1. $N$ is tree-based if and only if no $Z_i$ is a W-fence.
2. If $N$ is tree-based, the arc sets of its subdivision trees are exactly the products $\mathcal{T} = \prod_{i=1}^{\ell}\mathcal{S}(Z_i)$; hence the number of subdivision trees is

$$\alpha(N) = \prod_{i=1}^{\ell}\alpha(Z_i), \qquad \alpha(Z_i) = \begin{cases} 0 & \text{W-fence}, \\ 1 & \text{N-fence}, \\ 2 & \text{crown}, \\ |A(Z_i)|/2 & \text{M-fence}. \end{cases}$$

3. The minimum number $\delta(N)$ of leaves that must be attached to $N$ to make it tree-based equals the number of W-fences in $\mathcal{Z}$.

Consequently, recognizing tree-based networks, counting subdivision trees and computing $\delta(N)$ take linear time in $|A(N)|$, and the subdivision trees can be listed with $O(|A(N)|)$ delay (the number of subdivision trees can be exponential: $k$ crowns give $2^k$).

## Expansion

An arc set $S \subseteq A(N)$ induces a subdivision tree exactly when it is *admissible*: it contains every arc whose head has in-degree one or whose tail has out-degree one, each reticulation keeps exactly one incoming arc, and each tree vertex keeps at least one outgoing arc. These constraints only couple arcs that share a head or a tail, i.e. arcs in the same zig-zag trail, so admissibility splits into independent conditions on each maximal trail and the solution set is a direct product. On a trail the constraints alternate between "exactly one of the two arcs into this reticulation" and "at least one of the two arcs out of this tree vertex", with forced arcs at fence endpoints; solving them along the trail gives the alternating words above. A W-fence has one more upper vertex than lower vertices, so the constraints are infeasible, and attaching a leaf to one of its tails repairs exactly one W-fence, which yields $\delta(N)$. Uniqueness of the decomposition holds because "sharing a head or a tail" generates an equivalence relation on arcs whose classes are the maximal trails.

## Sources

- Momoko Hayamizu, "A structure theorem for rooted binary phylogenetic networks and its implications for tree-based networks", arXiv:1811.05849 (2018), Theorem 4.2, Corollary 4.6, Theorem 4.8, Proposition 5.1, Corollaries 5.4, 5.7 and 5.11, <https://doi.org/10.48550/arXiv.1811.05849>. Published version: SIAM Journal on Discrete Mathematics 35 (2021) 2490–2516, <https://doi.org/10.1137/19m1297403>.
