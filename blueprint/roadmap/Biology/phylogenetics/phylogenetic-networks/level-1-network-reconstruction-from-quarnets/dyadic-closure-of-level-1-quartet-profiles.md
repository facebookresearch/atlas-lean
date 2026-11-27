# Dyadic closure of level-1 quartet profiles

**Setting.** A *semi-directed level-1 network* $N$ on a leaf set $X$ ($|X| = n \ge 4$) is obtained from a binary rooted phylogenetic network whose cycles are vertex-disjoint by suppressing the root and undirecting all edges except reticulation edges. A *displayed tree* keeps one incoming reticulation edge per reticulation. The *quartet profile* of $N$ on $\{a,b,c,d\} \subseteq X$ is the set of quartet trees on $\{a,b,c,d\}$ induced by the displayed trees of $N$. For level-1 (indeed outer-labeled planar) networks it contains one or two quartets: a *trivial* profile $ab|cd$, or a pair written as the circular order $(abcd)$ when it contains $ab|cd$ and $ad|bc$. Write $\mathcal Q(N)$ for the set of all quartet profiles of $N$.

**Inference rules.** Two classical tree rules and two network rules are valid for every semi-directed level-1 network (if the left side is in $\mathcal Q(N)$ then so is the right side):

$$ab|cd + ac|de \mapsto ab|de + bc|de \quad (\mathrm{R1}), \qquad ab|cd + ab|ce \mapsto ab|de \quad (\mathrm{R2}),$$

$$(abcd) + ac|de \mapsto ab|de + bc|de \quad (\mathrm{R3}), \qquad (abcd) + bc|de \mapsto (abce) \quad (\mathrm{R4}).$$

The *dyadic closure* $\mathrm{cl}(\mathcal Q)$ of a set of quartet profiles is obtained by applying R1 to R4 exhaustively; it is extensive, monotone and idempotent.

**Representative profiles.** For each non-trivial cut-edge inducing the 2-circular order $(X_1,\dots,X_k)\,|\,(Y_1,\dots,Y_l)$, with representative leaves $x_i \in X_i$, $y_j \in Y_j$ closest to the edge, take $x_1 x_k | y_1 y_l$. For each cycle (blob) of length $k \ge 4$ with circular order $(X_1,\dots,X_k)$, $X_1$ below the reticulation, take $x_i x_{i+1}|x_{i+2}x_{i+3}$ for $2 \le i \le k-3$ and $(x_1 x_i x_{i+1} x_{i+2})$ for $2 \le i \le k-2$. These form the set $\mathcal R(N)$, and $|\mathcal R(N)| \le 2n - 7$.

**Theorem (Section 3).** If $\mathcal R(N) \subseteq \mathcal Q \subseteq \mathcal Q(N)$, then $\mathrm{cl}(\mathcal Q) = \mathcal Q(N)$.

**Corollary (Section 3).** Let $\overline N$ be the mixed graph obtained from $N$ by suppressing 2-cycles, 3-cycles and the reticulation vertices of 4-cycles. Then (a) some set of $O(n)$ quartet profiles of $N$ uniquely determines $\overline N$, and (b) some set of $O(n)$ four-leaf subnetworks (quarnets) of $N$ uniquely determines $N$.

The first statement uses that $\mathcal Q(N)$ determines $\overline N$ and that $\overline N$ is reconstructible from $\mathcal Q(N)$ in $O(n^2)$ time (Section 2).

## Expansion

R1 and R2 hold because any rule valid for every tree remains valid when all premises are trivial profiles, since then every displayed tree satisfies them. R3 and R4 are proved by splitting the displayed trees according to which quartet of $(abcd)$ they induce and applying R2 within each class. Completeness of the closure is proved first for a single cycle (sunlet) and then by induction on the number of non-trivial splits: splitting $N$ at a cut-edge into two smaller networks, the induction hypothesis gives their profiles, and three short case analyses produce every profile that straddles the edge using only R1 and R2. Linear size of $\mathcal R(N)$ follows by counting one profile per split and $2k - 7$ per $k$-cycle; sunlets maximize this. The $O(n)$ encoding does not contradict the $\Omega(n \log n)$ query lower bound for adaptive reconstruction from a quarnet oracle, since it presupposes knowing which quarnets to use.

## Sources

- M. Frohn, N. Holtgrefe, L. van Iersel, M. Jones, "Bounds on the sequence length sufficient to reconstruct binary level-1 phylogenetic networks under the CFN model", *Annals of Combinatorics* (2026), Section 2 (quartet profiles and the reconstruction proposition), Section 3 (inference rules R1 to R4, representative quartet profiles and their size bound, dyadic closure theorem and linear-encoding corollary), <https://doi.org/10.1007/s00026-026-00830-0> (preprint arXiv:2511.22736).
