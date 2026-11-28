# SNPR distance from a tree to a network via displayed trees and agreement forests

**SNPR.** Let $\mathcal{N}_n$ be the rooted binary phylogenetic networks on $n$ leaves. For an edge $e = (u, v)$ of $N \in \mathcal{N}_n$, a *subnet prune and regraft* is one of: (SNPR$^0$) if $u$ is a tree vertex other than the root, delete $e$, suppress $u$, subdivide an edge not below $v$ with a new vertex $u'$ and add $(u', v)$; (SNPR$^+$) subdivide $e$ by $v'$, subdivide an edge not below $v'$ by $u'$ and add $(u', v')$, creating a reticulation; (SNPR$^-$) if $u$ is a tree vertex and $v$ a reticulation, delete $e$ and suppress $u$ and $v$. SNPR$^0$ keeps the number of reticulations, SNPR$^\pm$ changes it by $\pm 1$, and restricted to trees with SNPR$^0$ only it is the rooted SPR operation. The SNPR distance $d_{SNPR}(N, N')$ is the length of a shortest SNPR-sequence; it is a metric on $\mathcal{N}_n$, and the space of trees embeds isometrically ($d_{SNPR} = d_{rSPR}$ on trees).

**Agreement forests.** Treat the root $\rho$ as a label. For a tree $T$ and a network $N$ with $r$ reticulations, an agreement forest is a collection $F = \{T_\rho, T_1, \dots, T_k, E_1, \dots, E_r\}$ of phylogenetic trees $T_\rho \ni \rho$, $T_1, \dots, T_k$ and single directed edges $E_j$ (disagreement edges) such that the label sets of the trees partition the leaves plus $\rho$, the trees embed edge-disjointly into $T$ covering all its edges, and the trees together with the $E_j$ embed edge-disjointly into $N$ covering all its edges. With $k$ minimal, $m(T, N) = k + r = |F| - 1$.

**Theorem.** Let $T$ be a phylogenetic tree and $N$ a network with $r$ reticulations on the same $n$ leaves, and let $D(N)$ be the set of trees displayed by $N$.

1. $d_{SNPR}(T, N) = \min_{T' \in D(N)} d_{SNPR}(T, T') + r$.
2. $d_{SNPR}(T, N) = m(T, N)$, extending the Bordewich–Semple theorem $d_{rSPR}(T, T') = m(T, T')$ for two trees.
3. Computing $d_{SNPR}(T, N)$ is fixed-parameter tractable in $d_{SNPR}(T, N)$.

**Non-isometric subclasses.** For $n \ge 4$, none of the classes of tree-child, reticulation-visible, or tree-based networks embeds isometrically into $\mathcal{N}_n$ under SNPR: some pairs in the class are strictly farther apart when SNPR-sequences must stay inside the class (also for tree-based networks without parallel edges). For $n \ge 4$ and $r \ge 1$ the class of networks with exactly $r$ reticulations does not embed isometrically into $\mathcal{N}_n$, and for $n \ge 2$ and $r \ge 3$ it does not embed isometrically into the networks with at most $r$ reticulations.

## Depends on

- [rSPR distance](../../../../not-yet-classified/rooted-spragreement-forest/rspr-dist.md)

## Proof depends on

- [rSPR distance equals the maximum agreement forest number](../../../../not-yet-classified/rooted-spragreement-forest/rspr-dist-eq-rooted-maf-number.md)

## Expansion

The upper bound in item 1 is the triangle inequality through the best displayed tree $T'$, since a network is at SNPR distance $r$ from each tree it displays. For the lower bound, follow a shortest sequence $T = N_0, \dots, N_k = N$ and track displayed trees: an SNPR$^+$ step only enlarges the set of displayed trees, and after any step every displayed tree of $N_{i-1}$ is within one SNPR of a displayed tree of $N_i$. This produces a sequence of trees from $T$ to some $T' \in D(N)$ that moves at most at the $k - r$ steps that are not forced SNPR$^+$ moves, so $d_{SNPR}(T, T') \le k - r$. Item 2 follows by combining item 1 with the tree case: a maximum agreement forest for $T$ and the best displayed tree $T'$, together with the $r$ edges deleted to obtain $T'$ from $N$, is an agreement forest for $T$ and $N$, and conversely. Item 3 follows from item 1 because $r \le d_{SNPR}(T, N)$, so $|D(N)| \le 2^r$ is bounded by a function of the parameter and each $d_{rSPR}(T, T')$ is FPT.

## Sources

- J. Klawitter, S. Linz, "On the Subnet Prune and Regraft Distance", arXiv:1805.07839 (2018): Section 2 (SNPR$^0$, SNPR$^\pm$, SNPR-distance and isometric embeddings), Section 3 (distance between a tree and a network via displayed trees, FPT theorem), Section 4 (agreement forests for a tree and a network, the Bordewich–Semple theorem and its network extension), Section 5 (properties of shortest SNPR-sequences; non-isometric embedding of reticulation tiers and of tree-child, reticulation-visible and tree-based classes). <https://doi.org/10.48550/arXiv.1805.07839> Published version: The Electronic Journal of Combinatorics 26(2) (2019), #P2.3.
