# Combinatorial consistency of quarnet puzzling for triangle-free level-1 networks

A **semi-directed network** on $X$ ($|X| \ge 4$) is obtained from a binary rooted phylogenetic network by suppressing the root and undirecting every edge except the reticulation edges. It is **level-1** if every reticulation lies on exactly one cycle, and **triangle-free** if it has no 3-cycle. Collapsing each cycle to a vertex gives its **blobtree** (tree of blobs). A **tf-quarnet** is a triangle-free level-1 semi-directed network on four leaves; up to relabelling it is either a quartet tree $ab|cd$ or a 4-cycle with a circular order of $a, b, c, d$ and one leaf below the reticulation. A set $Q$ of tf-quarnets on $X$ is **dense** if it contains exactly one tf-quarnet on every 4-subset of $X$; weights $w: Q \to [0,1]$ may be attached.

**Quarnet puzzling (Squirrel).** Given dense $Q$:

1. Let $T^*$ be the most refined tree on $X$ that induces no quartet conflicting with a quartet tree of $Q$ (Berry and Gascuel); refine it to a binary tree $T_1$ by an adapted Quartetjoining using the quartet weights.
2. For each edge of $T_1$ with split $A|B$, let $Q(A|B)$ be the tf-quarnets with two leaves on each side and $Q'(A|B)$ those that are quartet trees with split $(A \cap L(q))|(B \cap L(q))$; the **split-support** is $w(Q'(A|B))/w(Q(A|B))$. Contracting the $i-1$ least supported edges gives candidate blobtrees $T_1, \dots, T_{n-3}$.
3. In each candidate, replace every vertex of degree $s \ge 4$, whose incident edges partition $X$ into $Y_1 | \dots | Y_s$, by an $s$-cycle: order the blocks by a shortest travelling-salesman tour for a distance aggregated from the quarnets restricted to one leaf per block (neighbouring leaves of a 4-cycle, or leaves on one side of a quartet split, are at distance 1, other pairs at distance 2), and place the reticulation at the block most often below a reticulation, falling back down this ranking until the network is rootable.
4. Return the candidate network with the largest weighted fraction of input tf-quarnets that it induces.

**Theorem 1.** Let $N$ be a triangle-free semi-directed level-1 network on $X$ and let $Q$ be the set of (unweighted) tf-quarnets induced by $N$. Then Squirrel applied to $Q$, with the travelling-salesman instances solved exactly, reconstructs $N$.

## Expansion

Two ingredients carry the proof. First (supplementary Lemma A.2), if $Q$ is induced by a network, the Berry-Gascuel tree $T^*$ is exactly the blobtree of $N$. Every cut-edge split of $N$ is supported by all quarnets straddling it (split-support 1), and because $T_1$ refines $T^*$, contracting least supported edges passes through $T^*$, so the true blobtree is among the candidates. Second, at a blob vertex the leaf-to-leaf distances derived from the quarnets form a Kalmanson metric for the circular order of the true cycle, and for a Kalmanson metric that order is an optimal travelling-salesman tour, so the cycle order is recovered; the 4-cycle quarnets then locate the reticulation. Statistical consistency is not claimed: it is inherited only from a statistically consistent method for producing the input quarnets, such as an invariant-based quarnet classifier.

## Sources

- N. Holtgrefe, K. T. Huber, L. van Iersel, M. Jones, S. Martin, V. Moulton, "Squirrel: Reconstructing semi-directed phylogenetic level-1 networks from four-leaved networks or sequence alignments", Molecular Biology and Evolution 42(4):msaf067 (2025), Theorem 1, Eq. (4), Algorithms 2 and 3 and supplementary Lemma A.2, <https://doi.org/10.1093/molbev/msaf067>, PMCID PMC11979102.
