# Fast SPR and TBR neighborhood search for reconciliation-based gene tree correction

**Setting.** Trees are rooted full binary trees. A gene tree $G$ and a species tree $S$ are compared
through the **LCA mapping** $\mathcal{M}(g) = \mathrm{LCA}_S(\text{species of the leaves below } g)$.
With $d_S$ the edge distance in $S$, the three gene tree parsimony costs are

- duplication: $C_D(G, S) = \sum_{g \in I(G)} [\mathcal{M}(g) \in \mathcal{M}(\mathrm{Ch}(g))]$;
- duplication-loss: $C_{DL}(G, S) = C_D(G, S) + \sum_{g \in I(G)} C_L(g)$, where $C_L(g) = 0$ if all children
  of $g$ map to $\mathcal{M}(g)$ and otherwise $C_L(g) = \sum_{h \in \mathrm{Ch}(g)} |d_S(\mathcal{M}(g), \mathcal{M}(h)) - 1|$;
- deep coalescence: $C_{DC}(G, S) = \sum_{g \in I(G)} \sum_{h \in \mathrm{Ch}(g)} d_S(\mathcal{M}(g), \mathcal{M}(h)) - |E(S)|$.

For $\Gamma \in \{D, DL, DC\}$, the **SPR (TBR) error-correction problem** asks for a tree of minimum
$C_\Gamma(\cdot, S)$ among all trees one subtree-prune-and-regraft (tree-bisection-and-reconnection)
move away from $G$; $n$ is the number of taxa.

**Theorem.**

1. For a fixed pruned subtree $G_v$, the trees $\mathrm{SPR}_G(v)$, joined when they are one nearest
   neighbor interchange apart, form a rooted full binary tree $\mathcal{X}$ whose root regrafts $G_v$ above
   the root of $G$.
2. Along an edge of $\mathcal{X}$ only the two vertices $x, y$ touched by the interchange change their LCA
   mapping or local cost, so the cost difference is
   $\Gamma_e = \sum_{g \in \{x, y\}} \bigl(C_\Gamma(G'', S, g) - C_\Gamma(G', S, g)\bigr)$, computable in
   constant time.
3. A preorder walk of $\mathcal{X}$ therefore solves the restricted problem for one $v$ in $\Theta(n)$ time,
   and the SPR error-correction problem in $\Theta(n^2)$, a factor $n$ faster than rescoring every
   neighbor.
4. A best TBR neighbor is obtained by optimizing the rooting of the pruned subtree and its regraft
   position separately, so the TBR error-correction problem is solvable in $\Theta(n^2)$ time, a factor
   $n^2$ faster than the naive search.

## Depends on

- [Is LCAReconciliation](../../../not-yet-classified/lcareconciliation/is-lcareconciliation.md)

## Expansion

Moving the regraft point of $G_v$ one edge down the tree is a single nearest neighbor interchange.
Such a move changes the clade sets of only two internal vertices, so all other LCA images, and with
them all other local duplication, loss and lineage counts, are unchanged; the cost of every neighbor
is the cost of the root of $\mathcal{X}$ plus a sum of constant-time edge differences along a path. The
TBR decomposition works because the cost of the rerooted pruned subtree and the cost contributed at
the regraft position interact only through the LCA image of the pruned subtree, which does not
depend on its rooting. Searching these neighborhoods lets reconciliation absorb small topological
errors in estimated gene trees instead of reporting them as spurious duplications, losses or deep
coalescences.

## Sources

- R. Chaudhary, J. G. Burleigh, O. Eulenstein, "Efficient error correction algorithms for gene tree
  reconciliation based on duplication, duplication and loss, and deep coalescence", BMC Bioinformatics
  13(Suppl 10) (2012) S11, Definitions 1-11, Lemmas 1-8 and Theorems 1-4,
  <https://doi.org/10.1186/1471-2105-13-s10-s11> (PMC3382437).
