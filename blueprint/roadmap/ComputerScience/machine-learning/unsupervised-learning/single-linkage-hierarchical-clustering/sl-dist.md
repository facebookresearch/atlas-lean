# Single-linkage ultrametric

For a dissimilarity $d : X \times X \to \mathbb{R}$ on a set $X$, the single-linkage distance
$u^*(x, y)$ is the infimum of the scales $r \ge 0$ at which $x$ and $y$ are
[$r$-equivalent](sl-equiv.md), that is, the infimum over chains $x = x_0, \dots, x_k = y$ of the
largest hop, floored at $0$ (the one-hop chain shows that the set of such scales is nonempty). On
a finite set the infimum is attained, and when $d$ is a metric on a finite set this is the ultrametric $u^*$
of Carlsson and Mémoli
(JMLR 11 (2010), Example 7, equation (4)), the maximal sub-dominant ultrametric, which encodes
the single-linkage dendrogram (Lemma 12 and Cor. 14 there).

## Background

- [Ultrametric on taxa](../../../../Biology/phylogenetics/splits-compatibility-ultrametrics-and-upgma/is-ultrametric.md):
  the three-point condition that $u^*$ satisfies; Carlsson and Mémoli represent every dendrogram
  by such an ultrametric (their Thm. 9), as phylogenetics represents dated trees.
