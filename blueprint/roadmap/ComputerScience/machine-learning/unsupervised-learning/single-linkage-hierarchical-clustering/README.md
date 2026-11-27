# Single-linkage hierarchical clustering

Single-linkage clustering at scale $r$ puts two points in the same cluster when a chain of
points joins them with every hop of length at most $r$. For a metric space the clusters are the
connected components of the Vietoris–Rips complex at scale $r$, which is why G. Carlsson calls
clustering the statistical counterpart of $\pi_0$ (*Topology and data*, Bull. AMS 46 (2009), §1 and
§3.2). Letting $r \ge 0$ vary gives a nested family of partitions, the dendrogram. For a finite metric space it
is the same datum as the ultrametric $u^*(x, y)$, the smallest scale at which $x$ and $y$ are joined; for
general dissimilarities $u^*$ is the infimum of the joining scales.
G. Carlsson and F. Mémoli (*Characterization, stability and convergence of hierarchical clustering
methods*, JMLR 11 (2010)) show that, for finite metric spaces, $u^*$ is the maximal subdominant ultrametric, that single
linkage is functorial for distance non-increasing maps and stable under perturbation of the
metric (Lemma 15; Gromov–Hausdorff stability, Prop. 26), and that it is the only
hierarchical clustering method satisfying their three axioms (Thm. 18), in contrast with Kleinberg's impossibility theorem for flat clustering (their
Thm. 1).

- [$r$-equivalence (single-linkage clusters at scale $r$)](sl-equiv.md)
- [Single-linkage clusters are nested](sl-equiv-mono.md)
- [Chains concatenate](sl-equiv-trans-max.md)
- [Functoriality of single-linkage clustering](sl-equiv-map.md)
- [Single-linkage clusters are the connected components of the Rips graph](sl-equiv-dist-iff-reachable.md)
- [Single-linkage ultrametric](sl-dist.md)
- [The single-linkage ultrametric is below the dissimilarity](sl-dist-le.md)
- [Strong triangle inequality for the single-linkage distance](sl-dist-le-max.md)
- [Single linkage gives the maximal subdominant ultrametric](le-sl-dist.md)
- [The dendrogram is the family of closed balls of $u^*$](sl-equiv-iff-sl-dist-le.md)
- [Perturbing the dissimilarity shifts the scale](sl-equiv-of-le-add.md)
- [Stability of single linkage in the sup norm](abs-sl-dist-sub-le.md)
- [Metric on a set, as a function](is-metric-fn.md)
- [Ultrametric on a set, as a function](is-ultrametric-fn.md)
- [Single linkage outputs an ultrametric](is-ultrametric-fn-sl-dist.md)
- [Below the separation, clusters are singletons](eq-of-sl-equiv-of-lt.md)
- [Single linkage never merges below the separation](le-sl-dist-of-sep.md)
- [Candidate hierarchical clustering methods](hc-method.md)
- [Hierarchical clustering method](is-hc-method.md)
- [The two-point space](two-point-dist.md)
- [Condition (I)](cm-condition-i.md)
- [Condition (II), functoriality](cm-condition-ii.md)
- [Condition (III)](cm-condition-iii.md)
- [Single linkage satisfies the Carlsson–Mémoli axioms](sl-dist-axioms.md)
- [Characterization of single linkage (Carlsson–Mémoli)](eq-sl-dist-of-axioms.md)

## Related topics

- [Simplicial complexes from point clouds](../../../../Topology/algebraic-topology/simplicial-complexes-from-point-clouds/README.md):
  single-linkage clusters are the connected components of the Vietoris–Rips complex.
- [Persistence modules and barcodes](../../../../Topology/algebraic-topology/persistence-modules-and-barcodes/README.md):
  the zero-dimensional barcode of the Vietoris–Rips filtration records the merges of the
  dendrogram.
- [Mapper](../../../../Topology/algebraic-topology/mapper/README.md): Mapper clusters the
  preimages of a cover by single linkage.
- [Splits, compatibility, ultrametrics and UPGMA](../../../../Biology/phylogenetics/splits-compatibility-ultrametrics-and-upgma/README.md):
  ultrametrics and the average-linkage method UPGMA in phylogenetics.
- [Kruskal's algorithm](../../../graph-algorithms/spanning-trees-flows-matchings/kruskal-s-algorithm/README.md):
  adding edges in increasing order of length and merging components, as Kruskal's algorithm does,
  computes the single-linkage merges.
- [k-means clustering](../k-means-clustering/README.md): a flat, centroid-based alternative.
- [Optimal leaf ordering of dendrograms](../../../../Biology/bioinformatics/optimal-leaf-ordering-of-dendrograms/README.md):
  how to draw a dendrogram, such as the single-linkage one, with similar leaves adjacent.
