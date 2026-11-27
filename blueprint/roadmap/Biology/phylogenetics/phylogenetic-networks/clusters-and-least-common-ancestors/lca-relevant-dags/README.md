# LCA-relevant DAGs

Inferred phylogenetic networks often contain vertices that are not the least common ancestor of any set of taxa and so have no direct support in the data. A DAG is lca-relevant (resp. LCA-relevant) when every vertex is the unique (resp. a minimal) common ancestor of some taxon set. These DAGs are characterized through clusters, and the vertex-deletion operator $\ominus$ removes all unsupported vertices while preserving leaves, ancestry and least common ancestors; recognizing $k$-lca vertices for prescribed $k$ is NP-complete.

- [Characterization of lca-relevant DAGs by clusters](characterization-of-lca-relevant-dags-by-clusters.md)
- [Pruning non-lca vertices and complexity of k-lca recognition](pruning-non-lca-vertices-and-complexity-of-k-lca-recognition.md)
